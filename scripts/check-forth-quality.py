#!/usr/bin/env python3
"""Enforce the Forth review and quality rules (owner, 2026-11-12). Part of `make test`.

Usage: python3 scripts/check-forth-quality.py [--update-baseline] [--strict | --warn]

1. Review coverage. Every commit since START that changes Forth source (src/**/*.fs) must lie in a range
   `BASE..HEAD` listed in docs/development/forth-reviews/LOG.md, i.e. an independent Forth reviewer
   (docs/development/FORTH_REVIEWER.md) has read it and its report is saved beside the log. Strict (a failure) on
   branch main, where merges are tested before a push; a warning on other branches, where agents work before review.
   --strict / --warn override that.
2. Quality ratchet. For every file under src/, the counts below may not grow beyond
   tests/forth-quality-baseline.json: words longer than 5 lines, deep stack shuffles (ROT -ROT PICK ROLL 2SWAP 2OVER
   2ROT), return-stack operations, globals, and lines over 90 characters (scripts/forth-metrics.py's definitions).
   A new file starts from zero long words and long lines, at most 0.15 shuffles and 0.5 return-stack operations per
   word (below the project average of 2026-11-12), and its globals listed in the baseline only by an update.
   --update-baseline rewrites the baseline from the tree; do it only in a commit whose Forth review accepts the
   growth, and say so in the review's log row.
"""
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
metrics = __import__("forth-metrics")

LOG = ROOT / "docs/development/forth-reviews/LOG.md"
BASELINE = ROOT / "tests/forth-quality-baseline.json"
START = "3ac0558"     # main when the rule was introduced; earlier commits are the backlog (plan 9.4.5)
RANGE = re.compile(r"`([0-9a-f]{7,40})\.\.([0-9a-f]{7,40})`")


def git(*args):
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True, check=True).stdout


def reviewed():
    covered = set()
    for base, head in RANGE.findall(LOG.read_text(encoding="utf-8")):
        covered.update(git("rev-list", f"{base}..{head}").split())
    return covered


def unreviewed():
    covered = reviewed()
    commits = git("rev-list", "--no-merges", f"{START}..HEAD").split()
    return [c for c in commits if c not in covered
            and any(p.startswith("src/") and p.endswith(".fs")
                    for p in git("diff-tree", "--no-commit-id", "--name-only", "-r", c).split())]


def counts():
    files = sorted((ROOT / "src").rglob("*.fs"))
    defining, naming = metrics.definers(files), metrics.namers(files)
    table = {}
    for path in files:
        defs, stats = metrics.analyse(path, defining, naming)
        table[str(path.relative_to(ROOT))] = {
            "words": len(defs),
            "long words": sum(d["lines"] > 5 for d in defs),
            "shuffles": sum(d["shuffles"] for d in defs),
            "rstack": sum(d["rstack"] for d in defs),
            "globals": stats["globals"],
            "long lines": stats["long lines"],
        }
    return table


def allowance(name, base, now):
    if base is not None:
        return {k: base.get(k, 0) for k in now}
    words = now["words"]
    return {"words": words, "long words": 0, "shuffles": int(0.15 * words),
            "rstack": int(0.5 * words), "globals": 0, "long lines": 0}


def ratchet():
    base = json.loads(BASELINE.read_text()) if BASELINE.exists() else {}
    problems = []
    for name, now in counts().items():
        limit = allowance(name, base.get(name), now)
        for key, value in now.items():
            if key != "words" and value > limit[key]:
                problems.append(f"{name}: {key} {value} > {limit[key]}")
    return problems


def main(argv):
    if "--update-baseline" in argv:
        BASELINE.write_text(json.dumps(counts(), indent=1, sort_keys=True) + "\n")
        print(f"wrote {BASELINE.relative_to(ROOT)}")
        return 0
    branch = git("rev-parse", "--abbrev-ref", "HEAD").strip()
    strict = "--strict" in argv or (branch == "main" and "--warn" not in argv)
    failed = False
    missing = unreviewed()
    if missing:
        label = "error" if strict else "warning"
        print(f"forth review {label}: {len(missing)} commit(s) change Forth source without a logged Forth review "
              f"(docs/development/forth-reviews/LOG.md):")
        for c in missing:
            print("  " + git("log", "-1", "--format=%h %s", c).strip())
        failed = strict
    problems = ratchet()
    if problems:
        print("forth quality ratchet: counts grew beyond tests/forth-quality-baseline.json "
              "(refactor, or update the baseline in a reviewed commit):")
        for p in problems:
            print("  " + p)
        failed = True
    if not failed:
        print(f"forth quality: ratchet holds; review log covers Forth changes since {START}"
              + ("" if not missing else " except the warned commits"))
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

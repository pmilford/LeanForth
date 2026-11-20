#!/usr/bin/env python3
"""The tactic registry (tactic plug-in design 3.1-3.5 and 4; slice a2-ii).

1. tests/front/tactic-registry.fs after src/load/front.fs dumps every authoring
   error code (the catalogue and the codes tactic files add with lfa-code:),
   every reserved word with whether LF-WORDS holds it, and every tactic
   kind's row; the lines must equal tests/front/tactic-registry.golden
   (--write writes it after a review): moving a tactic changes no line, a
   new tactic only adds its own.
2. src/front/tactics/all.fs requires every tactic file of its folder once,
   sorted, and nothing else.
3. The load refuses a code registered twice and a code 0 (lfa-code:), and a
   word reserved already, a tactic's or any other, and a word not spelt
   by-... (lf-tactic:).
A harness self-test first checks that a changed line and an unsorted list
are told apart.

Usage: GFORTH=... python3 tests/front/check_registry.py [--write]
"""
import os
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
GFORTH = os.environ.get("GFORTH", "gforth")
GOLDEN = ROOT / "tests/front/tactic-registry.golden"
ALL = ROOT / "src/front/tactics/all.fs"
REQUIRE = re.compile(r"^require \./(\S+\.fs)$")


class Failure(Exception):
    pass


def forth(*words):
    return subprocess.run([GFORTH, "src/load/front.fs", *words], cwd=ROOT, stdin=subprocess.DEVNULL,
                          capture_output=True, text=True, timeout=300)


def dump():
    done = forth("tests/front/tactic-registry.fs", "-e", "registry-dump bye")
    if done.returncode != 0 or done.stderr:
        raise Failure(f"tactic-registry.fs: exit {done.returncode}\n{done.stdout}{done.stderr}")
    return done.stdout.splitlines()


def listed(text):
    """The files all.fs requires, in order, or None when a line is no require."""
    names = []
    for line in text.splitlines():
        if not line.strip() or line.startswith("\\"):
            continue
        match = REQUIRE.match(line)
        if not match:
            return None
        names.append(match.group(1))
    return names


def all_ok(names, files):
    return names is not None and names == sorted(set(names)) and set(names) == set(files)


def self_test(want):
    if not want or [line.replace("380", "381") for line in want] == want:
        raise Failure("harness self-test: a changed line is not told apart")
    if all_ok(["b.fs", "a.fs"], ["a.fs", "b.fs"]) or all_ok(["a.fs", "a.fs"], ["a.fs"]) \
            or all_ok(["a.fs"], ["a.fs", "b.fs"]) or not all_ok(["a.fs", "b.fs"], ["b.fs", "a.fs"]):
        raise Failure("harness self-test: all.fs's order, repeats or completeness not checked")


def check_all():
    files = [p.name for p in (ROOT / "src/front/tactics").glob("*.fs") if p.name != "all.fs"]
    if not all_ok(listed(ALL.read_text(encoding="utf-8")), files):
        raise Failure(f"{ALL.relative_to(ROOT)}: not one sorted require per tactic file {files}")
    return len(files)


REFUSALS = [
    ("380 outcome-invalid s\" again\" lfa-code: twice", "lfa-code: a code 0 or below"),
    ("0 outcome-invalid s\" zero\" lfa-code: none", "lfa-code: a code 0 or below"),
    ("tac-shape-plain lf-tactic: by-apply drop", "a word reserved already"),
    ("tac-shape-plain lf-tactic: by-rfl drop", "a word reserved already"),
    ("tac-shape-plain lf-tactic: Nat drop", "a tactic word is spelt by-"),
    ("tac-shape-plain lf-tactic: by- drop", "a tactic word is spelt by-"),
]


def check_refusals():
    for line, text in REFUSALS:
        done = forth("-e", f"{line} bye")
        if done.returncode == 0 or text not in done.stdout + done.stderr:
            raise Failure(f"load accepted {line!r}: exit {done.returncode}\n{done.stderr}")


def main():
    lines = dump()
    if "--write" in sys.argv:
        GOLDEN.write_text("\n".join(lines) + "\n", encoding="utf-8")
    want = GOLDEN.read_text(encoding="utf-8").splitlines()
    self_test(want)
    if lines != want:
        raise Failure("the registry dump differs from tests/front/tactic-registry.golden "
                      "(--write after a review)")
    files = check_all()
    check_refusals()
    print(f"check_registry: {len(lines)} lines as golden; all.fs requires the {files} tactic "
          f"files, sorted; {len(REFUSALS)} registrations refused; harness self-test passed")


if __name__ == "__main__":
    try:
        main()
    except (Failure, subprocess.TimeoutExpired) as exc:
        print(f"check_registry: {exc}", file=sys.stderr)
        sys.exit(1)

#!/usr/bin/env python3
"""The Make targets that use a changed file: make test-changed, check-changed.

Usage (from the repository root):
  python3 scripts/changed-tests.py [--base REF] [--why] [--files FILE...] test|check

Prints, on one line, every leaf target of `make test` (or `make check`) that
uses a file that differs from the merge base of REF (default main) and the
working tree, new untracked files included; with --why, also each target's
changed files on stderr. A target uses the files its recipe names (as
`make -n` expands it, globs included), and, transitively, the files those
name: repository paths (src/, tests/, scripts/, docs/) anywhere in their
text, a Forth file's require and include, a Python file's imports of a
module beside it or in scripts/. Two rules cover what that misses: a
changed Forth source selects check-portable-forth and smoke, a changed
Markdown file check-docs. A changed Makefile selects every target.

This is a heuristic for an agent's inner loop, not a proof that the other
targets are unaffected: run `make test` before every commit and `make check`
at the end. Needs git, make and Python 3.
"""
import argparse
import glob
import os
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

PATH = re.compile(r"(?<![\w./-])(?:\./)?((?:src|tests|scripts|docs)/[\w.*/+-]*[\w*])")
FORTH_LOAD = re.compile(r"\b(?:require|include|needs)\s+(\S+\.fs)\b", re.IGNORECASE)
PY_IMPORT = re.compile(r"^\s*(?:from\s+(\w+)\s+import|import\s+(\w+))", re.MULTILINE)
AGGREGATES = {"test": ["test"], "check": ["test", "test-differential", "check"]}
TEXT_LIMIT = 2 * 1024 * 1024
CODE = (".fs", ".py", ".sh", ".lean", ".toml")


def git(*args):
    return subprocess.run(["git", *args], capture_output=True, text=True, check=True).stdout


def changed_files(base):
    merge_base = git("merge-base", base, "HEAD").strip()
    names = git("diff", "--name-only", merge_base).splitlines()
    names += git("ls-files", "--others", "--exclude-standard").splitlines()
    return sorted(set(names))


def leaf_targets(aggregate):
    database = subprocess.run(["make", "-pn", aggregate], capture_output=True, text=True).stdout
    prerequisites = {}
    for line in database.splitlines():
        match = re.match(r"^([\w-]+):(?!=)(.*)$", line)
        if match and match.group(1) not in prerequisites:
            prerequisites[match.group(1)] = match.group(2).split()
    targets = []
    for name in AGGREGATES[aggregate]:
        targets += [t for t in prerequisites.get(name, []) if t not in AGGREGATES["check"]]
    return list(dict.fromkeys(targets))


def recipe(target):
    return subprocess.run(["make", "-n", "--no-print-directory", "-j1", target],
                          capture_output=True, text=True).stdout


def named_files(text):
    """Repository files a text names: paths, with globs and folders expanded."""
    found = set()
    for token in PATH.findall(text):
        for path in (glob.glob(token) if "*" in token else [token]):
            if os.path.isfile(path):
                found.add(os.path.normpath(path))
            elif os.path.isdir(path):
                found.update(os.path.normpath(os.path.join(root, name))
                             for root, _, names in os.walk(path) for name in names)
    return found


def used_files(path, text):
    """The files one file uses: named paths, Forth loads, Python imports."""
    found = named_files(text)
    folder = os.path.dirname(path)
    if path.endswith(".fs"):
        for name in FORTH_LOAD.findall(text):
            for base in (folder, "."):
                candidate = os.path.normpath(os.path.join(base, name))
                if os.path.isfile(candidate):
                    found.add(candidate)
    if path.endswith(".py"):
        for first, second in PY_IMPORT.findall(text):
            for base in (folder, "scripts"):
                candidate = os.path.normpath(os.path.join(base, (first or second) + ".py"))
                if os.path.isfile(candidate):
                    found.add(candidate)
    return found


def closure(start, cache):
    seen, todo = set(), list(start)
    while todo:
        path = todo.pop()
        if path in seen:
            continue
        seen.add(path)
        if path not in cache and not path.endswith(CODE):
            cache[path] = set()  # documents and data name files but do not run them
        if path not in cache:
            try:
                with open(path, encoding="utf-8", errors="replace") as stream:
                    text = stream.read(TEXT_LIMIT)
            except OSError:
                text = ""
            cache[path] = used_files(path, text)
        todo += cache[path] - seen
    return seen


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--base", default="main")
    parser.add_argument("--why", action="store_true")
    parser.add_argument("--files", nargs="+", help="these files instead of git's changes")
    parser.add_argument("aggregate", choices=sorted(AGGREGATES))
    args = parser.parse_args()
    changed = args.files or changed_files(args.base)
    targets = leaf_targets(args.aggregate)
    if "Makefile" in changed:
        print(" ".join(targets))
        return 0
    with ThreadPoolExecutor(max_workers=8) as pool:
        recipes = dict(zip(targets, pool.map(recipe, targets)))
    cache, chosen = {}, []
    for target in targets:
        uses = closure(named_files(recipes[target]), cache)
        hits = [name for name in changed if name in uses]
        hits += [name for name in changed if name.startswith("src/") and name.endswith(".fs")
                 and target in ("check-portable-forth", "smoke")]
        hits += [name for name in changed if name.endswith(".md") and target == "check-docs"]
        if hits:
            chosen.append(target)
            if args.why:
                print(f"{target}: {' '.join(sorted(set(hits)))}", file=sys.stderr)
    unused = [name for name in changed
              if not any(name in closure(named_files(recipes[t]), cache) for t in chosen)
              and not name.endswith(".md")]
    if args.why and unused:
        print(f"no selected target uses: {' '.join(unused)}", file=sys.stderr)
    print(" ".join(chosen))
    return 0


if __name__ == "__main__":
    sys.exit(main())

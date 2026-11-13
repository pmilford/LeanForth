#!/usr/bin/env python3
"""The Make targets that use a changed file: make test-changed, check-changed.

Usage (from the repository root):
  python3 scripts/changed-tests.py [--base REF] [--why] [--files FILE...] test|check

Prints, on one line, every leaf target of `make test` (or `make check`) that
uses a file that differs from the merge base of REF (default main) and the
working tree, new untracked files included (or the files given by --files);
with --why, also each chosen target's changed files on stderr.

A target uses the files its recipe names (as `make -n` expands it, globs
included) and, transitively, what those programs use: a Forth file's
require and include; a Python file's imports of a module beside it or in
scripts/; and the repository paths (src/, tests/, scripts/, docs/) named in
the code of Forth, Python and shell files, comments and Python docstrings
left out. Lean files, the fault list and data files are used but not
followed further. Rules cover what that misses: a changed Forth source
selects check-portable-forth and smoke, a changed Markdown file check-docs,
a changed Makefile every target.

This is a heuristic for an agent's inner loop, not a proof that the other
targets are unaffected: at the end of a branch run its change tier's suites
(make tier; scripts/test-tier.py builds the tiers on these functions). Most
tests load src/main.fs, so a change to a checker module still selects most
targets. Needs git, make and Python 3.
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
# Anchored at the start of the text (\A), comment lines matched one line at a
# time: the earlier form (DOTALL, re.sub at every position) backtracked over
# whole files and took minutes per run (2026-11-13).
DOCSTRING = re.compile(r'\A(?:#[^\n]*\n|[ \t]*\n)*(?:"""|\'\'\')[\s\S]*?(?:"""|\'\'\')')
COMMENT = {".fs": "\\", ".py": "#", ".sh": "#"}
# make check is make test plus check-rest (the Makefile, plan 9.4.6).
AGGREGATES = {"test": ["test"], "check": ["check", "test", "check-rest", "test-differential"]}
# A target-specific variable line of make's database ("target: VAR := value").
TARGET_VARIABLE = re.compile(r"^\s*[\w.-]+\s*(?:::=|:=|\?=|\+=|!=|=)")
TEXT_LIMIT = 2 * 1024 * 1024


def git(*args):
    return subprocess.run(["git", *args], capture_output=True, text=True, check=True).stdout


def changed_files(base):
    merge_base = git("merge-base", base, "HEAD").strip()
    names = git("diff", "--name-only", merge_base).splitlines()
    names += git("ls-files", "--others", "--exclude-standard").splitlines()
    return sorted(set(names))


def make_env():
    """The environment without an enclosing make's flags (its jobs, its goals)."""
    return {k: v for k, v in os.environ.items()
            if k not in ("MAKEFLAGS", "MAKELEVEL", "MFLAGS", "MAKEOVERRIDES")}


def prerequisites_of(aggregate):
    """{target: [prerequisite, ...]} from make's database, first rule line each."""
    database = subprocess.run(["make", "-pn", aggregate], capture_output=True, text=True,
                              env=make_env()).stdout
    prerequisites = {}
    for line in database.splitlines():
        match = re.match(r"^([\w-]+):(?!=)(.*)$", line)
        if match and match.group(1) not in prerequisites and not TARGET_VARIABLE.match(match.group(2)):
            prerequisites[match.group(1)] = match.group(2).replace("|", " ").split()
    return prerequisites


def leaf_targets(aggregate, prerequisites=None):
    """The prerequisites of the aggregate's targets, aggregates left out, in make's order."""
    prerequisites = prerequisites if prerequisites is not None else prerequisites_of(aggregate)
    targets = []
    for name in AGGREGATES[aggregate]:
        targets += [t for t in prerequisites.get(name, []) if t not in AGGREGATES["check"]]
    return list(dict.fromkeys(targets))


def recipe(target):
    return subprocess.run(["make", "-n", "--no-print-directory", "-j1", target],
                          capture_output=True, text=True, env=make_env()).stdout


def named_files(text):
    """Repository files a text names: paths, with globs expanded (a folder's
    name alone, as comments use it, does not select its files)."""
    found = set()
    for token in PATH.findall(text):
        for path in (glob.glob(token) if "*" in token else [token]):
            if os.path.isfile(path):
                found.add(os.path.normpath(path))
    return found


def code_of(path, text):
    """The text of a program without its comment lines and module docstring."""
    if path.endswith(".py"):
        text = DOCSTRING.sub("", text, count=1)
    mark = COMMENT[os.path.splitext(path)[1]]
    return "\n".join(line for line in text.splitlines() if not line.lstrip().startswith(mark))


def used_files(path, text):
    """The files one program uses: named paths, Forth loads, Python imports."""
    found = named_files(code_of(path, text))
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
    """Every file the start files use, following programs (not Lean or data)."""
    seen, todo = set(), list(start)
    while todo:
        path = todo.pop()
        if path in seen:
            continue
        seen.add(path)
        if os.path.splitext(path)[1] not in COMMENT:
            continue
        if path not in cache:
            try:
                with open(path, encoding="utf-8", errors="replace") as stream:
                    cache[path] = used_files(path, stream.read(TEXT_LIMIT))
            except OSError:
                cache[path] = set()
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
        if args.why:
            print("the Makefile changed: every target", file=sys.stderr)
        print(" ".join(targets))
        return 0
    with ThreadPoolExecutor(max_workers=8) as pool:
        recipes = dict(zip(targets, pool.map(recipe, targets)))
    cache, chosen, used = {}, [], set()
    for target in targets:
        uses = closure(named_files(recipes[target]), cache)
        hits = [name for name in changed if name in uses]
        hits += [name for name in changed if name.startswith("src/") and name.endswith(".fs")
                 and target in ("check-portable-forth", "smoke")]
        hits += [name for name in changed if name.endswith(".md") and target == "check-docs"]
        if hits:
            chosen.append(target)
            used.update(hits)
            if args.why:
                print(f"{target}: {' '.join(sorted(set(hits)))}", file=sys.stderr)
    unused = [name for name in changed if name not in used]
    if args.why and unused:
        print(f"no target uses: {' '.join(unused)}", file=sys.stderr)
    print(" ".join(chosen))
    return 0


if __name__ == "__main__":
    sys.exit(main())

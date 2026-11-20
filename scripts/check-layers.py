#!/usr/bin/env python3
"""Fail when a layer entry of src/load/ loads a layer above its own (make check-layers, part of
make test; src/README.md, "Layer entries").

Usage (from the repository root):
  python3 scripts/check-layers.py [--gforth GFORTH] [--root DIR]

A test loads the smallest entry that serves it, and scripts/tested-tree.py reuses a target's
recorded pass while the files it loads are unchanged: an entry that loaded a higher layer would
make every test of the lower one re-run for a change up there. Fails (exit 1, each reason on
stderr) when:
  1. an entry's closure (require, include and needs, comments too, as scripts/test-tier.py
     follows them) holds a file of a folder its layer may not use (ENTRIES); the checker
     entry may load only CHECKER_PRESENT of present/, the name text of run records;
  2. a file of src/lib loads anything outside src/lib, or a file of src/core anything but lib
     and core (src/README.md's rules); or src/main.fs loads a module that no entry and no
     file of src/cli loads (every module comes in through a layer);
  3. a test file under tests/ requires src/main.fs and is not in WHOLE_LOADS, the tests of the
     whole load itself: any other test requires the entries it needs (the command line's are
     src/load/cli-checker.fs for exports and src/load/cli.fs with a LeanForth text);
  4. with --gforth: Gforth loading an entry alone fails, writes to standard error, or loads a
     file of src/ the closure of check 1 lacks (Gforth's .included), so the closure is what
     Gforth really loads and scripts/tested-tree.py's inputs miss nothing. (make smoke loads
     each entry alone too and fails if it prints anything.)
Exit 0 when all hold, 2 on a usage error. --root runs on another tree (the tests' fixtures).
"""
import argparse
import glob
import os
import re
import subprocess
import sys

ENTRIES = {
    "src/load/kernel.fs": {"lib", "core", "kernel"},
    "src/load/import.fs": {"lib", "core", "import"},
    "src/load/checker.fs": {"lib", "core", "kernel", "import", "present"},
    "src/load/program.fs": {"lib", "program"},
    "src/load/present.fs": {"lib", "core", "present"},
    "src/load/front.fs": {"lib", "core", "present", "author", "import", "front"},
    "src/load/cli-checker.fs": {"lib", "core", "kernel", "import", "present", "cli"},
    "src/load/cli.fs": {"lib", "core", "kernel", "import", "present", "author", "front", "cli"},
}
# The import pass names its run records' declarations with the presentation's name text
# (import/run-record.fs): the only modules of present/ the checker loads.
CHECKER_PRESENT = {"src/present/binder-table.fs", "src/present/name-text.fs", "src/present/print-job.fs",
                   "src/present/print-names.fs"}
FOLDER_RULES = {"lib": {"lib"}, "core": {"lib", "core"}}
# Tests that require src/main.fs because the whole load is what they test; every other test
# requires the entries it needs (the command line's: src/load/cli-checker.fs for exports,
# src/load/cli.fs with a LeanForth text).
WHOLE_LOADS = {
    "tests/smoke/smoke.fs": "the whole load is what it tests",
    "tests/core/contexts-main.fs": "the dictionary of everything src/main.fs loads",
}
FORTH_LOAD = re.compile(r"\b(?:require|include|needs)\s+(\S+\.fs)\b", re.IGNORECASE)
MAIN_LOAD = re.compile(r"^\s*require\s+(?:\.\./)+src/main\.fs\b", re.IGNORECASE | re.MULTILINE)


def read(path):
    try:
        with open(path, encoding="utf-8", errors="replace") as stream:
            return stream.read()
    except OSError:
        return None


def loads(path):
    """The files of the tree PATH loads (beside it, or from the root, as test-tier.py resolves)."""
    found = []
    for name in FORTH_LOAD.findall(read(path) or ""):
        for base in (os.path.dirname(path), "."):
            candidate = os.path.normpath(os.path.join(base, name))
            if os.path.isfile(candidate):
                found.append(candidate)
                break
    return found


def closure(start):
    seen, todo = set(), [start]
    while todo:
        path = todo.pop()
        if path not in seen:
            seen.add(path)
            todo += loads(path)
    return seen


def folder(path):
    parts = path.split("/")
    return parts[1] if len(parts) > 2 and parts[0] == "src" else None


def entry_problems():
    problems = []
    for entry, allowed in ENTRIES.items():
        if not os.path.isfile(entry):
            problems.append(f"{entry} is missing")
            continue
        for path in sorted(closure(entry) - {entry}):
            where = folder(path)
            if where == "load":
                if path not in ENTRIES:
                    problems.append(f"{entry} loads {path}, which is no entry")
            elif where not in allowed:
                problems.append(f"{entry} loads {path}: its layer uses only {', '.join(sorted(allowed))}")
            elif entry == "src/load/checker.fs" and where == "present" and path not in CHECKER_PRESENT:
                problems.append(f"{entry} loads {path}: the checker loads of present/ only the name text "
                                "of run records (CHECKER_PRESENT)")
    return problems


def folder_problems():
    problems = []
    for name, allowed in FOLDER_RULES.items():
        for path in sorted(glob.glob(f"src/{name}/*.fs")):
            for used in loads(path):
                if folder(used) not in allowed:
                    problems.append(f"{path} loads {used}: src/{name} uses only {', '.join(sorted(allowed))}")
    if os.path.isfile("src/main.fs"):
        layered = set().union(*(closure(e) for e in ENTRIES if os.path.isfile(e)))
        for path in sorted(glob.glob("src/cli/*.fs")):
            layered |= closure(path)
        for path in sorted(closure("src/main.fs") - layered - {"src/main.fs"}):
            problems.append(f"src/main.fs loads {path} through no entry of src/load and no file of src/cli")
    return problems


def test_files():
    """Every Forth file under tests/: walked, not globbed, so that the finder (changed-tests.py)
    does not take this check for a run of every test (test-classes.py would call the hand-run
    benchmarks' rows stale). Named without their folder: a path in a docstring is followed."""
    for top, folders, names in os.walk("tests"):
        folders.sort()
        yield from (os.path.join(top, name) for name in sorted(names) if name.endswith(".fs"))


def test_problems():
    problems = []
    for path in test_files():
        if MAIN_LOAD.search(read(path) or "") and path not in WHOLE_LOADS:
            problems.append(f"{path} requires src/main.fs: require the entries of src/load it needs "
                            "(or, if it runs the command line's own words, list it in WHOLE_LOADS)")
    for path in sorted(WHOLE_LOADS):
        if not MAIN_LOAD.search(read(path) or ""):
            problems.append(f"{path} is listed in WHOLE_LOADS but is missing or does not require src/main.fs: "
                            "remove it from the list")
    return problems


def gforth_problems(gforth):
    """Each entry loaded alone by GFORTH: silent, exit 0, and no file of src/ beyond its closure."""
    problems = []
    for entry in ENTRIES:
        if not os.path.isfile(entry):
            continue
        run = subprocess.run([gforth, entry, "-e", ".included bye"], stdin=subprocess.DEVNULL,
                             capture_output=True, text=True, timeout=300)
        loaded = {os.path.normpath(line.strip()) for line in run.stdout.splitlines()
                  if line.strip().startswith("src/")}
        if run.returncode != 0 or run.stderr.strip():
            problems.append(f"{entry}: Gforth exited {run.returncode} loading it alone: "
                            f"{(run.stderr or run.stdout).strip()[-300:]}")
            continue
        if not loaded:
            problems.append(f"{entry}: Gforth's .included listed no file of src/")
        for path in sorted(loaded - closure(entry)):
            problems.append(f"{entry}: Gforth loads {path}, which its closure lacks")
    return problems


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--gforth", help="also load each entry alone with this Gforth")
    parser.add_argument("--root", default=".", help="the tree to check (default: the working folder)")
    args = parser.parse_args(argv)
    gforth = os.path.abspath(args.gforth) if args.gforth and "/" in args.gforth else args.gforth
    os.chdir(args.root)
    problems = entry_problems() + folder_problems() + test_problems()
    if gforth:
        problems += gforth_problems(gforth)
    for problem in problems:
        print(f"check-layers: {problem}", file=sys.stderr)
    if problems:
        return 1
    print(f"check-layers: {len(ENTRIES)} layer entries keep to their layers"
          + (", and Gforth loads each alone within its closure" if gforth else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())

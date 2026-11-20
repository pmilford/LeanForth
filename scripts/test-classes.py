#!/usr/bin/env python3
"""The unit and end-to-end classes of the tests (owner, 2026-11-14): tests/test-classes.txt.

Usage (from the repository root):
  python3 scripts/test-classes.py               (make check-test-classes)
  python3 scripts/test-classes.py --list CLASS  (unit, e2e, manual or daily: the names of that class)

tests/test-classes.txt is the one list of the classes (docs/development/TESTING_STRATEGY.md,
"Unit and end-to-end tests"): each row is a target of the Makefile or a test program's path, its
class (unit, e2e, manual or daily) and a note; # starts a comment line. A daily row names a test
target that make daily runs (scripts/test-tier.py's DAILY_SUITES) and make check does not. A target row may be a pattern
with * (test-tactic-*: the targets the Makefile finds from tests/front/tactics/, tactic plug-in
design, slice (a1)): a target without a row of its own takes the class of the longest pattern
that matches it, and a pattern may match no target yet. The Makefile reads it for make
test-unit and make test-e2e, scripts/test-tier.py for the suites of a change tier: unit tests run
on Gforth 1.0 (instrumented), on gforth-fast and at the push on Gforth 0.7.3, end-to-end tests
once.

Without --list it checks the table against the Makefile and the tree, and exits 1 naming every
problem: a malformed row, an unknown class, a name given twice; a leaf target of make check
(scripts/changed-tests.py's) with no row, or a target row that names no leaf target of make
check (a daily row: no target of make daily, or a leaf of make check, or a path); a tracked
test program under tests/ (.fs, .py, .sh) that no target of make check runs
(scripts/changed-tests.py's closure of the recipes: named paths, Forth loads, Python imports)
and that no row names; a path row whose file is missing or that a target already reaches (the
row is then stale); a target row classed manual. Exit status 0, 1 for problems, 2 for a usage
error.
"""
import argparse
import fnmatch
import importlib.util
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
TABLE = "tests/test-classes.txt"
CLASSES = ("unit", "e2e", "manual", "daily")
PROGRAMS = (".fs", ".py", ".sh")


def module(name, file):
    spec = importlib.util.spec_from_file_location(name, os.path.join(HERE, file))
    loaded = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(loaded)
    return loaded


def is_path(name):
    return "/" in name


def parse(text):
    """({name: class}, [problem]) of the table's TEXT, in its order."""
    rows, problems = {}, []
    for number, line in enumerate(text.splitlines(), 1):
        words = line.split()
        if not words or words[0].startswith("#"):
            continue
        if len(words) < 2 or words[1] not in CLASSES:
            problems.append(f"{TABLE}:{number}: not 'NAME CLASS [note]' with a class of {', '.join(CLASSES)}")
        elif words[0] in rows:
            problems.append(f"{TABLE}:{number}: {words[0]} is given twice")
        else:
            rows[words[0]] = words[1]
    return rows, problems


def read(path=TABLE):
    """({name: class}, [problem]) of the table in this tree; a missing table is one problem."""
    try:
        with open(path, encoding="utf-8") as stream:
            return parse(stream.read())
    except OSError:
        return {}, [f"{path}: missing: every test target needs a class"]


def is_pattern(name):
    return "*" in name


def of_class(rows, wanted):
    """The target names (not paths or patterns) of class WANTED, in the table's order."""
    return [name for name, kind in rows.items() if kind == wanted and not is_path(name) and not is_pattern(name)]


def class_of(rows, target):
    """TARGET's class: its own row's, else the longest matching pattern's, else None."""
    if target in rows:
        return rows[target]
    patterns = sorted((n for n in rows if is_pattern(n) and fnmatch.fnmatchcase(target, n)), key=len, reverse=True)
    return rows[patterns[0]] if patterns else None


class OfClass:
    """The targets of one class, as a container: `target in OfClass(rows, "e2e")`."""

    def __init__(self, rows, wanted):
        self.rows, self.wanted = rows, wanted

    def __contains__(self, target):
        return class_of(self.rows, target) == self.wanted


def daily_problems(rows, leaves, daily):
    """The problems of the daily rows of ROWS: each names a target of DAILY (make daily's goals)
    that is no leaf of make check (LEAVES), never a test program's path."""
    found = []
    for name in (n for n, k in rows.items() if k == "daily"):
        if is_path(name):
            found.append(f"row {name}: class daily names a target of make daily, never a test program")
        elif name in leaves:
            found.append(f"row {name}: a target of make check is unit or e2e, never daily")
        elif name not in daily:
            found.append(f"row {name}: class daily, but make daily runs no target of that name")
    return found


def problems_of(rows, leaves, reached, programs, daily=()):
    """The table's problems against LEAVES (make check's leaf targets), REACHED (every file their
    recipes reach), PROGRAMS (the tracked test programs under tests/) and DAILY (the targets make
    daily runs)."""
    found = daily_problems(rows, leaves, daily)
    targets = {n: k for n, k in rows.items() if not is_path(n)}
    paths = {n: k for n, k in rows.items() if is_path(n) and k != "daily"}
    found += [f"target {t}: in no class (add a row to {TABLE})" for t in leaves if class_of(targets, t) is None]
    found += [f"row {t}: no leaf target of make check has that name" for t, k in targets.items()
              if k != "daily" and t not in leaves and not is_pattern(t)]
    found += [f"row {t}: a target is unit or e2e, never manual" for t, k in targets.items() if k == "manual"]
    for path in programs:
        if path not in reached and path not in paths:
            found.append(f"test file {path}: in neither class: no target of make check runs it and no "
                         f"row of {TABLE} names it")
    for path in paths:
        if path not in programs:
            found.append(f"row {path}: no such tracked test program")
        elif path in reached:
            found.append(f"row {path}: a target already runs it; its class is that target's (stale row)")
    return found


def tracked_programs():
    listed = subprocess.run(["git", "ls-files", "tests"], capture_output=True, text=True, check=True).stdout
    return sorted(p for p in listed.splitlines() if os.path.splitext(p)[1] in PROGRAMS)


def check():
    """Every problem of this tree's table, Makefile and tests."""
    rows, found = read()
    test_tier = module("test_tier", "test-tier.py")
    reach = test_tier.Reach(test_tier.make_database()[0])
    reached = set().union(*reach.uses.values()) if reach.uses else set()
    daily = {goal for suite in test_tier.DAILY_SUITES for goal in suite["goals"]}
    return found + problems_of(rows, reach.every, reached, tracked_programs(), daily)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--list", choices=CLASSES)
    args = parser.parse_args(argv)
    if args.list:
        rows, found = read()
        print(" ".join(n for n, k in rows.items() if k == args.list))
        return 1 if found else 0
    found = check()
    for problem in found:
        print(f"test-classes: {problem}", file=sys.stderr)
    if not found:
        rows = read()[0]
        print(f"test-classes: {len(of_class(rows, 'unit'))} unit and {len(of_class(rows, 'e2e'))} end-to-end "
              f"targets ({len(of_class(rows, 'daily'))} daily, run by make daily alone); every test program "
              f"in a class")
    return 1 if found else 0


if __name__ == "__main__":
    sys.exit(main())

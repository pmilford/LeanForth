#!/usr/bin/env python3
"""Block coverage of the Forth source (plan task 1.4.1): make coverage.

Usage (from the repository root):
  python3 scripts/coverage.py [--gforth GFORTH] [--files] [--uncovered FILE]
                              [--keep DIR] [-- COMMAND ...]

Runs COMMAND (default: make test) with GFORTH set to
scripts/coverage-gforth.sh, so that every Gforth run of the command, the
Python tests' too, loads Gforth 1.0's coverage.fs first and leaves its
block counts (scripts/coverage-prelude.fs). Then it joins the counts of
all runs and prints, for each folder of src/, the basic blocks compiled
in any run and how many of them ran at least once. make test's smoke
check loads every module of src/ on its own, so every block counts, also
those of modules no test runs.

A block is Gforth's: the code from one counter to the next, a counter
being placed at each colon definition's start, at each control-flow word
and at the start of each source line inside a definition. A block that ran
is not a tested block: the measure finds code no test reaches, and says
nothing about whether the tests check what that code does (make mutants
asks that). Runs that end with an uncaught THROW (such as the harness's
deliberate failures) leave no counts.

--files also prints every file; --uncovered writes each block that never
ran, as file:line:column; --keep keeps the raw counts in DIR. The command
must pass: a failure is reported and the exit status is 1. Needs Gforth
1.0 (Gforth 0.7.3 has no coverage.fs) and the files under scripts/.
"""
import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
WRAPPER = ROOT / "scripts/coverage-gforth.sh"
PRELUDE = ROOT / "scripts/coverage-prelude.fs"
COUNT = re.compile(r"^(.+):(\d+):(\d+): (\d+)\s*$")
MAKE_VARIABLES = ("MAKEFLAGS", "MAKELEVEL", "MFLAGS", "MAKEOVERRIDES")


def resolve(gforth):
    if "/" in gforth:
        return str((Path.cwd() / gforth).resolve())
    found = shutil.which(gforth)
    return found or gforth


def has_coverage(gforth):
    """Whether this Gforth loads the prelude (it needs coverage.fs)."""
    env = {k: v for k, v in os.environ.items() if k != "LF_COVERAGE_OUT"}
    try:
        result = subprocess.run([gforth, str(PRELUDE), "-e", "bye"], env=env,
                                stdin=subprocess.DEVNULL, capture_output=True, timeout=60)
    except (OSError, subprocess.TimeoutExpired):
        return False
    return result.returncode == 0 and not result.stdout and not result.stderr


def run_command(command, gforth, directory):
    env = {k: v for k, v in os.environ.items() if k not in MAKE_VARIABLES}
    env.update(GFORTH=str(WRAPPER), LF_COVERAGE_GFORTH=gforth,
               LF_COVERAGE_DIR=str(directory))
    return subprocess.run(command, cwd=ROOT, env=env, stdin=subprocess.DEVNULL).returncode


def source_key(name, cwd):
    """The path of a counted file relative to the root, or None outside src/."""
    path = Path(name)
    if not path.is_absolute():
        path = Path(cwd) / path
    try:
        relative = Path(os.path.normpath(path)).relative_to(ROOT)
    except ValueError:
        return None
    return str(relative) if relative.parts[0] == "src" else None


def read_runs(directory):
    """({(file, line, column): count} over src/, runs with counts, runs without)."""
    blocks, counted, empty = {}, 0, 0
    for out in sorted(directory.glob("run.*")):
        if out.name.endswith(".cwd"):
            continue
        lines = out.read_text(encoding="utf-8", errors="replace").splitlines()
        if not lines:
            empty += 1
            continue
        counted += 1
        cwd = Path(str(out) + ".cwd").read_text(encoding="utf-8").splitlines()[0]
        for line in lines:
            match = COUNT.match(line)
            key = match and source_key(match[1], cwd)
            if key:
                block = (key, int(match[2]), int(match[3]))
                blocks[block] = blocks.get(block, 0) + int(match[4])
    return blocks, counted, empty


def totals(blocks, group):
    """{group name: [blocks, executed]} with group ( file -- name )."""
    table = {}
    for (name, _, _), count in blocks.items():
        entry = table.setdefault(group(name), [0, 0])
        entry[0] += 1
        entry[1] += count > 0
    return table


def print_table(title, table):
    print(f"{title:<40} {'blocks':>7} {'ran':>7} {'coverage':>9}")
    total = [0, 0]
    for name in sorted(table):
        size, ran = table[name]
        total[0] += size
        total[1] += ran
        print(f"{name:<40} {size:>7} {ran:>7} {100 * ran / size:>8.1f}%")
    print(f"{'total':<40} {total[0]:>7} {total[1]:>7} {100 * total[1] / total[0]:>8.1f}%")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--gforth", default=os.environ.get("GFORTH", "gforth"))
    parser.add_argument("--files", action="store_true")
    parser.add_argument("--uncovered")
    parser.add_argument("--keep")
    parser.add_argument("command", nargs="*")
    args = parser.parse_args(argv)
    command = args.command or ["make", "test"]
    gforth = resolve(args.gforth)
    if not has_coverage(gforth):
        print(f"make coverage needs Gforth 1.0's coverage.fs; {gforth} cannot load "
              f"{PRELUDE.relative_to(ROOT)}")
        return 2
    directory = Path(args.keep) if args.keep else Path(tempfile.mkdtemp(prefix="leanforth-cov-"))
    directory.mkdir(parents=True, exist_ok=True)
    try:
        status = run_command(command, gforth, directory)
        blocks, counted, empty = read_runs(directory)
    finally:
        if not args.keep:
            shutil.rmtree(directory, ignore_errors=True)
    print(f"\nBlock coverage of src/ over: {' '.join(command)} "
          f"({counted} Gforth runs with counts, {empty} without)")
    if not blocks:
        print("no counts were collected")
        return 1
    print_table("folder", totals(blocks, lambda name: str(Path(name).parent)))
    if args.files:
        print()
        print_table("file", totals(blocks, lambda name: name))
    if args.uncovered:
        with open(args.uncovered, "w", encoding="utf-8") as handle:
            for (name, line, column), count in sorted(blocks.items()):
                if count == 0:
                    handle.write(f"{name}:{line}:{column}\n")
    if status != 0:
        print(f"FAILED: {' '.join(command)} exited with status {status} under coverage")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())

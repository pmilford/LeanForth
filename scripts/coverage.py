#!/usr/bin/env python3
"""Block coverage of the Forth source (plan task 1.4.1): make coverage.

Usage (from the repository root):
  python3 scripts/coverage.py [--gforth GFORTH] [--files] [--uncovered FILE]
                              [--keep DIR] [--check | --update-baseline
                              [--reason TEXT]] [-- COMMAND ...]

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

Every Gforth run goes through the counting wrapper: the Makefile keeps a GFORTH
that names scripts/coverage-gforth.sh, bin/leanforth's --fast finds
scripts/gforth-fast beside it, which hands over to the wrapper, and Python
tests that start $GFORTH use it. The measurement fails (exit 1) when no run left
counts, when more than 10% of the runs left none, or when fewer runs left counts
than 90% of tests/coverage-baseline.json's "runs": the tool must never again stop
counting silently, as it did unnoticed until 2026-11-12.

--check compares each file's never-run blocks with tests/coverage-baseline.json
(the ratchet, make coverage-check) and fails when a file's grow or a file the
baseline lacks has any never-run block. --update-baseline rewrites the baseline
from this measurement; a new file with never-run blocks needs --reason TEXT, kept
in the baseline, and the other files keep their reasons.

--files also prints every file; --uncovered writes each block that never
ran, as file:line:column; --keep keeps the raw counts in DIR. The command
must pass: a failure is reported and the exit status is 1. Needs Gforth
1.0 (Gforth 0.7.3 has no coverage.fs) and the files under scripts/.
"""
import argparse
import json
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
COUNT_HEAD = re.compile(r"^(.+):(\d+):(\d+)$")
BASELINE = ROOT / "tests/coverage-baseline.json"
SHORTFALL = 0.9   # fewer runs with counts than this share of the baseline's fails
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
    """({(file, line, column): count} over src/, runs with counts, runs without).

    A run's file has one line per block compiled, src/ or not (about 40,000), and
    a make test has over a thousand runs: the lines are first summed per working
    directory by their text, and only the distinct ones are parsed."""
    sums, counted, empty = {}, 0, 0
    for out in sorted(directory.glob("run.*")):
        if out.name.endswith(".cwd"):
            continue
        cwd = Path(str(out) + ".cwd").read_text(encoding="utf-8", errors="replace").splitlines()[0]
        table, seen = sums.setdefault(cwd, {}), False
        with open(out, encoding="utf-8", errors="replace") as handle:
            for line in handle:
                seen = True
                head, sep, count = line.rpartition(": ")
                if sep:
                    table[head] = table.get(head, 0) + int(count)
        counted, empty = counted + seen, empty + (not seen)
    blocks = {}
    for cwd, table in sums.items():
        for head, count in table.items():
            match = COUNT_HEAD.match(head)
            key = match and source_key(match[1], cwd)
            if key:
                block = (key, int(match[2]), int(match[3]))
                blocks[block] = blocks.get(block, 0) + count
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


def per_file(blocks):
    """{file: [blocks, never run]}."""
    return {name: [size, size - ran] for name, (size, ran) in totals(blocks, str).items()}


def run_problems(counted, empty, baseline):
    """Reasons why the measurement itself cannot be trusted (empty when it can)."""
    problems = []
    if counted == 0:
        problems.append("no Gforth run left counts")
    if empty > 0.1 * (counted + empty):
        problems.append(f"{empty} of {counted + empty} Gforth runs left no counts")
    expected = baseline.get("runs", 0) if baseline else 0
    if expected and counted < SHORTFALL * expected:
        problems.append(f"only {counted} Gforth runs left counts; the baseline "
                        f"({BASELINE.name}) has {expected}")
    return problems


def load_baseline():
    return json.loads(BASELINE.read_text(encoding="utf-8")) if BASELINE.exists() else None


def ratchet(files, baseline):
    """Messages for each file whose never-run blocks grew, or that is new with some."""
    known = baseline["files"] if baseline else {}
    messages = []
    for name, (size, never) in sorted(files.items()):
        entry = known.get(name)
        if entry is None and never:
            messages.append(f"{name}: new file with {never} of {size} blocks never run "
                            f"and no reason listed in the baseline")
        elif entry is not None and never > entry["never_run"]:
            messages.append(f"{name}: {never} blocks never run, the baseline allows "
                            f"{entry['never_run']}")
    return messages


def new_baseline(files, counted, old, reason):
    """The baseline for this measurement; a new file with never-run blocks needs REASON."""
    known = old["files"] if old else {}
    out = {}
    for name, (size, never) in sorted(files.items()):
        entry = {"blocks": size, "never_run": never}
        why = known.get(name, {}).get("reason") or (reason if never else None)
        if never and not why:
            raise SystemExit(f"{name} is new with {never} never-run blocks: "
                             f"--update-baseline needs --reason TEXT")
        if why:
            entry["reason"] = why
        out[name] = entry
    return {"runs": counted, "files": out}


def main(argv=None):
    global BASELINE
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--gforth", default=os.environ.get("GFORTH", "gforth"))
    parser.add_argument("--files", action="store_true")
    parser.add_argument("--uncovered")
    parser.add_argument("--keep")
    parser.add_argument("--baseline", default=str(BASELINE))
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--update-baseline", action="store_true")
    parser.add_argument("--reason", default="")
    parser.add_argument("command", nargs="*")
    args = parser.parse_args(argv)
    BASELINE = Path(args.baseline)
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
    baseline = load_baseline()
    problems = run_problems(counted, empty, None if args.update_baseline else baseline)
    if not blocks:
        print("FAILED: no counts were collected; " + "; ".join(problems))
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
    if problems:
        print("FAILED: " + "; ".join(problems))
        return 1
    files = per_file(blocks)
    if args.update_baseline:
        text = json.dumps(new_baseline(files, counted, baseline, args.reason), indent=1)
        BASELINE.write_text(text + "\n", encoding="utf-8")
        print(f"wrote {BASELINE}")
    elif args.check:
        messages = ratchet(files, baseline) if baseline else [f"no {BASELINE.name}"]
        for message in messages:
            print("FAILED: " + message)
        if messages:
            return 1
        print("coverage ratchet: no file has more never-run blocks than the baseline")
    return 0


if __name__ == "__main__":
    sys.exit(main())

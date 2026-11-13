#!/usr/bin/env python3
"""Tactic proofs read, end to end (plan FE1g-2; src/front/tactic-syntax.fs,
docs/design/FE1G_TACTICS.md section 3).

1. The record of each FE1 file (FILES below), printed by
   tests/front/tactic-dump.fs in its format 1, with the error the run ends
   with, equals tests/front/tactics.golden line for line. A harness
   self-test first checks that a changed record is told apart.
2. `bin/leanforth check --env tests/front/tactic-slice.ndjson FILE` on
   each file exits 2 with error 80 at its end NAME (not supported yet:
   running tactics, plan FE1g-3), and on malformed twins written here
   exits 4 with the twin's error code; nothing is checked, nothing
   accepted.
With --lean instead: pinned Lean, through scripts/export.sh, reproduces
the export these tests run against (tests/front/tactic-slice.ndjson:
Nat.add_succ, Nat.zero_add and congrArg from Init, with what they use)
and its manifest, byte for byte.

Usage: GFORTH=... python3 tests/front/check_tactics.py
       LEAN=... python3 tests/front/check_tactics.py --lean
"""
import os
import pathlib
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
GFORTH = os.environ.get("GFORTH", "gforth")
LEAN = os.environ.get("LEAN", ".tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean")
SLICE_NAMES = ["Nat.add_succ", "Nat.zero_add", "congrArg"]
GOLDEN = ROOT / "tests/front/tactics.golden"
SLICE = "tests/front/tactic-slice.ndjson"
LIMIT = 300
FILES = ["tests/front/01-zero-add-rw.lf", "tests/front/01-zero-add.lf",
         "tests/front/02-add-zero-rfl.lf", "tests/front/03-zero-add-exact.lf"]

# Malformed twins of 01-zero-add-rw.lf: (what changes, old text, new text,
# the error the command line must print).
MAIN = (ROOT / FILES[0]).read_text(encoding="utf-8")
TWINS = [
    ("by-end missing", "  by-end\n", "", "error 82 at line:col 16:1"),
    ("| outside by-induction-with", "n by-induction-with", "n by-induction",
     "error 83 at line:col 14:3"),
    ("=> missing", "| zero =>  ", "| zero ", "error 84 at line:col 14:15"),
    ("] missing", "ih ]", "ih", "error 82 at line:col 16:3"),
    ("an empty alternative", "by-rfl\n", "\n", "error 85 at line:col 15:3"),
]


class Failure(Exception):
    pass


def dump():
    calls = " ".join(f's" {path}" tactic-dump-file' for path in FILES)
    run = subprocess.run([GFORTH, "src/main.fs", "tests/front/tactic-dump.fs", "-e", calls + " bye"],
                         cwd=ROOT, stdin=subprocess.DEVNULL, capture_output=True, text=True,
                         timeout=LIMIT)
    if run.returncode != 0 or run.stderr:
        raise Failure(f"tactic-dump.fs: exit {run.returncode}\n{run.stdout}{run.stderr}")
    return run.stdout.splitlines()


def differ(got, want):
    """The first line where the records differ, or None."""
    for i, (a, b) in enumerate(zip(got, want)):
        if a != b:
            return f"line {i + 1}:\n  golden: {b}\n  record: {a}"
    if len(got) != len(want):
        return f"{len(got)} lines, the golden file has {len(want)}"
    return None


def self_test(want):
    """A record with one argument moved is told apart."""
    changed = [line.replace("@15:41", "@15:42") for line in want]
    if changed == want or differ(changed, want) is None:
        raise Failure("harness self-test: a changed record is not told apart")


def check(path):
    run = subprocess.run(["bin/leanforth", "check", "--env", SLICE, str(path)], cwd=ROOT,
                         stdin=subprocess.DEVNULL, capture_output=True, text=True,
                         timeout=LIMIT, env=dict(os.environ, GFORTH=GFORTH))
    return run.returncode, run.stdout + run.stderr


def check_files():
    for path in FILES:
        code, out = check(path)
        if code != 2 or "error 80 at" not in out or "accepted" in out:
            raise Failure(f"{path}: exit {code}, expected 2 with error 80\n{out}")


def check_twins():
    with tempfile.TemporaryDirectory() as work:
        for what, old, new, error in TWINS:
            if MAIN.count(old) != 1:
                raise Failure(f"twin {what}: {old!r} is not in {FILES[0]} once")
            path = pathlib.Path(work) / "twin.lf"
            path.write_text(MAIN.replace(old, new), encoding="utf-8")
            code, out = check(path)
            if code != 4 or error not in out or "accepted" in out:
                raise Failure(f"twin {what}: exit {code}, expected 4 with {error}\n{out}")


def check_slice():
    """The export and its manifest, made again by pinned Lean."""
    with tempfile.TemporaryDirectory() as work:
        made = pathlib.Path(work) / "tactic-slice.ndjson"
        run = subprocess.run(["bash", "scripts/export.sh", str(made), "Init", "--", *SLICE_NAMES],
                             cwd=ROOT, env=dict(os.environ, LEAN=LEAN), stdin=subprocess.DEVNULL,
                             capture_output=True, timeout=LIMIT)
        if run.returncode != 0:
            raise Failure(f"scripts/export.sh: exit {run.returncode}\n{run.stderr.decode()[-400:]}")
        for suffix in ("", ".manifest.json"):
            mine = (ROOT / f"{SLICE}{suffix}").read_bytes()
            if pathlib.Path(str(made) + suffix).read_bytes() != mine:
                raise Failure(f"scripts/export.sh does not reproduce {SLICE}{suffix}")


def main_lean():
    try:
        check_slice()
    except Failure as error:
        print(f"check_tactics: {error}")
        return 1
    print(f"{SLICE} and its manifest reproduced byte for byte by pinned Lean")
    return 0


def main():
    if "--lean" in sys.argv[1:]:
        return main_lean()
    try:
        want = GOLDEN.read_text(encoding="utf-8").splitlines()
        self_test(want)
        problem = differ(dump(), want)
        if problem:
            raise Failure(f"the records differ from {GOLDEN.relative_to(ROOT)}, {problem}")
        check_files()
        check_twins()
    except Failure as error:
        print(f"check_tactics: {error}")
        return 1
    print(f"tactic records: {len(FILES)} files read as tests/front/tactics.golden says; "
          f"leanforth check stops each with error 80 (exit 2) and {len(TWINS)} malformed "
          "twins with their errors (exit 4); harness self-test passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())

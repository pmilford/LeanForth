#!/usr/bin/env python3
"""The front end on the Mathlib slice fixture (plan MF1; docs/design/MATHLIB_FRONT.md
section 6). Never a run on all of Mathlib.

1. scripts/mathlib-slice.py gives the fixture (cut and cached from the machine's
   Mathlib export, checked against tests/front/mathlib-slice.sha256).
2. `bin/leanforth check --save-snapshot` of the slice: exit 0, every declaration
   accepted, the snapshot written once for this run.
3. Against that snapshot and the slice's data, each text of TEXTS: its exit status
   and its report's lines (S1's 0 + 0 = 0 and 0 + n = n on Mathlib's Nat, the
   first statement about real numbers, x + 0 = x + 0 by rfl, with Lean's axioms;
   S1's wrong twin 0 + 0 = 1 refused at by-rfl).

Usage: GFORTH=... [LEANFORTH_LEAN=...] [MATHLIB_EXPORT=...] python3 tests/front/check_mathlib_slice.py
The fixture's inputs are found as scripts/mathlib-slice.py finds them; without a
Mathlib export the test fails (exit 1) and says so, never passing unrun. With the
fixture's cache cold it never starts the Mathlib import unless MATHLIB_SLICE_BUILD=1:
it prints "SKIPPED, NOT A PASS" and exits 3, which a tier counts as a failure
(nothing recorded) until the cache is filled.
"""
import os
import pathlib
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
LIMIT = int(os.environ.get("TEST_TIMEOUT", "1800"))
AXIOMS = "axioms: propext, Classical.choice, Quot.sound"
CHECKED = ": accepted (checked in this run, uses results from the snapshot); "
SKIPPED = 3   # scripts/mathlib-slice.py: a cold cache entry without MATHLIB_SLICE_BUILD=1
# Each text: its path, the exit status, the lines its report must hold.
TEXTS = [("tests/front/s1-rfl.lf", 0, ["t" + CHECKED + "axioms: none\n"]),
         ("tests/front/03-zero-add-exact.lf", 0, ["zero_add_ex" + CHECKED + "axioms: none\n"]),
         ("tests/front/mf-real-rfl.lf", 0, ["real_refl" + CHECKED + AXIOMS + "\n"]),
         ("tests/front/s1-rfl-wrong.lf", 4, ["error", "by-rfl"])]


def run(argv):
    return subprocess.run(argv, cwd=ROOT, capture_output=True, text=True, timeout=LIMIT)


def fixture():
    done = run([sys.executable, "scripts/mathlib-slice.py"])
    if done.returncode == SKIPPED:
        print(f"check_mathlib_slice: SKIPPED, NOT A PASS (exit {SKIPPED}): {done.stderr.strip()}")
        sys.exit(SKIPPED)
    if done.returncode != 0:
        sys.exit(f"check_mathlib_slice: no fixture (exit {done.returncode}): {done.stderr.strip()}")
    return pathlib.Path(done.stdout.strip())


def main():
    fix = fixture()
    failures = []
    with tempfile.TemporaryDirectory() as work:
        snap = pathlib.Path(work) / "slice.lfsnap"
        done = run(["bin/leanforth", "check", "--save-snapshot", str(snap),
                    str(fix / "slice.ndjson")])
        last = done.stdout.strip().splitlines()[-1:] or [""]
        if done.returncode != 0 or "rejected" in last[0] or not snap.is_file():
            sys.exit(f"check_mathlib_slice: the slice's snapshot: exit {done.returncode}, {last[0]}")
        print(f"slice: {last[0]}")
        for path, status, wanted in TEXTS:
            done = run(["bin/leanforth", "check", "--snapshot", str(snap), "--elab-data",
                        str(fix / "slice.elab.ndjson"), path])
            text = done.stdout + done.stderr
            missing = [w for w in wanted if w not in text]
            if done.returncode != status or missing:
                failures.append(f"{path}: exit {done.returncode} (wanted {status}), "
                                f"missing {missing}: {text[-600:]}")
            else:
                print(f"{path}: exit {status}")
    for f in failures:
        print("FAIL " + f)
    if failures:
        return 1
    print("Mathlib slice: all tests passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())

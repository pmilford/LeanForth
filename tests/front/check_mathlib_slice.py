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
The fixture's inputs are found as scripts/mathlib-slice.py finds them. Without a
Mathlib export a recorded run (a tier, a push, the daily run: scripts/tested-tree.py
sets REQUIRE_MATHLIB=1) fails (exit 1) and says so, never passing unrun; a user's
plain make check on a fresh clone prints "SKIPPED, NOT RUN" and goes on (exit 0),
because the export is not in the repository (fresh-clone test of 2026-11-20). With the
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
    if (done.returncode != 0 and "no Mathlib export" in done.stderr
            and os.environ.get("REQUIRE_MATHLIB") != "1"):
        # A checkout without a Mathlib export (a fresh clone: the export is 6 GB and not in the
        # repository): a user's make check goes on. scripts/tested-tree.py sets REQUIRE_MATHLIB=1,
        # so a tier, a push and the daily run still fail here.
        print("check_mathlib_slice: SKIPPED, NOT RUN: this machine has no Mathlib export "
              "(--export, $MATHLIB_EXPORT or .tools/mathlib/mathlib.ndjson), so the front end was "
              "not compared on the Mathlib slice. Every other comparison of make check ran. "
              "A tier, a push and the nightly run require the export (REQUIRE_MATHLIB=1).")
        sys.exit(0)
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

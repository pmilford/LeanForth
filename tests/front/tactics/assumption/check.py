#!/usr/bin/env python3
"""by-assumption end to end against pinned Lean (slice a2-iii;
src/front/tactics/assumption.fs, src/front/meta-tactic/assumption.fs): the
harness and its usage are tests/front/tactics/tactic_check.py's."""
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent))
import tactic_check  # noqa: E402

D = "tests/front/tactics/assumption/"
FILES = [(D + "as-one.lf", ["as_one"]), (D + "as-newest.lf", ["as_newest"]),
         (D + "as-defeq.lf", ["as_defeq"])]
WRONG = [(D + "w-as.lf", 381, "Tactic `assumption` failed",
          "\na b : Nat\nh : a ≤ b\n⊢ b ≤ a")]
UNSUPPORTED = []

if __name__ == "__main__":
    tactic_check.main("assumption", FILES, WRONG, UNSUPPORTED)

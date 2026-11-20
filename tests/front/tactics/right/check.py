#!/usr/bin/env python3
"""by-right end to end against pinned Lean (plan row TB1; src/front/tactics/right.fs,
src/front/meta-tactic/constructor.fs's lf-goal-nth-constructor): the harness and its usage are
tests/front/tactics/tactic_check.py's."""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tests/front/tactics"))
import tactic_check  # noqa: E402

D = "tests/front/tactics/right/"
FILES = [(D + "ri-or.lf", ["ri_or"]), (D + "ri-le.lf", ["ri_le"])]
WRONG = [(D + "w-ri-not.lf", 387, "Tactic `right` failed: target is not an inductive datatype",
          "\na b : Nat\n⊢ ¬a = b"),
         (D + "w-ri-and.lf", 388,
          "Tactic `right` failed: right tactic works for inductive types with exactly 2 "
          "constructors", "\na b : Nat\n⊢ a ≤ b ∧ b ≤ a")]
UNSUPPORTED = []

if __name__ == "__main__":
    tactic_check.main("right", FILES, WRONG, UNSUPPORTED)

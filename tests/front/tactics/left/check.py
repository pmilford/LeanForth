#!/usr/bin/env python3
"""by-left end to end against pinned Lean (plan row TB1; src/front/tactics/left.fs,
src/front/meta-tactic/constructor.fs's lf-goal-nth-constructor): the harness and its usage are
tests/front/tactics/tactic_check.py's."""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tests/front/tactics"))
import tactic_check  # noqa: E402

D = "tests/front/tactics/left/"
FILES = [(D + "le-or.lf", ["le_or"]), (D + "le-le.lf", ["le_le"])]
# Lean's first line and the detail after it (apply's note prints the full type as Lean's
# `∀ {n : Nat}, n.le n`, LeanForth's printer otherwise: plan 8.6; the lines compared stop
# before it).
WRONG = [(D + "w-le-and.lf", 386,
          "Tactic `left` failed: left tactic works for inductive types with exactly 2 constructors",
          "\na b : Nat\n⊢ a ≤ b ∧ b ≤ a"),
         (D + "w-le-not.lf", 385, "Tactic `left` failed: target is not an inductive datatype",
          "\na b : Nat\n⊢ ¬a = b"),
         (D + "w-le-le.lf", 380, "Tactic `apply` failed: could not unify the conclusion of the term",
          "  Nat.le ?n ?n\nwith the goal\n  a ≤ b\n\nNote: The full type of the term is")]
UNSUPPORTED = []

if __name__ == "__main__":
    tactic_check.main("left", FILES, WRONG, UNSUPPORTED)

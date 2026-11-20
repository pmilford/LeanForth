#!/usr/bin/env python3
"""by-clear end to end against pinned Lean (plan row TB1; src/front/tactics/clear.fs,
src/front/meta-tactic/goal.fs's lf-goal-clear!, src/front/tactic-core.fs's lf-tac-get-fvar):
the harness and its usage are tests/front/tactics/tactic_check.py's."""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tests/front/tactics"))
import tactic_check  # noqa: E402

D = "tests/front/tactics/clear/"
FILES = [(D + "cl-hyp.lf", ["cl_hyp"]), (D + "cl-var.lf", ["cl_var"])]
WRONG = [(D + "w-cl-dep.lf", 441, "Tactic `clear` failed: variable 'h' depends on 'a'",
          "\na : Nat\nh : a ≤ a\n⊢ a ≤ a"),
         (D + "w-cl-target.lf", 442, "Tactic `clear` failed: target depends on 'a'",
          "\na : Nat\n⊢ a ≤ a"),
         (D + "w-cl-const.lf", 389,
          "Unexpected term `Nat.le_refl`; expected single reference to variable", "")]
UNSUPPORTED = []

if __name__ == "__main__":
    tactic_check.main("clear", FILES, WRONG, UNSUPPORTED)

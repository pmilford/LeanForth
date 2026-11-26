#!/usr/bin/env python3
"""by-simp-only[ ] at[ ] at hypotheses, end to end against pinned Lean (plan row FE9, simp
slice SL1a-2 of docs/design/TACTIC_SIMP.md, and plan row 9.4.8z2(e)'s two rule errors):
src/front/tactics/simp-only.fs over src/front/simp/goal.fs. The harness and its usage are
tests/front/tactics/tactic_check.py's, against simp's slice of Init
(tests/front/simp-slice.ndjson and its format-4 elaboration data), with this slice's own Lean
twins (simp-2.lean, simp-2-wrong.lean) and golden (simp-2.golden). UNSUPPORTED are the texts
LeanForth answers 99 (not supported yet) for, which Lean accepts (simp-2.lean): at[ * ] (a
hypothesis changed by defeq that another depends on, also 99, is test.fs's)."""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tests/front/tactics"))
import tactic_check  # noqa: E402

D = "tests/front/tactics/simp-2/"
ENV = tactic_check.Env("tests/front/simp-slice.ndjson", "tests/front/simp-slice.elab.ndjson",
                       "simp-dump")
FILES = [(D + "simp-at.lf", ["simp_at_defeq", "simp_at_proof", "simp_at_goal", "simp_at_two",
                             "simp_at_mixed", "simp_at_false", "simp_at_false_defeq",
                             "simp_at_true", "simp_at_one_still",
                             "simp_at_goal_kept"])]
MISMATCH = "  h\nhas type\n  True\nbut is expected to have type\n  a = b"
NOTE = ("\nNote: This simp theorem will rewrite `a ≤ b` to `True`, which should not be applied "
        "in the reverse direction")
WRONG = [(D + "w-at-self.lf", 96, "Type mismatch", MISMATCH),
         (D + "w-at-no-progress.lf", 500, "`simp` made no progress", ""),
         (D + "w-at-two-no-progress.lf", 500, "`simp` made no progress", ""),
         (D + "w-arg-var.lf", 501,
          "Invalid argument: Variable `a` is not a proposition or let-declaration", ""),
         (D + "w-symm-prop.lf", 502,
          "Invalid `←` modifier: Cannot be applied to a rule that rewrites to `True`", NOTE)]
NOT_YET = "not supported yet: this case of the tactic"
UNSUPPORTED = [(D + "u-at-star.lf", 99, NOT_YET)]

if __name__ == "__main__":
    tactic_check.main("simp-2", FILES, WRONG, UNSUPPORTED, env=ENV, lean=D + "simp-2.lean",
                      lean_wrong=D + "simp-2-wrong.lean", golden=ROOT / D / "simp-2.golden")

#!/usr/bin/env python3
"""by-simp-only[ ] on the target, end to end against pinned Lean (plan row FE9, simp slice
SL1a-1 of docs/design/TACTIC_SIMP.md): src/front/tactics/simp-only.fs over simp's files
(src/front/simp/). The harness and its usage are tests/front/tactics/tactic_check.py's,
against simp's slice of Init (tests/front/simp-slice.ndjson and its format-4 elaboration
data), with this slice's own Lean twins (simp-1.lean, simp-1-wrong.lean) and golden
(simp-1.golden). UNSUPPORTED are the texts LeanForth answers 99 (not supported yet) for,
which Lean accepts (simp-1.lean): at[ ], h : True (True = True, a perm theorem), a definition
to unfold, and 6 unified with 2 * 3 (LeanForth's unifier answers unsupported)."""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tests/front/tactics"))
import tactic_check  # noqa: E402

D = "tests/front/tactics/simp-1/"
ENV = tactic_check.Env("tests/front/simp-slice.ndjson", "tests/front/simp-slice.elab.ndjson",
                       "simp-dump")
FILES = [(D + "simp-only.lf", ["simp_add_zero=propext", "simp_hyp=propext",
                               "simp_hyp_whole=propext", "simp_true", "simp_self=propext",
                               "simp_symm=propext", "simp_prop=propext",
                               "simp_same_head=propext", "simp_mul_zero=propext",
                               "simp_mul_one=propext", "simp_mul_one_twice=propext",
                               "simp_zero_add_mul_one=propext", "simp_sub_self=propext",
                               "simp_chain=propext"])]
WRONG = [(D + "w-no-progress.lf", 500, "`simp` made no progress", ""),
         (D + "w-head-only.lf", 500, "`simp` made no progress", ""),
         (D + "w-unused-rule-closes.lf", 90, "No goals to be solved", "")]
NOT_YET = "not supported yet: this case of the tactic"
UNSUPPORTED = [(D + "u-at.lf", 99, NOT_YET),
               (D + "u-hyp-prop.lf", 99, NOT_YET),
               (D + "u-def.lf", 99, NOT_YET),
               (D + "u-literal.lf", 99, NOT_YET)]

if __name__ == "__main__":
    tactic_check.main("simp-1", FILES, WRONG, UNSUPPORTED, env=ENV, lean=D + "simp-1.lean",
                      lean_wrong=D + "simp-1-wrong.lean", golden=ROOT / D / "simp-1.golden")

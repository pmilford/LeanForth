#!/usr/bin/env python3
"""by-simp-only[ ] below binders and through congruence lemmas, end to end against pinned Lean
(plan row FE9, simp group 3 of docs/design/TACTIC_SIMP.md: slice SL1b's simpArrow and
simpForall, slice SL2's congruence): src/front/simp/main.fs under src/front/tactics/simp-only.fs.
The harness and its usage are tests/front/tactics/tactic_check.py's, against simp's slice of
Init (tests/front/simp-slice.ndjson and its format-4 elaboration data), with this group's own
Lean twins (simp-3.lean, simp-3-wrong.lean) and golden (simp-3.golden). A goal with a binder is
made by by-revert, as no LeanForth statement writes -> or ∀ yet; simp below fun, which no
statement can hold, is test.fs's."""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tests/front/tactics"))
import tactic_check  # noqa: E402

D = "tests/front/tactics/simp-3/"
ENV = tactic_check.Env("tests/front/simp-slice.ndjson", "tests/front/simp-slice.elab.ndjson",
                       "simp-dump")
FUNEXT = "=propext, Quot.sound"   # forall_congr's axioms
FILES = [(D + "simp-binders.lf", ["simp_binder_arrow", "simp_binder_forall" + FUNEXT,
                                  "simp_binder_forall_hyp" + FUNEXT, "simp_binder_nested"]),
         (D + "simp-congr.lf", ["simp_ite=propext", "simp_ite_branch=propext",   # ite_congr's
                                 "simp_ite_forall" + FUNEXT, "simp_ite_nested=propext"]),
         (D + "simp-decide.lf", ["simp_decide=propext"])]
MISMATCH = "  Nat.add_zero a\nhas type\n  a + 0 = a\nbut is expected to have type\n  True"
NO_PROGRESS = "`simp` made no progress"
WRONG = [(D + "w-binder-skipped.lf", 96, "Type mismatch", MISMATCH),
         (D + "w-binder-no-progress.lf", 500, NO_PROGRESS, ""),
         (D + "w-ite-no-progress.lf", 500, NO_PROGRESS, "")]
UNSUPPORTED = []

if __name__ == "__main__":
    tactic_check.main("simp-3", FILES, WRONG, UNSUPPORTED, env=ENV, lean=D + "simp-3.lean",
                      lean_wrong=D + "simp-3-wrong.lean", golden=ROOT / D / "simp-3.golden")

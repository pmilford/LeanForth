#!/usr/bin/env python3
"""Case patterns, slice E2a, end to end against pinned Lean (plan row TB2, piece E;
docs/design/TACTIC_PATTERNS.md: by-subst, by-subst[ ] and by-subst-vars,
src/front/tactics/subst.fs over src/front/meta-tactic/subst.fs; rfl in a pattern and
by-rintro[ ], src/front/rcases.fs and src/front/tactics/rintro.fs): the harness and its
usage are tests/front/tactics/tactic_check.py's, against decide's slice of Init
(tests/front/decide-slice.ndjson, which holds Eq.rec, Eq.ndrec, Eq.symm, HEq, eq_of_heq and
Nat.casesAuxOn), with this batch's own Lean twins (batch-h.lean, batch-h-wrong.lean) and
golden (batch-h.golden).

The wrong twins that name a hypothesis or a statement variable the goal no longer has
(Lean's "Unknown identifier") are refused with LeanForth's own error 76 (a name the goal's
context lacks), so --lean does not ask Lean for their text."""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tests/front/tactics"))
import tactic_check  # noqa: E402

D = "tests/front/tactics/batch-h/"
ENV = tactic_check.Env("tests/front/decide-slice.ndjson", "tests/front/decide-slice.elab.ndjson",
                       "decide-dump")
FILES = [(D + "subst.lf", ["sb_right", "sb_left", "sb_dep_before", "sb_dep_after", "sb_rec",
                           "sb_rec_left", "sb_heq", "sb_reduced", "sb_var_right", "sb_var_left",
                           "sb_many", "sb_skip", "sb_hidden"]),
         (D + "rfl.lf", ["rf_exists", "rf_right", "rf_left", "rf_alts", "rf_cleared"]),
         (D + "rintro.lf", ["ri_name", "ri_alts", "ri_tuple", "ri_rfl", "ri_nat"]),
         (D + "subst-vars.lf", ["sv_two", "sv_var_first"])]

MISMATCH = "  right\nhas type\n  c = c\nbut is expected to have type\n  a = a"
FORM = "Tactic `subst` failed: invalid equality proof, it is not of the form (x = t) or (t = x)"
WRONG = [(D + "w-hidden-subst.lf", 96, "Type mismatch", MISMATCH),
         (D + "w-hidden-reduced.lf", 96, "Type mismatch", MISMATCH),
         (D + "w-hidden-heq.lf", 96, "Type mismatch", MISMATCH),
         (D + "w-rintro-group.lf", 94, "Tactic `introN` failed: There are no additional binders"
          " or `let` bindings in the goal to introduce",
          "\ncase inl\na b : Nat\nx : a = b\nz : b = a\n⊢ b = a"),
         (D + "subst-errors.lf", 476, "Tactic `subst` failed: 'a' occurs at",
          "  a\n\na : Nat\nh : a = a\n⊢ True"),
         (D + "w-no-equation.lf", 479,
          "Tactic `subst` failed: did not find equation for eliminating 'a'", "\na : Nat\n⊢ a = a"),
         (D + "w-rfl-not-eq.lf", 478, FORM,
          "  True\n\na b : Nat\nleft✝ : a = b\nright✝ : True\n⊢ b = a"),
         (D + "w-sides.lf", 478, FORM, "  Nat.zero = Nat.zero\n\nh : Nat.zero = Nat.zero\n⊢ False")]
UNNAMED = "malformed elaboration: a term that is no node, or a value unfit for the declaration"
OWN = [(D + "w-subst-var-used.lf", 76, UNNAMED, "")]
UNSUPPORTED = [(D + "x-let.lf", 99, "not supported yet"),
               (D + "x-have.lf", 93, "not supported yet")]

if __name__ == "__main__":
    wrong = WRONG if "--lean" in sys.argv else WRONG + OWN
    tactic_check.main("batch-h", FILES, wrong, UNSUPPORTED, env=ENV, lean=D + "batch-h.lean",
                      lean_wrong=D + "batch-h-wrong.lean", golden=ROOT / D / "batch-h.golden")

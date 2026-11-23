#!/usr/bin/env python3
"""Case patterns, slice E1, end to end against pinned Lean (plan row TB2, piece E;
docs/design/TACTIC_PATTERNS.md: by-obtain[ and by-rcases[, src/front/tactics/obtain.fs, the
walk src/front/rcases.fs, the reader src/front/pattern-syntax.fs, the Meta split
src/front/meta-tactic/meta-induction.fs and cases.fs): the harness and its usage are
tests/front/tactics/tactic_check.py's, against decide's slice of Init
(tests/front/decide-slice.ndjson, which holds And.casesOn, Or.casesOn, Exists.casesOn and
Nat.casesAuxOn), with this batch's own Lean twins (batch-g.lean, batch-g-wrong.lean) and
golden (batch-g.golden).

Two wrong twins name a hypothesis the goal does not have (Lean's "Unknown identifier"):
LeanForth refuses both with errors of its own (76, a hypothesis no goal holds; 98, a
statement variable the split cleared), so --lean does not ask Lean for their text."""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tests/front/tactics"))
import tactic_check  # noqa: E402

D = "tests/front/tactics/batch-g/"
ENV = tactic_check.Env("tests/front/decide-slice.ndjson", "tests/front/decide-slice.elab.ndjson",
                       "decide-dump")
FILES = [(D + "obtain.lf", ["ob_and", "ob_exists", "ob_nested", "ob_fewer", "ob_clear",
                            "ob_clear_dep", "ob_term", "ob_term_name", "ob_name"]),
         (D + "rcases.lf", ["rc_or", "rc_three", "rc_or_and", "rc_nat", "rc_comment"]),
         (D + "nest.lf", ["ns_left", "ns_flat", "ns_right"]),
         (D + "order.lf", ["od_depth", "od_tags", "od_one"]),
         (D + "hidden.lf", ["hd_kept"])]

WRONG = [(D + "w-tag-intro.lf", 210, "Case tag `intro` not found.",
          "\nNote: There are no cases to select."),
         (D + "w-hidden-extra.lf", 96, "Type mismatch",
          "  right\nhas type\n  c = c\nbut is expected to have type\n  0 = a")]
OWN = [(D + "w-order.lf", 76, "malformed elaboration: a term that is no node, or a value unfit"
          " for the declaration", ""),
       (D + "w-clear-used.lf", 98, "Tactic `exact` failed: attempting to close the goal using",
        "  _fvar.2\nthis is often due to an occurs-check failure\n\na b : Nat\n⊢ a = b")]
UNSUPPORTED = [(D + "x-rfl.lf", 99, "not supported yet"),
               (D + "x-indexed.lf", 99, "not supported yet"),
               (D + "x-not-inductive.lf", 136, "not supported yet")]

if __name__ == "__main__":
    wrong = WRONG if "--lean" in sys.argv else WRONG + OWN
    tactic_check.main("batch-g", FILES, wrong, UNSUPPORTED, env=ENV, lean=D + "batch-g.lean",
                      lean_wrong=D + "batch-g-wrong.lean", golden=ROOT / D / "batch-g.golden")

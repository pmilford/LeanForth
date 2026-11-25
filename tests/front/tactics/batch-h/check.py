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
                           "sb_many", "sb_skip", "sb_hidden"])]

WRONG = []
UNNAMED = "malformed elaboration: a term that is no node, or a value unfit for the declaration"
OWN = []
UNSUPPORTED = []

if __name__ == "__main__":
    wrong = WRONG if "--lean" in sys.argv else WRONG + OWN
    tactic_check.main("batch-h", FILES, wrong, UNSUPPORTED, env=ENV, lean=D + "batch-h.lean",
                      lean_wrong=D + "batch-h-wrong.lean", golden=ROOT / D / "batch-h.golden")

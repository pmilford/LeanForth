#!/usr/bin/env python3
"""Case patterns, slice E2b, end to end against pinned Lean (plan row TB2, piece E;
docs/design/TACTIC_PATTERNS.md: by-contra[ ] and by-contra: with a pattern,
src/front/tactics/by-contra.fs over src/front/rcases.fs's lf-rintro; by-contradiction on an
empty type, src/front/meta-tactic/contradiction.fs's rule 6; obtain through a field an
earlier split substituted, the E1 review's probe p27): the harness and its usage are
tests/front/tactics/tactic_check.py's, against the patterns slice of Init
(tests/front/patterns-slice.ndjson, cut from tests/front/patterns-slice.roots: decide's
slice and the declarations the case-pattern slices need, Empty, Prod and Dvd among them),
with this batch's own Lean twins (batch-h2.lean, batch-h2-wrong.lean) and golden
(batch-h2.golden).

w-contra-two.lf is LeanForth's own reading error (474: by-contra[ takes one pattern, where
Lean's by_contra k j does not parse), so --lean does not ask Lean for its text."""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tests/front/tactics"))
import tactic_check  # noqa: E402

D = "tests/front/tactics/batch-h2/"
ENV = tactic_check.Env("tests/front/patterns-slice.ndjson",
                       "tests/front/patterns-slice.elab.ndjson", "patterns-dump")
FILES = [(D + "by-contra.lf", ["bc_tuple", "bc_alts", "bc_rfl", "bc_rfl_word", "bc_name",
                               "bc_clear", "bc_clear_word", "bc_anon_word", "bc_nest"]),
         (D + "empty.lf", ["em_empty", "em_later", "em_dep"]),
         (D + "dvd.lf", ["dv_obtain"])]

FAILED = "Tactic `contradiction` failed"
UNNAMED = "malformed elaboration: a term that is no node, or a value unfit for the declaration"
WRONG = [(D + "w-looks-empty.lf", 449, FAILED, "\na : Nat\nh : False ∧ a = a\n⊢ False"),
         (D + "w-one-ctor.lf", 449, FAILED, "\nh : True\n⊢ False")]
OWN = [(D + "w-contra-alts.lf", 76, UNNAMED, ""),
       (D + "w-contra-two.lf", 474, "by-obtain[, by-rcases[ and by-contra[ take one pattern", "")]
UNSUPPORTED = [(D + "x-indexed.lf", 99, "not supported yet")]

if __name__ == "__main__":
    wrong = WRONG if "--lean" in sys.argv else WRONG + OWN
    tactic_check.main("batch-h2", FILES, wrong, UNSUPPORTED, env=ENV, lean=D + "batch-h2.lean",
                      lean_wrong=D + "batch-h2-wrong.lean", golden=ROOT / D / "batch-h2.golden")

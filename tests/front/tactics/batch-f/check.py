#!/usr/bin/env python3
"""Tactic batch 3c end to end against pinned Lean (plan row TB2: the anonymous constructor
<< >> and ⟨ ⟩, src/front/elab-term.fs's port of elabAnonymousConstructor; by-exists[ ],
src/front/tactics/exists.fs; bracket lists over several lines, src/author/runner.fs and
scopes.fs): the harness and its usage are tests/front/tactics/tactic_check.py's, against
decide's slice of Init (tests/front/decide-slice.ndjson, as batch-a's), with this batch's own
Lean twins (batch-f.lean, batch-f-wrong.lean) and golden (batch-f.golden)."""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tests/front/tactics"))
import tactic_check  # noqa: E402

D = "tests/front/tactics/batch-f/"
ENV = tactic_check.Env("tests/front/decide-slice.ndjson", "tests/front/decide-slice.elab.ndjson",
                       "decide-dump")
FILES = [(D + "anon.lf", ["an_and", "an_three", "an_nested", "an_id", "an_true", "an_exists",
                          "an_have", "an_refine", "an_case"]),
         (D + "exists.lf", ["ex_eq", "ex_and", "ex_and3", "ex_open"]),
         (D + "lines.lf", ["ml_names", "ml_rw", "ml_exacts"])]

ANON = "Invalid `⟨...⟩` notation: The expected type"
FIELDS = "Insufficient number of fields for `⟨...⟩` constructor: Constructor"
NOTE = ("\nNote: This notation can only be used when the expected type is an inductive type with"
        " a single constructor")
WRONG = [(D + "w-anon-few.lf", 466, FIELDS + " `And.intro` has 2 explicit field, but only 1 was"
          " provided", ""),
         (D + "w-anon-fields.lf", 467, FIELDS + " `Eq.refl` does not have explicit fields, but 1"
          " was provided", ""),
         (D + "w-anon-nested.lf", 467, FIELDS + " `Eq.refl` does not have explicit fields, but 2"
          " were provided", ""),
         (D + "w-anon-ctors.lf", 465, ANON + " `a = b ∨ b = a` has more than one constructor",
          NOTE),
         (D + "w-anon-none.lf", 464, ANON + " `False` has no constructors", ""),
         (D + "w-anon-unknown.lf", 462, ANON + " of this term could not be determined", ""),
         (D + "w-exists-many.lf", 467, FIELDS + " `Eq.refl` does not have explicit fields, but 2"
          " were provided", ""),
         (D + "w-exists-open.lf", 89, "unsolved goals", "a b : Nat\nh : a = b\n⊢ b = a")]
UNSUPPORTED = [(D + "x-anon-leaf.lf", 132, "not supported yet"),
               (D + "x-anon-arg.lf", 131, "not supported yet: a coercion"),
               (D + "x-anon-pi.lf", 133, "not supported yet")]
# A message no natural text of this slice reaches (Prop cannot be written yet: error 70):
# batch-f-wrong.lean's w_anon_type gives Lean's, which test.fs checks LeanForth's parts of.
LEAN_ONLY = [("", 463, ANON + " `Prop` is not an inductive type", NOTE)]

if __name__ == "__main__":
    wrong = WRONG + LEAN_ONLY if "--lean" in sys.argv else WRONG
    tactic_check.main("batch-f", FILES, wrong, UNSUPPORTED, env=ENV, lean=D + "batch-f.lean",
                      lean_wrong=D + "batch-f-wrong.lean", golden=ROOT / D / "batch-f.golden")

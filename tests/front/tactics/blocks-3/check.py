#!/usr/bin/env python3
"""Tactic blocks, slice 3, end to end against pinned Lean (plan row TB2, piece F; design
docs/design/TACTIC_BLOCKS.md 4): by-try, by-first, by-repeat and by-any-goals (Lean's try,
first, repeat, any_goals), src/front/tactics/blocks.fs over the runner's handlers
(src/front/tactic-run.fs) and the reader's bare alternatives (src/front/tactic-syntax.fs).
The harness and its usage are tests/front/tactics/tactic_check.py's, against decide's slice
of Init (tests/front/decide-slice.ndjson, as blocks-1's and blocks-2's), with this slice's
own Lean twins (blocks-3.lean, blocks-3-wrong.lean) and golden (blocks-3.golden).
UNSUPPORTED are the texts where Lean logs an error inside a block that may still take it
back (490, the coordinator's rule): Lean rejects u_any_term, u_any_brace, u_try_have_brace and
u_try_have_brace2 (blocks-3-wrong.lean; a brace that is a have-by's whole body logs) and
accepts u_any_gap (blocks-3.lean, the known gap).
OWN is w-try-brace.lf, where Lean says "Unknown identifier `j`" and LeanForth answers its
own 76 (as batch-g's), so --lean does not ask Lean for its text."""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tests/front/tactics"))
import tactic_check  # noqa: E402

D = "tests/front/tactics/blocks-3/"
ENV = tactic_check.Env("tests/front/decide-slice.ndjson", "tests/front/decide-slice.elab.ndjson",
                       "decide-dump")
FILES = [(D + "try.lf", ["try_skip", "try_runs", "try_partial", "try_then", "try_brace",
                         "try_deep"]),
         (D + "first.lf", ["first_second", "first_one", "first_rollback", "first_then",
                           "first_chain"]),
         (D + "repeat.lf", ["repeat_ctor", "repeat_none", "repeat_rollback"]),
         (D + "any-goals.lf", ["any_some", "any_all_goals", "any_chain"]),
         (D + "recover.lf", ["rec_q8", "rec_q8_inner", "rec_try_have", "rec_try_brace",
                             "rec_try_brace_fail", "rec_brace_try", "rec_then_try"]),
         (D + "names.lf", ["names_try", "names_first", "names_mvar"])]

MISMATCH = "  k\nhas type\n  b = a\nbut is expected to have type\n  a = b"
WRONG = [(D + "w-try-open.lf", 89, "unsolved goals", "a b : Nat\nh : a = b\nk : b = a\n⊢ a = b"),
         (D + "w-first-all.lf", 96, "Type mismatch", MISMATCH),
         (D + "w-any-all.lf", 469, "Tactic failed on all goals:", ""),
         (D + "w-any-none.lf", 469, "Tactic failed on all goals:", "")]
UNNAMED = "malformed elaboration: a term that is no node, or a value unfit for the declaration"
OWN = [(D + "w-try-brace.lf", 76, UNNAMED, "")]   # Lean: Unknown identifier `j`
UNDECIDED = "Lean logs this error and goes on; a block around may take it back: not followed yet"
UNSUPPORTED = [(D + "u-any-term.lf", 490, UNDECIDED),
               (D + "u-any-brace.lf", 490, UNDECIDED),
               (D + "u-any-gap.lf", 490, UNDECIDED),
               (D + "u-try-have-brace.lf", 490, UNDECIDED),
               (D + "u-try-have-brace2.lf", 490, UNDECIDED)]

if __name__ == "__main__":
    wrong = WRONG if "--lean" in sys.argv else WRONG + OWN
    tactic_check.main("blocks-3", FILES, wrong, UNSUPPORTED, env=ENV, lean=D + "blocks-3.lean",
                      lean_wrong=D + "blocks-3-wrong.lean", golden=ROOT / D / "blocks-3.golden")

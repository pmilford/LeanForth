#!/usr/bin/env python3
"""Tactic blocks, slice 2, end to end against pinned Lean (plan row TB2, piece F; design
docs/design/TACTIC_BLOCKS.md): t1 <;> t2 (Lean's macro focus (t1; all_goals t2)) and
by-all-goals (Lean's all_goals), src/front/tactics/blocks.fs over the runner's per-goal mode
(src/front/tactic-run.fs) and the reader's then-step (src/front/tactic-syntax.fs). The harness
and its usage are tests/front/tactics/tactic_check.py's, against decide's slice of Init
(tests/front/decide-slice.ndjson, as blocks-1's), with this slice's own Lean twins
(blocks-2.lean, blocks-2-wrong.lean) and golden (blocks-2.golden). OWN is refused with
LeanForth's own code where Lean's message differs (76 where Lean says unknown identifier:
both reject, TACTIC_STATUS row NR) and READ is LeanForth's own reading error (no Lean twin:
Lean's parser reports its own); both are checked in the plain mode only."""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tests/front/tactics"))
import tactic_check  # noqa: E402

D = "tests/front/tactics/blocks-2/"
ENV = tactic_check.Env("tests/front/decide-slice.ndjson", "tests/front/decide-slice.elab.ndjson",
                       "decide-dump")
FILES = [(D + "and-then.lf", ["at_and", "at_none", "at_one", "at_three", "at_chain", "at_rest",
                              "at_ind", "at_induct", "at_brace", "at_inner", "at_alt", "at_loc",
                              "at_names"]),
         (D + "all-goals.lf", ["ag_and", "ag_left", "ag_assigned", "ag_steps"])]

MISMATCH = "  h\nhas type\n  a = b\nbut is expected to have type\n  b = a"
WRONG = [(D + "w-ag-second.lf", 96, "Type mismatch", MISMATCH),
         (D + "w-then-second.lf", 96, "Type mismatch", MISMATCH),
         (D + "w-then-open.lf", 89, "unsolved goals",
          "case left\na b : Nat\nh : a = b\nk : b = a\nx : a = b\n⊢ a = b\n\n"
          "case right\na b : Nat\nh : a = b\nk : b = a\nx : a = b\n⊢ b = a")]
OWN = [(D + "w-then-name.lf", 76,
        "malformed elaboration: a term that is no node, or a value unfit for the declaration", "")]
READ = [(D + "then-errors.lf", 468, "<;> follows no tactic of its block (t1 <;> t2)", ""),
        (D + "w-then-empty.lf", 85, "this block needs at least one tactic (an alternative,"
         " by-case: or a by- block)", "")]
UNSUPPORTED = []

if __name__ == "__main__":
    wrong = WRONG if "--lean" in sys.argv else WRONG + OWN + READ
    tactic_check.main("blocks-2", FILES, wrong, UNSUPPORTED, env=ENV, lean=D + "blocks-2.lean",
                      lean_wrong=D + "blocks-2-wrong.lean", golden=ROOT / D / "blocks-2.golden")

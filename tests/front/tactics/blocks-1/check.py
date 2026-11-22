#!/usr/bin/env python3
"""Tactic blocks, slice 1, end to end against pinned Lean (plan row TB2, piece F; design
docs/design/TACTIC_BLOCKS.md): braces { } (src/front/tactics/blocks.fs, Lean's bullet and
tacticSeqBracketed), by-focus (Lean's focus) and by-have-by: (src/front/tactics/have.fs, Lean's
have h : T := by tacs) over the runner's block modes (src/front/tactic-run.fs). The harness and
its usage are tests/front/tactics/tactic_check.py's, against decide's slice of Init
(tests/front/decide-slice.ndjson, as batch-f's), with this slice's own Lean twins
(blocks-1.lean, blocks-1-wrong.lean) and golden (blocks-1.golden). READ is LeanForth's own
reading error (no Lean twin: Lean's parser reports its own), checked in the plain mode only."""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tests/front/tactics"))
import tactic_check  # noqa: E402

D = "tests/front/tactics/blocks-1/"
ENV = tactic_check.Env("tests/front/decide-slice.ndjson", "tests/front/decide-slice.elab.ndjson",
                       "decide-dump")
FILES = [(D + "braces.lf", ["br_and", "br_two", "br_three", "br_names", "br_ind", "br_case"]),
         (D + "have-by.lf", ["hb_symm", "hb_inner", "hb_twice"]),
         (D + "focus.lf", ["fo_and", "fo_open", "fo_split"])]

UNSOLVED = "unsolved goals"
NONE = "No goals to be solved"
WRONG = [(D + "w-brace-open.lf", 89, UNSOLVED,
          "case right\na b : Nat\nh : a = b\nk x : b = a\n⊢ b = a"),
         (D + "w-brace-empty.lf", 89, UNSOLVED, "a b : Nat\nh : a = b\n⊢ a = b"),
         (D + "w-brace-none.lf", 90, NONE, ""),
         (D + "w-have-by-open.lf", 89, UNSOLVED, "a b : Nat\nh x : a = b\n⊢ b = a"),
         (D + "w-focus-none.lf", 90, NONE, ""),
         (D + "w-focus-open.lf", 89, UNSOLVED,
          "case left\na b : Nat\nh : a = b\nk : b = a\nx : a = b\n⊢ a = b\n\n"
          "case right\na b : Nat\nh : a = b\nk : b = a\n⊢ b = a")]
READ = [(D + "brace-errors.lf", 83, "no block of this word's kind is open (| belongs right inside"
         " by-induction-with, } closes {)", "")]
UNSUPPORTED = [(D + "x-have-by-name.lf", 99, "not supported yet")]

if __name__ == "__main__":
    wrong = WRONG if "--lean" in sys.argv else WRONG + READ
    tactic_check.main("blocks-1", FILES, wrong, UNSUPPORTED, env=ENV, lean=D + "blocks-1.lean",
                      lean_wrong=D + "blocks-1-wrong.lean", golden=ROOT / D / "blocks-1.golden")

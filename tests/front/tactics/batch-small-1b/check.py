#!/usr/bin/env python3
"""Small tactics 1, iterate, end to end against pinned Lean (plan row TB2): n by-iterate tacs
by-end (src/front/tactics/iterate.fs, a block mode of the runner, tactic-run.fs). The harness and
its usage are tests/front/tactics/tactic_check.py's, against decide's slice of Init
(tests/front/decide-slice.ndjson), with this batch's own Lean twins (batch-small-1b.lean,
batch-small-1b-wrong.lean) and golden (batch-small-1b.golden). Kept apart from batch-small-1
so that each test.fs stays under 30 s. UNSUPPORTED are u-it-term.lf, a count that is no numeral,
which Lean's parser refuses, and u-it-deep.lf, a count past iterate's weight bound (tit-most),
which Lean accepts up to 251."""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tests/front/tactics"))
import tactic_check  # noqa: E402

D = "tests/front/tactics/batch-small-1b/"
ENV = tactic_check.Env("tests/front/decide-slice.ndjson", "tests/front/decide-slice.elab.ndjson",
                       "decide-dump")
FILES = [(D + "iterate.lf", ["it_two", "it_zero", "it_seq", "it_nest"])]

GOAL_LEFT = "case left\na b : Nat\nh : a = b\nk : b = a\n⊢ a = b"
WRONG = [(D + "w-it-more.lf", 90, "No goals to be solved", ""),
         (D + "w-it-ctor.lf", 383, "Tactic `constructor` failed: no applicable constructor found",
          "\n" + GOAL_LEFT),
         (D + "w-it-short.lf", 89, "unsolved goals",
          "case right\na b : Nat\nh : a = b\nk : b = a\n⊢ b = a")]
UNSUPPORTED = [(D + "u-it-term.lf", 99, "not supported yet"),
               (D + "u-it-deep.lf", 99, "not supported yet")]

if __name__ == "__main__":
    tactic_check.main("batch-small-1b", FILES, WRONG, UNSUPPORTED, env=ENV,
                      lean=D + "batch-small-1b.lean", lean_wrong=D + "batch-small-1b-wrong.lean",
                      golden=ROOT / D / "batch-small-1b.golden")

#!/usr/bin/env python3
"""Tactic batch 3b end to end against pinned Lean (plan row TB2: lists of names up to ] for
by-intro[ ], by-revert[ ], by-clear[ ] and by-rename-i[ ]; holes _, ?_ and ?: NAME with
by-refine, by-exact, by-apply and by-have:; src/front/tactic-syntax.fs's list shapes,
src/front/new-goals.fs, tactic-core.fs's lf-tac-elab-with-holes, elab-term.fs's holes, and
src/front/tactics/intro.fs, revert.fs, clear.fs, rename-i.fs, refine.fs): the harness and
its usage are tests/front/tactics/tactic_check.py's, against decide's slice of Init
(tests/front/decide-slice.ndjson, as batch-a's), with this batch's own Lean twins
(batch-e.lean, batch-e-wrong.lean) and golden (batch-e.golden)."""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tests/front/tactics"))
import tactic_check  # noqa: E402

D = "tests/front/tactics/batch-e/"
ENV = tactic_check.Env("tests/front/decide-slice.ndjson", "tests/front/decide-slice.elab.ndjson",
                       "decide-dump")
FILES = [(D + "names.lf", ["nl_intro", "nl_holes", "nl_revert_dep", "nl_clear", "nl_rename",
                           "nl_rename_hole"]),
         (D + "holes.lf", ["rf_and", "rf_and_case", "rf_named", "rf_one", "rf_or",
                           "rf_natural", "ex_hole", "ap_hole", "hv_hole"])]


def context(goal):
    return "context:\na b : Nat\nh : a = b\n⊢ " + goal


PLACEHOLDER = "don't know how to synthesize placeholder"
WRONG = [(D + "w-refine-hole.lf", 461, PLACEHOLDER, context("a = b")),
         (D + "w-exact-hole.lf", 461, PLACEHOLDER, context("a = b")),
         (D + "w-exact-synth.lf", 461, PLACEHOLDER, context("a = b")),
         (D + "w-revert-unknown.lf", 455, "Unknown identifier `foo`", ""),
         (D + "w-clear-order.lf", 442, "Tactic `clear` failed: target depends on 'a'",
          "\na b : Nat\n⊢ a = a"),
         (D + "w-rename-many.lf", 211, "too many variable names provided", ""),
         (D + "w-intro-many.lf", 94, "Tactic `introN` failed: There are no additional binders"
          " or `let` bindings in the goal to introduce", "\na b : Nat\nx : a = b\n⊢ a = b")]
UNSUPPORTED = [(D + "x-arg-hole.lf", 99, "not supported yet: this case of the tactic"),
               (D + "x-named-twice.lf", 139, "not supported yet"),
               (D + "x-apply-open.lf", 99, "not supported yet: this case of the tactic"),
               (D + "x-intro-rfl.lf", 99, "not supported yet: this case of the tactic"),
               (D + "x-have-synth.lf", 93, "not supported yet")]

if __name__ == "__main__":
    tactic_check.main("batch-e", FILES, WRONG, UNSUPPORTED, env=ENV, lean=D + "batch-e.lean",
                      lean_wrong=D + "batch-e-wrong.lean", golden=ROOT / D / "batch-e.golden")

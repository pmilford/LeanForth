#!/usr/bin/env python3
"""Tactic batch 2a end to end against pinned Lean (plan row TB2: by-have:, by-have,
by-have-goal:, by-let:, by-suffices:, by-replace:; src/front/tactics/have.fs and replace.fs,
their goal operations in src/front/meta-tactic/assert.fs): the harness and its usage are
tests/front/tactics/tactic_check.py's, against decide's slice of Init (tests/front/
decide-slice.ndjson, as batch-a's), with this batch's own Lean twins (batch-b.lean,
batch-b-wrong.lean: Mathlib's valueless have copied as have_goal) and golden (batch-b.golden).
Lean's letE is (let T V B), (let-nd T V B) for a have, on both sides."""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tests/front/tactics"))
import tactic_check  # noqa: E402

D = "tests/front/tactics/batch-b/"
ENV = tactic_check.Env("tests/front/decide-slice.ndjson", "tests/front/decide-slice.elab.ndjson",
                       "decide-dump")
FILES = [(D + "have.lf", ["hv_named", "hv_this", "hv_type", "hv_case", "hg_goal", "hg_unused"]),
         (D + "let.lf", ["lt_basic", "lt_use", "sf_basic", "sf_shadow", "rp_ge", "rp_new"])]


def mismatch(term, has, want):
    return f"  {term}\nhas type\n  {has}\nbut is expected to have type\n  {want}"


WRONG = [(D + "w-hv.lf", 96, "Type mismatch", mismatch("h", "a ≤ b", "b ≤ a")),
         (D + "w-hv-this.lf", 96, "Type mismatch", mismatch("this", "a ≤ b", "b ≤ a")),
         (D + "w-lt.lf", 96, "Type mismatch",
          "  h\nhas type\n  a ≤ b\nof sort `Prop` but is expected to have type\n  Nat\n"
          "of sort `Type`"),
         (D + "w-sf.lf", 96, "Type mismatch", mismatch("h2", "b ≤ a", "a ≤ b")),
         (D + "w-rp.lf", 96, "Type mismatch", mismatch("h", "a ≤ b", "b ≤ a")),
         (D + "w-hg.lf", 96, "Type mismatch", mismatch("h", "a ≤ b", "b ≤ a"))]
UNSUPPORTED = [(D + "x-hv-hole.lf", 99, "not supported yet: this case of the tactic"),
               (D + "x-hv-mvar.lf", 93, "not supported yet")]

if __name__ == "__main__":
    tactic_check.main("batch-b", FILES, WRONG, UNSUPPORTED, env=ENV, lean=D + "batch-b.lean",
                      lean_wrong=D + "batch-b-wrong.lean", golden=ROOT / D / "batch-b.golden")

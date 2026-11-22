#!/usr/bin/env python3
"""Tactic batch 3a end to end against pinned Lean (plan row TB2: the location at: after
by-rw[ ], by-rewrite[ ], by-rwa[ ], by-change, by-symm and by-delta, and by-rfl's exact
Iff.rfl and its Lean failure on a goal that is no relation; src/front/tactic-syntax.fs,
tactic-core.fs's lf-with-location, src/front/tactics/rewrite.fs, rwa.fs, change.fs, symm.fs,
delta.fs, rfl.fs, their goal operations in src/front/meta-tactic/assert.fs, symm.fs and
goal.fs): the harness and its usage are tests/front/tactics/tactic_check.py's, against
decide's slice of Init (tests/front/decide-slice.ndjson, as batch-a's), with this batch's own
Lean twins (batch-d.lean, batch-d-wrong.lean) and golden (batch-d.golden)."""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tests/front/tactics"))
import tactic_check  # noqa: E402

D = "tests/front/tactics/batch-d/"
ENV = tactic_check.Env("tests/front/decide-slice.ndjson", "tests/front/decide-slice.elab.ndjson",
                       "decide-dump")
FILES = [(D + "rw-at.lf", ["at_hyp", "at_closes", "at_two", "at_goal", "at_rules",
                           "at_turnstile"]),
         (D + "rwa-at.lf", ["rwa_at", "rwa_none", "rwa_legacy", "rwa_le", "rwa_not"]),
         (D + "change-at.lf", ["ch_at", "ch_goal", "sy_at", "sy_at_ne", "rf_iff", "rf_rw_iff",
                                "rf_id", "rf_id_iff"])]


def mismatch(term, has, want):
    return f"  {term}\nhas type\n  {has}\nbut is expected to have type\n  {want}"


NO_REFL = "Hint: Reflexivity tactics can only be used on goals of the form `x ~ x` or `R x x`"
# (215's first line ends, in LeanForth's, with the rule's place: the pattern is matched instead)
WRONG = [(D + "w-at-unknown.lf", 455, "Unknown identifier `foo`", ""),
         (D + "w-rw-at.lf", 215, "  a", "in the target expression\n  c ≤ d"),
         (D + "w-rwa-at.lf", 456, "Type mismatch: The rewritten hypothesis",
          mismatch("k", "¬a ≤ b", "False")),
         (D + "w-delta-at.lf", 448, "Tactic `delta` failed: did not delta reduce [Nat.le] at h2",
          "\na b : Nat\nh2 : a ≤ b\n⊢ a ≤ b"),
         (D + "w-rfl-not.lf", 457,
          "Tactic `rfl` failed: Expected the goal to be a binary relation",
          "\n" + NO_REFL + "\n\na b : Nat\nh : ¬a ≤ b\n⊢ ¬a ≤ b"),
         (D + "w-change-at.lf", 443, "'change' tactic failed, pattern",
          "  b = a\nis not definitionally equal to target\n  a = b"),
         (D + "w-symm-at.lf", 451, "Symmetry lemmas only apply to binary relations, not",
          "  ¬a ≤ b")]
UNSUPPORTED = [(D + "x-at-all.lf", 99, "not supported yet: this case of the tactic"),
               (D + "x-at-const.lf", 99, "not supported yet: this case of the tactic"),
               (D + "x-delta-at.lf", 99, "not supported yet: this case of the tactic"),
               (D + "x-rfl-le.lf", 93, "not supported yet"),
               (D + "x-change-dep.lf", 93, "not supported yet")]

if __name__ == "__main__":
    tactic_check.main("batch-d", FILES, WRONG, UNSUPPORTED, env=ENV, lean=D + "batch-d.lean",
                      lean_wrong=D + "batch-d-wrong.lean", golden=ROOT / D / "batch-d.golden")

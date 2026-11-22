#!/usr/bin/env python3
"""Tactic batch 1 end to end against pinned Lean (plan row TB2: by-change, by-show, by-swap,
by-specialize, by-revert, by-delta, by-contradiction, by-trivial, by-absurd; src/front/tactics/,
their goal operations in src/front/meta-tactic/): the harness and its usage are
tests/front/tactics/tactic_check.py's, against decide's slice of Init (tests/front/
decide-slice.ndjson: Ne, GE.ge, trivial's instances and of_decide_eq_false, which the S2 slice
lacks), with this batch's own Lean twins (batch-a.lean, batch-a-wrong.lean) and golden
(batch-a.golden)."""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tests/front/tactics"))
import tactic_check  # noqa: E402

D = "tests/front/tactics/batch-a/"
ENV = tactic_check.Env("tests/front/decide-slice.ndjson", "tests/front/decide-slice.elab.ndjson",
                       "decide-dump")
FILES = [(D + "change.lf", ["ch_target", "ch_same", "sh_target", "sh_second"]),
         (D + "goals.lf", ["sw_and", "rv_hyp", "rv_dep", "sp_self", "sp_exact", "sp_later",
                           "rv_reuse"]),
         (D + "close.lf", ["de_ge", "cn_false", "cn_not", "cn_ne", "tr_rfl", "tr_and", "tr_decide",
                           "tr_false", "tr_assumption", "ab_neg", "ab_pos"])]
NOT_EQUAL = "is not definitionally equal to target\n  a ≥ b"
WRONG = [(D + "w-ch.lf", 443, "'change' tactic failed, pattern", "  a ≤ b\n" + NOT_EQUAL),
         (D + "w-sh.lf", 444, "'show' tactic failed, pattern", "  a ≤ b\n" + NOT_EQUAL),
         (D + "w-sh-many.lf", 445, "'show' tactic failed, no goals unify with the given pattern.",
          "\nIn the first goal, the pattern\n  a = b\nis not definitionally equal to the target\n"
          "  a ≤ b\n(Errors for other goals omitted)"),
         (D + "w-sh-type.lf", 96, "Type mismatch",
          "  a\nhas type\n  Nat\nbut is expected to have type\n  Prop"),
         (D + "w-sw.lf", 446, "goal index `2` is out of bounds", ""),
         (D + "w-sp.lf", 447, "'specialize' requires a term of the form `h x_1 .. x_n` where `h` "
          "appears in the local context", ""),
         (D + "w-sp-exact.lf", 96, "Type mismatch",
          "  h2\nhas type\n  b ≤ a\nbut is expected to have type\n  a ≤ b"),
         (D + "w-rv.lf", 389, "Unexpected term `Nat.le_refl`; expected single reference to variable",
          ""),
         (D + "w-de.lf", 448, "Tactic `delta` failed: did not delta reduce [Ne]",
          "\na b : Nat\nh : b ≤ a\n⊢ a ≥ b"),
         (D + "w-cn.lf", 449, "Tactic `contradiction` failed", "\na b : Nat\nh : a = b\n⊢ b = a"),
         (D + "w-tr.lf", 381, "Tactic `assumption` failed", "\na b : Nat\nh : a = b\n⊢ b = a"),
         (D + "w-ab.lf", 381, "Tactic `assumption` failed", "\na b : Nat\nh h2 : a ≤ b\n⊢ ¬a ≤ b")]
NOT_YET = "not supported yet: this case of the tactic"
UNSUPPORTED = [(D + "x-cn-le.lf", 99, NOT_YET), (D + "x-cn-ctor.lf", 99, NOT_YET),
               (D + "x-tr-le.lf", 99, NOT_YET),
               (D + "x-sp-not.lf", 136, "a binder whose kind the declaration's type does not give")]

if __name__ == "__main__":
    tactic_check.main("batch-a", FILES, WRONG, UNSUPPORTED, env=ENV, lean=D + "batch-a.lean",
                      lean_wrong=D + "batch-a-wrong.lean", golden=ROOT / D / "batch-a.golden")

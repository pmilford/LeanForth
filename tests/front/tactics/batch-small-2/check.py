#!/usr/bin/env python3
"""Small tactics 2, end to end against pinned Lean (plan row 9.4.8z12): by-calc[ ]
(src/front/tactics/calc.fs over src/front/elab-calc.fs). The harness and its usage are
tests/front/tactics/tactic_check.py's, against the patterns slice of Init
(tests/front/patterns-slice.ndjson, which holds Trans.trans and the Trans instances of Eq and
of Nat's <= and <, tests/front/patterns-slice.roots), with this batch's own Lean twins
(batch-small-2.lean, batch-small-2-wrong.lean) and golden (batch-small-2.golden).

w-calc-trans.lf compares Lean's first line only: the type sought holds a metavariable, which
Lean and LeanForth name differently. UNSUPPORTED are the texts LeanForth answers not supported
yet for (exit 2): u-calc-target.lf (throwCalcFailure, after a coercion) and u-calc-hole.lf (a
step _ alone), which Lean rejects too; u-calc-odd.lf (a first step written alone), which has
no Lean twin."""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tests/front/tactics"))
import tactic_check  # noqa: E402

D = "tests/front/tactics/batch-small-2/"
ENV = tactic_check.Env("tests/front/patterns-slice.ndjson",
                       "tests/front/patterns-slice.elab.ndjson", "patterns-dump")
FILES = [(D + "calc.lf", ["cc_eq", "cc_explicit", "cc_one", "cc_le", "cc_lt", "cc_mix",
                          "cc_ltle", "cc_leeq", "cc_ext", "cc_ext_lt", "cc_hole", "cc_holes",
                          "cc_num", "cc_order"]),
         (D + "with-reducible.lf", ["wr_ok", "wr_inst", "wr_all", "wr_exact_dflt", "wr_try",
                                    "wr_all_exact", "wr_two", "wr_have"])]

UNSOLVED_IFF = "a b : Nat\nh : a = b\n⊢ "
WRONG = [(D + "w-calc-lhs.lf", 513, "invalid 'calc' step, left-hand side is",
          "  a : Nat\nbut previous right-hand side is\n  b : Nat"),
         (D + "w-calc-trans.lf", 510,
          "invalid 'calc' step, failed to synthesize `Trans` instance", ""),
         (D + "w-calc-relation.lf", 512, "invalid 'calc' step, relation expected", "  True"),
         (D + "w-calc-order.lf", 96, "Type mismatch", "  h2\nhas type\n  c = c"),
         (D + "w-calc-tagged.lf", 96, "Type mismatch", "  h1\nhas type\n  a = b"),
         (D + "w-calc-natural.lf", 461, "don't know how to synthesize placeholder",
          "context:\na b c : Nat\nh1 : a = b\nh2 : b = c\n⊢ a = b"),
         (D + "w-rw-iff.lf", 89, "unsolved goals", UNSOLVED_IFF),
         (D + "w-rw-all.lf", 89, "unsolved goals", UNSOLVED_IFF),
         (D + "w-wr-rfl.lf", 97, "Tactic `rfl` failed: The left-hand side", "  a + 0"),
         (D + "w-wr-exact.lf", 96, "Type mismatch", "  h")]
NOT_YET = "not supported yet"
UNSUPPORTED = [(D + "u-calc-target.lf", 131, NOT_YET), (D + "u-calc-odd.lf", 99, NOT_YET),
               (D + "u-calc-hole.lf", 99, NOT_YET), (D + "u-wr-inst.lf", 139, NOT_YET)]

if __name__ == "__main__":
    tactic_check.main("batch-small-2", FILES, WRONG, UNSUPPORTED, env=ENV,
                      lean=D + "batch-small-2.lean", lean_wrong=D + "batch-small-2-wrong.lean",
                      golden=ROOT / D / "batch-small-2.golden")

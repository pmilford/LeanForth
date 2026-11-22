#!/usr/bin/env python3
"""Tactic batch 2b end to end against pinned Lean (plan row TB2: <- in by-rw[ ] and
by-rewrite[ ], by-rwa[, by-exacts[, by-cases:, by-contra:, by-contra, by-contra-core, by-symm,
by-and-intros, by-next and by-case: _; src/front/tactics/rwa.fs, exacts.fs, by-cases.fs,
by-contra.fs, symm.fs, and-intros.fs, case.fs, their goal operations in src/front/meta-tactic/
rewrite.fs, by-cases.fs, symm.fs and repeat.fs): the harness and its usage are
tests/front/tactics/tactic_check.py's, against decide's slice of Init (tests/front/
decide-slice.ndjson, as batch-a's), with this batch's own Lean twins (batch-c.lean,
batch-c-wrong.lean: Batteries' exacts, by_contra and absurd copied) and golden (batch-c.golden).
A theorem over Classical.propDecidable or Classical.byContradiction names its axioms."""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tests/front/tactics"))
import tactic_check  # noqa: E402

D = "tests/front/tactics/batch-c/"
ENV = tactic_check.Env("tests/front/decide-slice.ndjson", "tests/front/decide-slice.elab.ndjson",
                       "decide-dump")
CLASSICAL = "=propext, Classical.choice, Quot.sound"
FILES = [(D + "rw.lf", ["rs_hyp", "rs_lemma", "rs_two", "rs_rewrite"]),
         (D + "rwa.lf", ["ra_basic", "ra_rfl", "ra_symm", "ra_focus"]),
         (D + "exacts.lf", ["ex_two", "ex_none", "ex_app"]),
         (D + "cases.lf", ["bc_dec", "bc_tags", "bc_classical" + CLASSICAL]),
         (D + "contra.lf", ["bk_not", "bk_dec", "bk_classical" + CLASSICAL, "bk_ne"]),
         (D + "symm.lf", ["sy_eq", "sy_iff", "sy_ne", "sy_and", "sy_heq"]),
         (D + "intros.lf", ["ai_two", "ai_nested", "ai_all", "nx_basic", "nx_name"]),
         (D + "x-ra-le.lf", ["x_ra_le"])]


def mismatch(term, has, want):
    return f"  {term}\nhas type\n  {has}\nbut is expected to have type\n  {want}"


# (215's first line ends, in LeanForth's, with the rule's place: the pattern is matched instead)
WRONG = [(D + "w-rs.lf", 215, "  b", "in the target expression\n  a + 0 = a"),
         (D + "w-ra.lf", 381, "Tactic `assumption` failed",
          "\na b c : Nat\nh : a = b\nh2 : c = b\n⊢ b = c"),
         (D + "w-ex.lf", 89, "unsolved goals", "case right\na b : Nat"),
         (D + "w-ex-type.lf", 96, "Type mismatch", mismatch("h2", "b ≤ a", "a ≤ b")),
         (D + "w-bc.lf", 96, "Type mismatch", mismatch("h1", "b ≤ a", "a ≤ b")),
         (D + "w-bk.lf", 96, "Type mismatch", mismatch("h", "a ≤ b", "False")),
         (D + "w-sy.lf", 451, "Symmetry lemmas only apply to binary relations, not", "  ¬a ≤ b"),
         (D + "w-ai.lf", 96, "Type mismatch", mismatch("h2", "b ≤ a", "a ≤ b")),
         (D + "w-nx.lf", 96, "Type mismatch", mismatch("h2", "b ≤ a", "a ≤ b"))]
UNSUPPORTED = [(D + "x-rs-iff.lf", 99, "not supported yet: this case of the tactic"),
               (D + "x-bc-type.lf", 99, "not supported yet: this case of the tactic"),
               (D + "x-sy-le.lf", 99, "not supported yet: this case of the tactic")]

if __name__ == "__main__":
    tactic_check.main("batch-c", FILES, WRONG, UNSUPPORTED, env=ENV, lean=D + "batch-c.lean",
                      lean_wrong=D + "batch-c-wrong.lean", golden=ROOT / D / "batch-c.golden")

#!/usr/bin/env python3
"""by-simp with Lean's default simp set, end to end against pinned Lean (plan row FE9, simp
group 4, pass 1: src/front/tactics/simp.fs on src/front/simp/default-set.fs). The harness and
its usage are tests/front/tactics/tactic_check.py's, against simp's slice of Init
(tests/front/simp-slice.ndjson and its format-4.1 elaboration data, which holds the default
set), with this group's own Lean twins (simp-4.lean, simp-4-wrong.lean) and golden
(simp-4.golden). The goals meet no simproc candidate, no lemma the slice lacks and no
conditional lemma; the two not supported yet meet a left-out lemma and a simproc."""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tests/front/tactics"))
import tactic_check  # noqa: E402

D = "tests/front/tactics/simp-4/"
ENV = tactic_check.Env("tests/front/simp-slice.ndjson", "tests/front/simp-slice.elab.ndjson",
                       "simp-dump")
FILES = [(D + "simp-4.lf", ["simp_true", "simp_true_and=propext", "simp_add_zero=propext",
                            "simp_or_true=propext", "simp_not_not=propext",
                            "simp_mul_one=propext"]),
         (D + "simprocs.lf", ["simp_ite_true=propext", "simp_ite_false=propext",
                               "simp_add_lits=propext", "simp_mul_add=propext"]),
         (D + "brackets.lf", ["simp_br_hyp=propext", "simp_br_rev=propext", "simp_br_const=propext",
                              "simp_at_hyp=propext", "simp_at_both=propext", "simp_at_all=propext",
                              "simp_at_false=propext", "simp_br_at=propext"])]
WRONG = [(D + "w-no-progress.lf", 500, "`simp` made no progress", ""),
         (D + "w-ite-other.lf", 89, "unsolved goals", "⊢ False"),
         (D + "w-at-no-progress.lf", 500, "`simp` made no progress", "")]
NOT_YET = "not supported yet: this case of the tactic"
UNSUPPORTED = [(D + "u-left-out.lf", 99, NOT_YET), (D + "u-simproc.lf", 99, NOT_YET),
               (D + "u-ctor-eq.lf", 99, NOT_YET), (D + "u-rev-const.lf", 99, NOT_YET)]

if __name__ == "__main__":
    tactic_check.main("simp-4", FILES, WRONG, UNSUPPORTED, env=ENV, lean=D + "simp-4.lean",
                      lean_wrong=D + "simp-4-wrong.lean", golden=ROOT / D / "simp-4.golden")

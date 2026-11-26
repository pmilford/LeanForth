#!/usr/bin/env python3
"""Small tactics 1, end to end against pinned Lean (plan row TB2): by-funext and by-funext[ ]
(src/front/tactics/funext.fs over meta-tactic/apply.fs's lf-goal-apply-const),
by-infer-instance (tactics/infer-instance.fs), by-rename: (tactics/rename.fs), by-generalize:
and by-generalize-eq: with at[ ] (tactics/generalize.fs over meta-tactic/generalize.fs's
lf-goal-generalize-eq and lf-goal-generalize-hyp), by-skip and by-done (tactics/skip.fs,
done.fs). The harness and its usage are tests/front/tactics/tactic_check.py's, against
decide's slice of Init (tests/front/decide-slice.ndjson, which holds funext, inferInstance and
the instances used), with this batch's own Lean twins (batch-small-1.lean,
batch-small-1-wrong.lean) and golden (batch-small-1.golden).

Two wrong twins compare Lean's first line only: LeanForth prints the class of w-ii-none.lf as
`@IntCast Nat` where Lean prints `IntCast Nat`, and gives 110 no detail where Lean shows the
goal's type (w-ii-class.lf). OWN is w-funext.lf, where Lean names the constant `@funext` and
LeanForth `funext` (no @ before a bare constant), so --lean does not ask Lean for its text.
UNSUPPORTED are the texts LeanForth answers not supported yet for (exit 2): u-gen-type.lf and
u-ii-left-out.lf, which Lean rejects too; u-gen-star.lf (at *) and u-funext-add.lf (a
function of two arguments), which Lean accepts; u-gen-blank.lf and u-rename-blank.lf, whose _
Lean's parser refuses."""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tests/front/tactics"))
import tactic_check  # noqa: E402

D = "tests/front/tactics/batch-small-1/"
ENV = tactic_check.Env("tests/front/decide-slice.ndjson", "tests/front/decide-slice.elab.ndjson",
                       "decide-dump")
FUNEXT = "=Quot.sound"   # funext is proved by Quot.sound
FILES = [(D + "funext.lf", ["fx_one" + FUNEXT, "fx_plain" + FUNEXT, "fx_none",
                            "fx_blank" + FUNEXT]),
         (D + "infer.lf", ["ii_sub", "ii_have", "ii_and"]),
         (D + "rename.lf", ["rn_one", "rn_newest", "rn_hole", "rn_defeq"]),
         (D + "generalize.lf", ["gz_one", "gz_eq", "gz_eq_used", "gz_at", "gz_at_eq",
                                "gz_at_skip", "gz_absent"]),
         (D + "skip-done.lf", ["sk_one", "sk_after", "dn_try"])]

WRONG = [(D + "w-done.lf", 89, "unsolved goals", "a b : Nat\nh : a = b\n⊢ a = b"),
         (D + "w-rename.lf", 482, "Failed to find a hypothesis with type", "  b = a"),
         (D + "w-ii-none.lf", 125, "failed to synthesize instance of type class", ""),
         (D + "w-ii-class.lf", 110, "type class instance expected", "")]
OWN = [(D + "w-funext.lf", 380, "Tactic `apply` failed: could not unify the conclusion of `funext`",
        "  ?f = ?g\nwith the goal\n  a + 0 = a")]
NOT_YET = "not supported yet"
UNSUPPORTED = [(D + "u-gen-type.lf", 99, NOT_YET), (D + "u-gen-star.lf", 99, NOT_YET),
               (D + "u-gen-blank.lf", 99, NOT_YET), (D + "u-rename-blank.lf", 99, NOT_YET),
               (D + "u-funext-add.lf", 93, NOT_YET), (D + "u-ii-left-out.lf", 119, NOT_YET)]

if __name__ == "__main__":
    wrong = WRONG if "--lean" in sys.argv else WRONG + OWN
    tactic_check.main("batch-small-1", FILES, wrong, UNSUPPORTED, env=ENV,
                      lean=D + "batch-small-1.lean", lean_wrong=D + "batch-small-1-wrong.lean",
                      golden=ROOT / D / "batch-small-1.golden")

#!/usr/bin/env python3
"""by-apply end to end against pinned Lean (slice a2-iii;
src/front/tactics/apply.fs, src/front/meta-tactic/apply.fs): the
harness and its usage are tests/front/tactics/tactic_check.py's."""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tests/front/tactics"))
import tactic_check  # noqa: E402

D = "tests/front/tactics/apply/"
FILES = [(D + "ap-le-succ.lf", ["ap_le_succ"]), (D + "ap-le-trans.lf", ["ap_le_trans"]),
         (D + "ap-hyp.lf", ["ap_hyp"]), (D + "ap-partial.lf", ["ap_partial"]),
         (D + "ap-and.lf", ["ap_and"]), (D + "ap-tag.lf", ["ap_tag"]),
         (D + "ap-tag-trans.lf", ["ap_tag_trans"]), (D + "ap-exact.lf", ["ap_exact"])]
# Lean's first line and the detail after it (Lean's note prints the full
# type as `∀ (n : Nat), n ≤ n.succ`, LeanForth's printer as an arrow: plan 8.6).
WRONG = [(D + "w-ap-le-succ.lf", 380,
          "Tactic `apply` failed: could not unify the conclusion of `Nat.le_succ`",
          "  ?n ≤ Nat.succ ?n\nwith the goal\n  n + 1 ≤ n\n\nNote: The full type of "
          "`Nat.le_succ` is"),
         (D + "w-ap-hyp.lf", 380, "Tactic `apply` failed: could not unify the type of `h`",
          "  a ≤ b\nwith the goal\n  b ≤ a\n\na b : Nat\nh : a ≤ b\n⊢ b ≤ a"),
         # exact on apply's goal ?m ≤ ?k, both assigned (plan 9.4.8l J)
         (D + "w-ap-exact.lf", 96, "Type mismatch",
          "  h1\nhas type\n  a ≤ b\nbut is expected to have type\n  b ≤ c")]
UNSUPPORTED = []

if __name__ == "__main__":
    tactic_check.main("apply", FILES, WRONG, UNSUPPORTED)

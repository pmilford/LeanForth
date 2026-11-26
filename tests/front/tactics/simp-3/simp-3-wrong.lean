-- Pinned Lean's errors for the wrong twins of tests/front/tactics/simp-3/w-*.lf (plan row
-- FE9, simp group 3): tactic_check.py --lean checks that each message the LeanForth file must
-- print is Lean's.
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem w_binder_skipped (a : Nat) : a + 0 = a := by
  revert a
  simp only [Nat.add_zero]
  intro a
  exact Nat.add_zero a
theorem w_binder_no_progress (b c d : Nat) (h : c = d) (a : Nat) : a + 1 = b := by
  revert a
  simp only [h]

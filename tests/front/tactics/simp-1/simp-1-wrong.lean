-- Pinned Lean's errors for the wrong twins of tests/front/tactics/simp-1/w-*.lf (plan row
-- FE9, simp slice SL1a-1): tactic_check.py --lean checks that each message the LeanForth
-- file must print is Lean's.
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem w_no_progress (n : Nat) : n = n + 1 := by
  simp only []
theorem w_head_only (a c : Nat) (h : a * 7 = c) : a * 6 = c := by
  simp only [h]
theorem w_unused_rule_closes (a b : Nat) (h : a = 0) : b = b := by
  simp only [h]
  exact h

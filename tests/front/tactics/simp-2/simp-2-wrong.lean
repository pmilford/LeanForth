-- Pinned Lean's errors for the wrong twins of tests/front/tactics/simp-2/w-*.lf (plan row
-- FE9, simp slice SL1a-2 and plan row 9.4.8z2(e)): tactic_check.py --lean checks that each
-- message the LeanForth file must print is Lean's.
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem w_at_self (a b : Nat) (h : a = b) : a = b := by
  simp only [h] at h
  exact h
theorem w_at_no_progress (a b : Nat) (h : a = b) : a = b := by
  simp only [] at h
theorem w_at_two_no_progress (a b : Nat) (h : a = b) (k : b = a) : a = b := by
  simp only [Nat.add_zero] at h k
theorem w_arg_var (a : Nat) : a = a := by
  simp only [a]
theorem w_symm_prop (a b : Nat) (h : a ≤ b) : a ≤ b := by
  simp only [← h]
theorem w_symm_not (a b : Nat) (h : ¬ a ≤ b) : (a ≤ b) = False := by
  simp only [← h]
theorem w_symm_ne (a b : Nat) (h : a ≠ b) : (a = b) = False := by
  simp only [← h]
theorem w_and_order (a b c d : Nat) (h : a = b ∧ a = c) (k : c = d) : a = d := by
  simp only [h]
  exact k

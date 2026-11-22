-- Pinned Lean's errors for the wrong twins of tests/front/tactics/batch-d/w-*.lf (plan row
-- TB2, tactic batch 3a): tactic_check.py --lean checks that each message the LeanForth file
-- must print is Lean's.
import Lean
set_option linter.unusedVariables false

theorem w_at_unknown (a b c : Nat) (h : a = b) (h2 : a ≤ c) : b ≤ c := by
  rw [h] at foo
theorem w_rw_at (a b c d : Nat) (h : a = b) (h2 : c ≤ d) : c ≤ d := by
  rw [h] at h2
theorem w_rwa_at (a b : Nat) (k : ¬a ≤ b) : False := by
  rwa [] at k
theorem w_delta_at (a b : Nat) (h2 : a ≤ b) : a ≤ b := by
  delta Nat.le at h2
  exact h2
theorem w_rfl_not (a b : Nat) (h : ¬a ≤ b) : ¬a ≤ b := by
  rfl
theorem w_change_at (a b : Nat) (h : a = b) : a = b := by
  change b = a at h
theorem w_symm_at (a b : Nat) (h : ¬a ≤ b) : ¬a ≤ b := by
  symm at h

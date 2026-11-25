-- Pinned Lean's errors for the wrong twins of tests/front/tactics/blocks-3/w-*.lf (plan row
-- TB2, blocks slice 3): tactic_check.py --lean checks that each message the LeanForth file
-- must print is Lean's. The u_* theorems are the u-*.lf texts LeanForth answers 490
-- (unsupported) for: Lean rejects each, with the error it logged.
import Lean
set_option linter.unusedVariables false

theorem w_try_open (a b : Nat) (h : a = b) (k : b = a) : a = b := by
  try exact k
theorem w_first_all (a b : Nat) (h : a = b) (k : b = a) : a = b := by
  first
  | rfl
  | exact k
theorem w_any_all (a b : Nat) (h : a = b) : b = a ∧ b = a := by
  constructor
  any_goals exact h
theorem w_any_none (a b : Nat) (h : a = b) : a = b := by
  exact h
  any_goals exact h
theorem u_any_term (a b : Nat) (h : a = b) : a = b := by
  any_goals exact ⟨h⟩
theorem u_any_brace (a b : Nat) (h : a = b) (k : b = a) : a = b := by
  any_goals (· exact k)

-- Pinned Lean's errors for the wrong twins of tests/front/tactics/blocks-2/w-*.lf (plan row
-- TB2, blocks slice 2): tactic_check.py --lean checks that each message the LeanForth file
-- must print is Lean's.
import Lean
set_option linter.unusedVariables false

theorem w_ag_second (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a ∧ a = b := by
  and_intros
  all_goals exact h
theorem w_then_second (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a ∧ a = b := by
  and_intros <;> exact h
theorem w_then_open (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  constructor <;> have x : a = b := h
theorem w_then_name (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  constructor
  have x : a = b := h <;> exact x
  exact x

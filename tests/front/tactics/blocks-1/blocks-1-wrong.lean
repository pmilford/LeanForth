-- Pinned Lean's errors for the wrong twins of tests/front/tactics/blocks-1/w-*.lf (plan row
-- TB2, blocks slice 1): tactic_check.py --lean checks that each message the LeanForth file
-- must print is Lean's.
import Lean
set_option linter.unusedVariables false

theorem w_brace_open (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  constructor
  · exact h
  · have x : b = a := k
theorem w_brace_empty (a b : Nat) (h : a = b) : a = b := by
  { }
theorem w_brace_none (a b : Nat) (h : a = b) : a = b := by
  exact h
  { exact h }
theorem w_have_by_open (a b : Nat) (h : a = b) : b = a := by
  have k : b = a := by
    have x : a = b := h
  exact k
theorem w_focus_none (a b : Nat) (h : a = b) : a = b := by
  exact h
  focus
    exact h
theorem w_focus_open (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  constructor
  focus
    have x : a = b := h

-- Pinned Lean's errors for the wrong twins of tests/front/tactics/batch-g/w-*.lf (plan row
-- TB2, piece E, slice E1): tactic_check.py --lean checks that each message the LeanForth file
-- must print is Lean's.
import Lean
set_option linter.unusedVariables false

theorem w_tag_intro (a b : Nat) (h : a = b ∧ b = a) : b = a := by
  obtain ⟨hab, hba⟩ := h
  case intro => exact hba
theorem w_hidden_extra (a b c : Nat) (right : c = c) (h : a = b ∧ b = a) : b = a := by
  obtain ⟨hab, _⟩ := h
  rcases b with _ | d
  exact right
  exact right
theorem w_clear_used (a b : Nat) (h : a = b) : a = b := by
  rcases h with -
  exact h
theorem w_order (a b : Nat) (h : a = b ∨ b = a) : b = a ∨ a = b := by
  rcases h with h1 | h2
  exact Or.inl h2
  exact Or.inr h1

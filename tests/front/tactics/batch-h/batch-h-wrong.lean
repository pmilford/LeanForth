-- Pinned Lean's errors for the wrong twins of tests/front/tactics/batch-h/w-*.lf (plan row
-- TB2, piece E, slice E2a): tactic_check.py --lean checks that each message the LeanForth file
-- must print is Lean's.
import Lean
set_option linter.unusedVariables false

theorem w_hidden_subst (a b c : Nat) (right : c = c) (h : a = b ∧ b = a) : b = a := by
  obtain ⟨hab, _⟩ := h
  subst hab
  exact right
theorem w_hidden_reduced (a b c : Nat) (right : c = c) (h : a = id b ∧ b = a) : b = a := by
  obtain ⟨hab, _⟩ := h
  subst hab
  exact right
theorem w_hidden_heq (a b c : Nat) (right : c = c) (h : HEq a b ∧ b = a) : b = a := by
  obtain ⟨hab, _⟩ := h
  subst hab
  exact right
theorem w_rintro_group (a b : Nat) (h : a = b ∨ (b = a ∧ a = a)) (k : b = a) : b = a := by
  revert h k
  rintro (x | y) z
  intro d
  exact d
  intro d
  exact d
theorem w_occurs (a : Nat) (h : a = a) : True := by
  subst h
theorem w_no_equation (a : Nat) : a = a := by
  subst a
theorem w_rfl_not_eq (a b : Nat) (h : a = b ∧ True) : b = a := by
  obtain ⟨-, rfl⟩ := h
theorem w_sides (h : Nat.zero = Nat.zero) : False := by
  subst h
theorem w_subst_var_used (a b : Nat) (h : a = b) : b = a := by
  subst h
  exact Eq.refl b
theorem x_have (a b : Nat) (h : a = b) : b = a := by
  have k : a = b := h
  subst k
  rfl

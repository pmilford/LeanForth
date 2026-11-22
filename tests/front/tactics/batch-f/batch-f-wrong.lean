-- Pinned Lean's errors for the wrong twins of tests/front/tactics/batch-f/w-*.lf (plan row
-- TB2, tactic batch 3c): tactic_check.py --lean checks that each message the LeanForth file
-- must print is Lean's.
import Lean
set_option linter.unusedVariables false

theorem w_anon_few (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  exact ⟨h⟩
theorem w_anon_fields (a b : Nat) (h : a = b) : a = b := by
  exact ⟨h⟩
theorem w_anon_nested (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  exact ⟨h, k, h⟩
theorem w_anon_ctors (a b : Nat) (h : a = b) : a = b ∨ b = a := by
  exact ⟨h⟩
theorem w_anon_none (a b : Nat) (h : a = b) : False := by
  exact ⟨h⟩
theorem w_anon_type (a b : Nat) (h : a = b) : a = b := by
  have x : Prop := ⟨h⟩
  exact h
theorem w_anon_unknown (a b : Nat) (h : a = b) : a = b := by
  have := ⟨h, h⟩
  exact h
theorem w_exists_many (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  exists h, k
theorem w_exists_open (a b : Nat) (h : a = b) : Exists (Eq b) := by
  exists a

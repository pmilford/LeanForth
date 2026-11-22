-- Pinned Lean's errors for the wrong twins of tests/front/tactics/batch-e/w-*.lf (plan row
-- TB2, tactic batch 3b): tactic_check.py --lean checks that each message the LeanForth file
-- must print is Lean's.
import Lean
set_option linter.unusedVariables false

theorem w_refine_hole (a b : Nat) (h : a = b) : a = b := by
  refine _
theorem w_exact_hole (a b : Nat) (h : a = b) : a = b := by
  exact _
theorem w_exact_synth (a b : Nat) (h : a = b) : a = b := by
  exact ?_
theorem w_revert_unknown (a b : Nat) (h : a = b) : a = b := by
  revert h foo
theorem w_clear_order (a b : Nat) (h : a = b) : a = a := by
  clear a h
theorem w_rename_many (a b : Nat) (h : a = b) : a = b := by
  revert h
  intro _
  rename_i x y
theorem w_intro_many (a b : Nat) (h : a = b) : a = b := by
  revert h
  intro x y

-- Pinned Lean's errors for the wrong twins of tests/front/tactics/batch-small-1b/w-*.lf (plan
-- row TB2, small tactics 1: iterate): tactic_check.py --lean checks that each message the
-- LeanForth file must print is Lean's.
set_option linter.unusedVariables false

theorem w_it_more (a b : Nat) (h : a = b) : a = b := by
  iterate 2 exact h
theorem w_it_ctor (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  iterate 3 constructor
theorem w_it_short (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  iterate 1 constructor
  exact h

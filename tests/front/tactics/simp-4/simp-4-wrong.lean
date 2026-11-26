-- Pinned Lean's errors for the wrong twins of tests/front/tactics/simp-4/w-*.lf (plan row
-- FE9, simp group 4): tactic_check.py --lean checks that each message the LeanForth file must
-- print is Lean's.
set_option linter.unusedVariables false

theorem w_no_progress : False := by simp
theorem w_ite_other : if False then True else False := by simp

-- Pinned Lean's errors for the wrong twins of tests/front/tactics/batch-small-1/w-*.lf (plan
-- row TB2, small tactics 1): tactic_check.py --lean checks that each message the LeanForth
-- file must print is Lean's. w_funext is LeanForth's own (check.py's OWN: Lean prints
-- `@funext`, LeanForth `funext`). The u_* theorems are u-*.lf texts LeanForth answers not
-- supported yet for, which Lean rejects too (u_gen_type: not type correct; u_ii_left_out: no
-- instance); Lean accepts u_gen_star and u_funext_add, and refuses u_gen_blank and
-- u_rename_blank in its parser, so they are not here.
set_option linter.unusedVariables false

theorem w_done (a b : Nat) (h : a = b) : a = b := by
  done
theorem w_rename (a b : Nat) (h : a = b) : a = b := by
  rename b = a => k
theorem w_ii_none (a b : Nat) (h : a = b) : a = b := by
  have d : IntCast Nat := by infer_instance
  exact h
theorem w_ii_class (a b : Nat) (h : a = b) : a = b := by
  infer_instance
theorem w_funext (a : Nat) : a + 0 = a := by
  funext y
theorem u_gen_type (a b : Nat) : decide (a = b) = decide (a = b) := by
  generalize (a = b) = x
theorem u_ii_left_out (a b : Nat) (h : a = b) : a = b := by
  have d : Inhabited False := by infer_instance
  exact h

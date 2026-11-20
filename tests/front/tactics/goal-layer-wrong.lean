-- Pinned Lean's errors for the wrong twins of tests/front/tactics/*/w-*.lf
-- (slice a2-iii): tests/front/tactics/tactic_check.py --lean checks that
-- each message the LeanForth file must print is Lean's.
theorem w_ap_le_succ (n : Nat) : n + 1 ≤ n := by apply Nat.le_succ
theorem w_ap_hyp (a b : Nat) (h : a ≤ b) : b ≤ a := by apply h
theorem w_ap_exact (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  apply Nat.le_trans
  apply h1
  exact h1
theorem w_as (a b : Nat) (h : a ≤ b) : b ≤ a := by assumption
theorem w_co_false : False := by constructor
theorem w_co_not (a b : Nat) : ¬ a = b := by constructor
-- Plan row TB1: left, right, exfalso, intros and clear.
theorem w_le_and (a b : Nat) : a ≤ b ∧ b ≤ a := by left
theorem w_le_not (a b : Nat) : ¬ a = b := by left
theorem w_le_le (a b : Nat) : a ≤ b := by left
theorem w_ri_not (a b : Nat) : ¬ a = b := by right
theorem w_ri_and (a b : Nat) : a ≤ b ∧ b ≤ a := by right
theorem w_ex_exact (a b : Nat) (h : a ≤ b) : a = b := by
  exfalso
  exact h
theorem w_is_not (a b : Nat) : ¬ a = b := by
  intros
  assumption
theorem w_cl_dep (a : Nat) (h : a ≤ a) : a ≤ a := by clear a
theorem w_cl_target (a : Nat) : a ≤ a := by clear a
theorem w_cl_const (a : Nat) (h : a ≤ a) : a ≤ a := by clear Nat.le_refl
-- Plan row S3, slice S3a: decide.
theorem w_dc_add : 2 + 2 = 5 := by decide
theorem w_dc_lt : ¬ (10 < 20) := by decide
theorem w_dc_and : 3 ≤ 3 ∧ 2 + 2 = 5 := by decide
theorem w_dc_fvar (n : Nat) : n + 1 = n := by decide
theorem w_dc_fvar0 (n : Nat) : n + 0 = n := by decide
theorem w_dc_nonempty : Nonempty Nat := by decide
theorem w_dc_choice : Classical.choice (Nonempty.intro 0) = 0 := by decide
theorem w_dc_choice_bool : Classical.choice (Nonempty.intro true) = true := by decide
-- Plan row S3, slice S3a-ops C1: Lean's operators.
theorem w_dc_mul : 6 * 7 = 43 := by decide
theorem w_dc_gt : 10 > 20 := by decide
theorem w_dc_ne : 3 ≠ 3 := by decide
theorem w_dc_ge : 10 ≥ 11 := by decide
theorem w_dc_euler : 2 ^ 32 + 1 = 641 * 6700419 := by decide
theorem w_dc_divmod : 17 / 5 = 3 ∧ 17 % 5 = 3 := by decide
theorem w_dc_none : True := by
  decide
  decide

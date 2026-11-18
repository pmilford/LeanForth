-- Wrong proofs for S2's tactics (tests/front/check_s2.py): each must
-- fail at the step pinned Lean fails at, with Lean's first message,
-- which the LeanForth twins in tests/front/s2-wrong-*.lf must print.
theorem w_pattern (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.mul_succ]
theorem w_alt_name (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | suc k ih => rw [Nat.add_succ, ih]
theorem w_alt_missing (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
theorem w_alt_twice (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]
theorem w_alt_names (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih x => rw [Nat.add_succ, ih]
theorem w_not_eq (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [k]
theorem w_rw_unsolved (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ]
theorem w_not_inductive (f : Nat → Nat) : f = f := by
  induction f with
  | zero => rfl
theorem w_mvar_pattern (n : Nat) (h : ∀ x : Nat, x = 0 + x) : n = 0 + n := by
  rw [h]
theorem w_induction_plain (n : Nat) : 0 + n = n := by
  induction n
theorem w_rw_empty (n : Nat) : 0 + n = n := by
  rw []
theorem w_add_zero_rfl (n : Nat) : n + 0 = n + 1 := by rfl
theorem w_add_zero (n : Nat) : n + 0 = n + 1 := Eq.refl n

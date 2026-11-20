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
theorem w_case_tag (n : Nat) : 0 + n = n := by
  induction n
  case zero => rfl
  case suc k ih => exact congrArg Nat.succ ih
theorem w_case_tags (n : Nat) : 0 + n = n := by
  induction n
  case suc k ih => exact congrArg Nat.succ ih
theorem w_case_none (n : Nat) : 0 + n = n := by
  case zero => rfl
theorem w_case_names (n : Nat) : 0 + n = n := by
  induction n
  case zero => rfl
  case succ k ih extra => exact congrArg Nat.succ ih
theorem w_case_unsolved (n : Nat) : 0 + n = n := by
  induction n
  case zero => rfl
  case succ k ih => rw [Nat.add_succ]
theorem w_case_suffix (n m : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    induction m
    case foo.zero => rw [Nat.add_succ, ih]
    case succ j ih2 => exact ih2
theorem w_case_shadow (n m : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    induction m with
    | zero => rw [Nat.add_succ, ih]
    | succ k ih2 =>
      case succ x => rw [Nat.add_succ]
theorem w_case_under (n m : Nat) : 0 + n = n := by
  induction n
  case zero => rfl
  case succ _ _ _ => rfl
theorem w_case_newer (n m : Nat) : 0 + m = m := by
  induction m
  case zero => rfl
  case succ x y z => exact congrArg Nat.succ y
theorem w_alt_inner (n m : Nat) : 0 + n = n := by
  induction n with
  | zero =>
    induction m with
    | zero => rfl
    | succ j ih => exact ih
-- applyRfl's sides of id (a = b), Prop and a = b (plan 9.4.8l, s2w-rfl-id.lf).
theorem w_rfl_id (a b : Nat) : id (a = b) := by rfl

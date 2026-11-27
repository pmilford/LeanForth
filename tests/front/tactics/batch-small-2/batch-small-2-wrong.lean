-- Pinned Lean's errors for the wrong twins of tests/front/tactics/batch-small-2/w-*.lf (plan
-- row 9.4.8z12, small tactics 2): tactic_check.py --lean checks that each message the
-- LeanForth file must print is Lean's. The u_* theorems are u-*.lf texts LeanForth answers
-- not supported yet for, which Lean rejects too (u_calc_target: throwCalcFailure's sides;
-- u_calc_hole: (_ : Nat) is no type); u-calc-odd.lf has no Lean twin (a first step written
-- alone has no LeanForth form).
set_option linter.unusedVariables false

theorem w_calc_lhs (a b c : Nat) (h1 : a = b) (h2 : a = c) : a = c := by
  calc a = b := h1
    a = c := h2
theorem w_calc_trans (a b c : Nat) (h1 : a = b ∧ b = c) (h2 : b = c ∧ c = a) :
    a = b ∧ c = a := by
  calc a = b ∧ b = c := h1
    _ ∧ c = a := h2
theorem w_calc_relation (a b : Nat) (h : a = b) : a = b := by
  calc True := trivial
theorem u_calc_target (a b c : Nat) (h1 : a = b) (h2 : b = c) : c = a := by
  calc a = b := h1
    _ = c := h2
theorem u_calc_hole (a b : Nat) (h1 : a = b) : a = b := by
  calc a = b := h1
    _ := h1
theorem w_wr_exact (a b : Nat) (h : Nat.pred (Nat.succ a) = b) : a = b := by
  with_reducible exact h
theorem w_wr_rfl (a : Nat) : a + 0 = a := by
  with_reducible rfl
theorem w_calc_order (a b c : Nat) (h1 : a = b) (h2 : c = c) : a = b ∧ c = c := by
  constructor
  calc a = b := ?_;
  exact h2
  exact h1
theorem w_calc_tagged (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c ∧ a = c := by
  constructor
  calc a = b := ?_
    _ = c := ?_;
  calc a = b := h1
    _ = c := h2
  case left.calc_2 => exact h2
  exact h1
theorem w_calc_natural (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  calc a = b := _
    _ = c := h2;
  exact h1
theorem w_rw_iff (a b : Nat) (h : a = b) : Nat.pred (Nat.succ a) = b ↔ b = b := by
  rw [h]
theorem w_rw_all (a b : Nat) (h : a = b) : Nat.pred (Nat.succ a) = b ↔ b = b := by
  with_unfolding_all rw [h]

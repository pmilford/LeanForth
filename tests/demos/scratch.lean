def sumTo : Nat → Nat
  | 0 => 0
  | n+1 => sumTo n + (n+1)

theorem gauss (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show 2 * (sumTo k + (k+1)) = (k+1) * (k+1+1)
    rw [Nat.mul_add, ih]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega

#check @gauss
theorem add_comm' (m n : Nat) : m + n = n + m := by
  induction n with
  | zero => exact (Nat.zero_add m).symm ▸ rfl
  | succ k ih => rw [Nat.add_succ, ih, Nat.succ_add]
#check @add_comm'
theorem cantor (α : Type) : ¬ ∃ f : α → α → Prop, ∀ g : α → Prop, ∃ a, f a = g :=
  fun ⟨f, h⟩ =>
    let ⟨a, ha⟩ := h (fun x => ¬ f x x)
    have e : f a a = ¬ f a a := congrFun ha a
    have n : ¬ f a a := fun p => (e ▸ p) p
    n (e ▸ n)
#check @cantor
set_option pp.fieldNotation false
#check @cantor

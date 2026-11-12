/-- Addition of natural numbers is commutative: `m + n = n + m`, by induction on `n`.
    Demo 1 of docs/user/DEMOS.md. -/
theorem add_comm_by_induction (m n : Nat) : m + n = n + m := by
  induction n with
  | zero => exact (Nat.zero_add m).symm ▸ rfl
  | succ k ih => rw [Nat.add_succ, ih, Nat.succ_add]

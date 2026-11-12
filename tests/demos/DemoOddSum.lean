/-- `sumOdd n = 1 + 3 + ... + (2 n - 1)`. -/
def sumOdd : Nat → Nat
  | 0 => 0
  | n + 1 => sumOdd n + (2 * n + 1)

/-- The sum of the first `n` odd numbers is `n²`. Demo 3 of docs/user/DEMOS.md. -/
theorem odd_sum (n : Nat) : sumOdd n = n ^ 2 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show sumOdd k + (2 * k + 1) = (k + 1) ^ 2
    rw [ih, Nat.pow_two, Nat.pow_two]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega

import Lean

/- Independent arithmetic model, not a semantics or proof of Forth. -/
namespace FactorialReference

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => factorial n * (n + 1)

-- Each multiplication is performed in mathematical Nat and checked before
-- being returned as a bounded-cell result. `none` denotes failure.
def bounded : Nat → Nat → Option Nat
  | limit, 0 => if 1 ≤ limit then some 1 else none
  | limit, n + 1 =>
    match bounded limit n with
    | none => none
    | some a => if a * (n + 1) ≤ limit then some (a * (n + 1)) else none

theorem factorial_pos (n : Nat) : 0 < factorial n := by
  induction n with
  | zero => simp [factorial]
  | succ n ih => simp [factorial, Nat.mul_pos ih]

theorem previous_le (n : Nat) : factorial n ≤ factorial (n + 1) := by
  simp only [factorial]
  exact Nat.le_mul_of_pos_right _ (Nat.zero_lt_succ n)

theorem bounded_exact (limit n : Nat) :
    bounded limit n = if factorial n ≤ limit then some (factorial n) else none := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [bounded, ih]
    by_cases h : factorial n ≤ limit
    · simp only [h, ↓reduceIte, factorial]
      rfl
    · have hn : ¬ factorial (n + 1) ≤ limit := by
        have hp := previous_le n
        omega
      simp only [h, ↓reduceIte, hn]

-- Signed input and maximum are modeled explicitly; the precondition on cell
-- representability is stated by the caller, not enforced by this function.
def checked (limit : Nat) (input : Int) : Option Nat :=
  if input < 0 then none else bounded limit input.toNat

theorem negative_rejected (limit : Nat) (input : Int) (h : input < 0) :
    checked limit input = none := by simp [checked, h]

theorem success_iff (limit : Nat) (input : Int) (h : 0 ≤ input) (result : Nat) :
    checked limit input = some result ↔
      factorial input.toNat ≤ limit ∧ result = factorial input.toNat := by
  simp [checked, Int.not_lt.mpr h, bounded_exact, eq_comm]

theorem overflow_iff (limit : Nat) (input : Int) (h : 0 ≤ input) :
    checked limit input = none ↔ limit < factorial input.toNat := by
  simp [checked, Int.not_lt.mpr h, bounded_exact]

example : checked 7 (-1) = none := by decide
example : checked 7 0 = some 1 := by decide
example : checked 7 3 = some 6 := by decide
example : checked 7 4 = none := by decide
example : checked 120 5 = some 120 := by decide
example : checked 119 5 = none := by decide

end FactorialReference

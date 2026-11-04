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

-- The contract of lf-factorial, in the style of `ClampContract` (clamp.lean).
-- `FactorialSpec limit n r`: `r` is a right answer for the input `n` when
-- `limit` is the largest cell, namely no result for a negative n or when n!
-- exceeds the limit, and n! otherwise. tests/reference/program-ir.lean copies
-- this block and proves that the word's IR meets the same clauses.
def FactorialSpec (limit : Nat) (n : Int) (r : Option Nat) : Prop :=
  (n < 0 → r = none) ∧
  (0 ≤ n → factorial n.toNat ≤ limit → r = some (factorial n.toNat)) ∧
  (0 ≤ n → limit < factorial n.toNat → r = none)

def FactorialContract (f : Nat → Int → Option Nat) : Prop :=
  ∀ (limit : Nat) (n : Int), FactorialSpec limit n (f limit n)

-- Rejecting negative inputs and factorials above the limit meets the clauses.
theorem guarded_spec (limit : Nat) (n : Int) :
    FactorialSpec limit n
      (if n < 0 then none else if factorial n.toNat ≤ limit then some (factorial n.toNat)
        else none) := by
  refine ⟨fun h => by simp [h], fun h fits => ?_, fun h over => ?_⟩
  · simp [Int.not_lt.mpr h, fits]
  · simp [Int.not_lt.mpr h, Nat.not_le.mpr over]

theorem checked_contract : FactorialContract checked := by
  intro limit n
  have same : checked limit n =
      if n < 0 then none else if factorial n.toNat ≤ limit then some (factorial n.toNat)
        else none := by
    simp only [checked, bounded_exact]
  rw [same]
  exact guarded_spec limit n

theorem negative_rejected (limit : Nat) (input : Int) (h : input < 0) :
    checked limit input = none := by simp [checked, h]

theorem success_iff (limit : Nat) (input : Int) (h : 0 ≤ input) (result : Nat) :
    checked limit input = some result ↔
      factorial input.toNat ≤ limit ∧ result = factorial input.toNat := by
  simp [checked, Int.not_lt.mpr h, bounded_exact, eq_comm]

theorem overflow_iff (limit : Nat) (input : Int) (h : 0 ≤ input) :
    checked limit input = none ↔ limit < factorial input.toNat := by
  simp [checked, Int.not_lt.mpr h, bounded_exact]

-- A deliberately wrong variant that treats 0 like a negative input: 0! = 1
-- fits every limit from 1 on and must be returned.
def checkedRejectsZero (limit : Nat) (input : Int) : Option Nat :=
  if input ≤ 0 then none else bounded limit input.toNat

theorem checkedRejectsZero_violates : ¬ FactorialContract checkedRejectsZero := by
  intro h
  have bad := (h 7 0).2.1 (by decide) (by decide)
  simp [checkedRejectsZero] at bad

example : checked 7 (-1) = none := by decide
example : checked 7 0 = some 1 := by decide
example : checked 7 3 = some 6 := by decide
example : checked 7 4 = none := by decide
example : checked 120 5 = some 120 := by decide
example : checked 119 5 = none := by decide

#print axioms checked_contract
#print axioms checkedRejectsZero_violates

end FactorialReference

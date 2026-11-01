import Lean

/- Mathematical reference only: no Forth operational semantics or runtime link. -/
namespace CheckedAddReference

def inCell (min max n : Int) : Prop := min ≤ n ∧ n ≤ max

-- Mirrors the order and strict comparisons of lf-checked-add.
def checkedAdd (min max a b : Int) : Option Int :=
  if 0 < b then
    if max - b < a then none else some (a + b)
  else if b < 0 then
    if a < min - b then none else some (a + b)
  else some (a + b)

-- The checks' subtractions are representable before the final addition.
theorem thresholds_safe (min max b : Int)
    (hmax : 0 ≤ max) (hmin : min = -max - 1)
    (hb : inCell min max b) :
    (0 < b → inCell min max (max - b)) ∧
    (b < 0 → inCell min max (min - b)) := by
  simp only [inCell] at *
  constructor <;> intro h <;> constructor <;> omega

-- Acceptance is exact: no in-range sum is rejected, and no other is returned.
theorem success_iff (min max a b : Int)
    (_hmax : 0 ≤ max) (hmin : min = -max - 1)
    (ha : inCell min max a) (_hb : inCell min max b) :
    checkedAdd min max a b = some (a + b) ↔ inCell min max (a + b) := by
  simp only [inCell] at *
  unfold checkedAdd
  split <;> rename_i hp
  · split <;> rename_i ht <;> simp_all <;> omega
  · split <;> rename_i hn
    · split <;> rename_i ht <;> simp_all <;> omega
    · simp_all <;> omega

theorem failure_iff (min max a b : Int)
    (_hmax : 0 ≤ max) (hmin : min = -max - 1)
    (ha : inCell min max a) (_hb : inCell min max b) :
    checkedAdd min max a b = none ↔ a + b < min ∨ max < a + b := by
  simp only [inCell] at *
  unfold checkedAdd
  split <;> rename_i hp
  · split <;> rename_i ht <;> simp_all <;> omega
  · split <;> rename_i hn
    · split <;> rename_i ht <;> simp_all <;> omega
    · simp_all <;> omega

-- Explicit small-cell boundary and out-of-range cases exercise both branches.
example : checkedAdd (-8) 7 7 0 = some 7 := by decide
example : checkedAdd (-8) 7 (-8) 0 = some (-8) := by decide
example : checkedAdd (-8) 7 7 1 = none := by decide
example : checkedAdd (-8) 7 (-8) (-1) = none := by decide
example : checkedAdd (-8) 7 (-8) 7 = some (-1) := by decide
example : checkedAdd (-8) 7 7 (-1) = some 6 := by decide
example : checkedAdd (-8) 7 (-8) 1 = some (-7) := by decide

end CheckedAddReference

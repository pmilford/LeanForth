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

-- The exact-acceptance statement of `success_iff`, as a contract on candidates.
def SuccessContract (f : Int → Int → Int → Int → Option Int) : Prop :=
  ∀ min max a b : Int, 0 ≤ max → min = -max - 1 →
    inCell min max a → inCell min max b →
    (f min max a b = some (a + b) ↔ inCell min max (a + b))

theorem checkedAdd_contract : SuccessContract checkedAdd :=
  fun min max a b hmax hmin ha hb => success_iff min max a b hmax hmin ha hb

-- Deliberately wrong variants, each off by one at a single threshold.
def upperOffByOne (min max a b : Int) : Option Int :=
  if 0 < b then
    if max - b ≤ a then none else some (a + b)
  else if b < 0 then
    if a < min - b then none else some (a + b)
  else some (a + b)

def lowerOffByOne (min max a b : Int) : Option Int :=
  if 0 < b then
    if max - b < a then none else some (a + b)
  else if b < 0 then
    if a ≤ min - b then none else some (a + b)
  else some (a + b)

-- In a four-bit cell 6 + 1 = 7 is the maximum and must be accepted.
theorem upperOffByOne_violates : ¬ SuccessContract upperOffByOne := by
  intro h
  have bad := h (-8) 7 6 1 (by decide) (by decide)
    (by unfold inCell; omega) (by unfold inCell; omega)
  simp [upperOffByOne, inCell] at bad

-- Likewise 0 + (-8) = -8 is the minimum and must be accepted.
theorem lowerOffByOne_violates : ¬ SuccessContract lowerOffByOne := by
  intro h
  have bad := h (-8) 7 0 (-8) (by decide) (by decide)
    (by unfold inCell; omega) (by unfold inCell; omega)
  simp [lowerOffByOne, inCell] at bad

-- Explicit small-cell boundary and out-of-range cases exercise both branches.
example : checkedAdd (-8) 7 7 0 = some 7 := by decide
example : checkedAdd (-8) 7 (-8) 0 = some (-8) := by decide
example : checkedAdd (-8) 7 7 1 = none := by decide
example : checkedAdd (-8) 7 (-8) (-1) = none := by decide
example : checkedAdd (-8) 7 (-8) 7 = some (-1) := by decide
example : checkedAdd (-8) 7 7 (-1) = some 6 := by decide
example : checkedAdd (-8) 7 (-8) 1 = some (-7) := by decide

end CheckedAddReference

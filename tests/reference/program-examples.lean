import Lean

/- Independent integer specifications inspired by examples.fs. They are not an
   operational semantics for Forth and do not establish source correspondence. -/
namespace ProgramExamplesReference

-- `none` represents the single failure result; `some` represents success.
def checkedAbs (min n : Int) : Option Int :=
  if n = min then none else some (if n < 0 then -n else n)

def inRange (value lower upper : Int) : Option Bool :=
  if lower > upper then none else some (decide (lower ≤ value ∧ value ≤ upper))

-- The contracts of lf-checked-abs and lf-in-range, in the style of
-- `ClampContract` (clamp.lean). `CheckedAbsSpec min max n r` and
-- `InRangeSpec value lower upper r` say that `r` is a right answer for those
-- inputs. tests/reference/program-ir.lean copies this block and proves that
-- the words' IR meets the same clauses.

-- The smallest cell has no magnitude in the cell and gives no result; every
-- other input gives its magnitude, which lies in the cell.
def CheckedAbsSpec (min max n : Int) (r : Option Int) : Prop :=
  (n = min → r = none) ∧
  (n ≠ min → r = some (n.natAbs : Int)) ∧
  (∀ m, r = some m → 0 ≤ m ∧ m ≤ max)

def CheckedAbsContract (f : Int → Int → Option Int) : Prop :=
  ∀ min max n : Int, 0 ≤ max → min = -max - 1 → min ≤ n → n ≤ max →
    CheckedAbsSpec min max n (f min n)

theorem checkedAbs_contract : CheckedAbsContract checkedAbs := by
  intro min max n _ hmin low high
  simp only [CheckedAbsSpec, checkedAbs]
  by_cases h : n = min
  · simp [h]
  · simp only [h, ↓reduceIte, false_implies, Option.some.injEq, forall_eq', true_and]
    constructor <;> split <;> omega

-- Reversed bounds give no result; for ordered bounds the answer is true
-- exactly inside the closed interval and false exactly outside it.
def InRangeSpec (value lower upper : Int) (r : Option Bool) : Prop :=
  (lower > upper → r = none) ∧
  (lower ≤ upper → (r = some true ↔ lower ≤ value ∧ value ≤ upper)) ∧
  (lower ≤ upper → (r = some false ↔ value < lower ∨ upper < value))

def InRangeContract (f : Int → Int → Int → Option Bool) : Prop :=
  ∀ value lower upper : Int, InRangeSpec value lower upper (f value lower upper)

theorem inRange_contract : InRangeContract inRange := by
  intro value lower upper
  simp only [InRangeSpec, inRange]
  by_cases h : lower > upper
  · simp only [h, ↓reduceIte, forall_const, true_and]
    constructor <;> intro _ <;> omega
  · simp only [h, ↓reduceIte, false_implies, Option.some.injEq, true_and]
    constructor <;> intro _ <;> simp <;> omega

-- The parameterized signed-cell bounds have the two's-complement relation.
-- Inputs are assumed to be representable; on success the magnitude is too.
theorem checkedAbs_correct (min max n : Int)
    (_hmax : 0 ≤ max) (hbounds : min = -max - 1)
    (hnlo : min ≤ n) (hnhi : n ≤ max) :
    (n = min ∧ checkedAbs min n = none) ∨
    (n ≠ min ∧ checkedAbs min n = some (Int.natAbs n : Int) ∧
      0 ≤ (Int.natAbs n : Int) ∧ (Int.natAbs n : Int) ≤ max) := by
  by_cases h : n = min
  · left; simp [h, checkedAbs]
  · right
    have ha : (Int.natAbs n : Int) = if n < 0 then -n else n := by
      split <;> rename_i hs
      · exact Int.ofNat_natAbs_of_nonpos (by omega)
      · exact Int.natAbs_of_nonneg (by omega)
    refine ⟨h, ?_, ?_, ?_⟩
    · simp [checkedAbs, h, ha]
    · omega
    · split at ha <;> omega

-- Reversed bounds reject; ordered bounds return exactly inclusive membership.
theorem inRange_reversed (v lo hi : Int) (h : hi < lo) :
    inRange v lo hi = none := by
  simp [inRange, h]

theorem inRange_ordered (v lo hi : Int) (h : lo ≤ hi) :
    inRange v lo hi = some true ↔ lo ≤ v ∧ v ≤ hi := by
  simp [inRange, Int.not_lt.mpr h]

theorem inRange_ordered_false (v lo hi : Int) (h : lo ≤ hi) :
    inRange v lo hi = some false ↔ v < lo ∨ hi < v := by
  simp [inRange, Int.not_lt.mpr h]
  omega

-- Deliberately wrong variants: an exclusive upper bound, rejection of the
-- one-point interval as if it were reversed, and an absolute value without
-- the test for the smallest cell (Forth's ABS alone).
def inRangeExclusiveUpper (value lower upper : Int) : Option Bool :=
  if lower > upper then none else some (decide (lower ≤ value ∧ value < upper))

def inRangeRejectsEqual (value lower upper : Int) : Option Bool :=
  if lower ≥ upper then none else some (decide (lower ≤ value ∧ value ≤ upper))

def absAcceptsMin (_min n : Int) : Option Int :=
  some (if n < 0 then -n else n)

theorem inRangeExclusiveUpper_violates : ¬ InRangeContract inRangeExclusiveUpper := by
  intro h
  have bad := (h 10 0 10).2.1 (by decide)
  simp [inRangeExclusiveUpper] at bad

theorem inRangeRejectsEqual_violates : ¬ InRangeContract inRangeRejectsEqual := by
  intro h
  have bad := (h 3 3 3).2.1 (by decide)
  simp [inRangeRejectsEqual] at bad

-- In a four-bit cell |-8| = 8 does not fit, and the smallest cell must give
-- no result.
theorem absAcceptsMin_violates : ¬ CheckedAbsContract absAcceptsMin := by
  intro h
  have bad := (h (-8) 7 (-8) (by decide) (by decide) (by decide) (by decide)).1 rfl
  simp [absAcceptsMin] at bad

#print axioms checkedAbs_contract
#print axioms inRange_contract
#print axioms inRangeExclusiveUpper_violates
#print axioms inRangeRejectsEqual_violates
#print axioms absAcceptsMin_violates

end ProgramExamplesReference

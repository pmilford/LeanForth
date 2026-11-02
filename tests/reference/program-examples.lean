import Lean

/- Independent integer specifications inspired by examples.fs. They are not an
   operational semantics for Forth and do not establish source correspondence. -/
namespace ProgramExamplesReference

-- `none` represents the single failure result; `some` represents success.
def checkedAbs (min n : Int) : Option Int :=
  if n = min then none else some (if n < 0 then -n else n)

def inRange (value lower upper : Int) : Option Bool :=
  if lower > upper then none else some (decide (lower ≤ value ∧ value ≤ upper))

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

-- The `inRange_ordered` statement, as a contract on candidate functions.
def OrderedContract (f : Int → Int → Int → Option Bool) : Prop :=
  ∀ v lo hi : Int, lo ≤ hi → (f v lo hi = some true ↔ lo ≤ v ∧ v ≤ hi)

theorem inRange_contract : OrderedContract inRange :=
  fun v lo hi h => inRange_ordered v lo hi h

-- Deliberately wrong variants: an exclusive upper bound, and rejection of
-- the one-point interval as if it were reversed.
def inRangeExclusiveUpper (value lower upper : Int) : Option Bool :=
  if lower > upper then none else some (decide (lower ≤ value ∧ value < upper))

def inRangeRejectsEqual (value lower upper : Int) : Option Bool :=
  if lower ≥ upper then none else some (decide (lower ≤ value ∧ value ≤ upper))

theorem inRangeExclusiveUpper_violates : ¬ OrderedContract inRangeExclusiveUpper := by
  intro h
  have bad := h 10 0 10 (by decide)
  simp [inRangeExclusiveUpper] at bad

theorem inRangeRejectsEqual_violates : ¬ OrderedContract inRangeRejectsEqual := by
  intro h
  have bad := h 3 3 3 (by decide)
  simp [inRangeRejectsEqual] at bad

end ProgramExamplesReference

/- Deliberately incorrect clamps. Every claim in this file is false and must be
   rejected: tests/reference/check.sh requires Lean to fail, with a `decide`
   "is false" diagnostic. The proved refutations are in clamp.lean
   (`aboveEscapesClamp_violates_bounds`, `swappedClamp_violates_contract`). -/

-- Returns an input above the interval instead of the upper endpoint.
def incorrectClamp (lower upper value : Int) : Int :=
  if value < lower then lower else if value > upper then value else value

example : incorrectClamp 0 10 11 ≤ 10 := by decide

-- The `clamp_bounds` statement and the proof script that establishes it for
-- the correct clamp must fail for this implementation.
theorem incorrectClamp_bounds (lower upper value : Int) (ordered : lower ≤ upper) :
    lower ≤ incorrectClamp lower upper value ∧ incorrectClamp lower upper value ≤ upper := by
  unfold incorrectClamp
  split <;> (try split) <;> omega

-- Returns the opposite endpoint for inputs outside the interval. Results stay
-- in range, so only the endpoint (`clamp_below`/`clamp_above`) claims fail.
def swappedClamp (lower upper value : Int) : Int :=
  if value < lower then upper else if value > upper then lower else value

example : (-1 : Int) < 0 → swappedClamp 0 10 (-1) = 0 := by decide
example : (11 : Int) > 10 → swappedClamp 0 10 11 = 10 := by decide

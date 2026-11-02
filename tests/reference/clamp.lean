import Lean

def clamp (lower upper value : Int) : Int :=
  if value < lower then lower else if value > upper then upper else value

theorem clamp_bounds (lower upper value : Int) (ordered : lower ≤ upper) :
    lower ≤ clamp lower upper value ∧ clamp lower upper value ≤ upper := by
  unfold clamp
  split <;> (try split) <;> omega

theorem clamp_inside (lower upper value : Int)
    (above : lower ≤ value) (below : value ≤ upper) :
    clamp lower upper value = value := by
  unfold clamp
  split <;> (try split) <;> omega

theorem clamp_below (lower upper value : Int) (below : value < lower) :
    clamp lower upper value = lower := by
  simp [clamp, below]

theorem clamp_above (lower upper value : Int) (ordered : lower ≤ upper)
    (above : value > upper) : clamp lower upper value = upper := by
  unfold clamp
  split <;> (try split) <;> omega

-- The four properties above, as one contract over candidate functions.
def ClampContract (f : Int → Int → Int → Int) : Prop :=
  ∀ lower upper value, lower ≤ upper →
    (lower ≤ f lower upper value ∧ f lower upper value ≤ upper) ∧
    (lower ≤ value → value ≤ upper → f lower upper value = value) ∧
    (value < lower → f lower upper value = lower) ∧
    (value > upper → f lower upper value = upper)

theorem clamp_contract : ClampContract clamp := by
  intro lower upper value ordered
  exact ⟨clamp_bounds lower upper value ordered,
    fun above below => clamp_inside lower upper value above below,
    fun below => clamp_below lower upper value below,
    fun above => clamp_above lower upper value ordered above⟩

-- Deliberately wrong candidates must fail the contract. Returning an input
-- above the interval breaks the `clamp_bounds` statement itself.
def aboveEscapesClamp (lower upper value : Int) : Int :=
  if value < lower then lower else if value > upper then value else value

theorem aboveEscapesClamp_violates_bounds :
    ¬ ∀ lower upper value : Int, lower ≤ upper →
      lower ≤ aboveEscapesClamp lower upper value ∧
        aboveEscapesClamp lower upper value ≤ upper := by
  intro h
  have bad := (h 0 10 11 (by decide)).2
  simp [aboveEscapesClamp] at bad

-- Swapping the endpoints keeps every result in range, so `clamp_bounds`
-- alone cannot reject it; the endpoint clauses of the contract do.
def swappedClamp (lower upper value : Int) : Int :=
  if value < lower then upper else if value > upper then lower else value

theorem swappedClamp_in_range (lower upper value : Int) (ordered : lower ≤ upper) :
    lower ≤ swappedClamp lower upper value ∧ swappedClamp lower upper value ≤ upper := by
  unfold swappedClamp
  split <;> (try split) <;> omega

theorem swappedClamp_violates_contract : ¬ ClampContract swappedClamp := by
  intro h
  have bad := (h 0 10 (-1) (by decide)).2.2.1 (by decide)
  simp [swappedClamp] at bad

-- Print one test case in the same stable format as the Forth table.
def emitClamp (lower upper value : Int) : IO Unit := do
  if lower > upper then
    IO.println s!"{lower} {upper} {value} invalid"
  else
    IO.println s!"{lower} {upper} {value} {clamp lower upper value} "

def main : IO Unit := do
  for lowerNat in [0:7] do
    for upperNat in [0:7] do
      for valueNat in [0:7] do
        let lower := (Int.ofNat lowerNat) - 3
        let upper := (Int.ofNat upperNat) - 3
        let value := (Int.ofNat valueNat) - 3
        emitClamp lower upper value
  -- These seven values fit a signed 32-bit cell and exercise its endpoints.
  let boundaries : List Int := [-2147483648, -2147483647, -1, 0, 1, 2147483646, 2147483647]
  for lower in boundaries do
    for upper in boundaries do
      for value in boundaries do
        emitClamp lower upper value

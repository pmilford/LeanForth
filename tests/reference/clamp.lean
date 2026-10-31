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

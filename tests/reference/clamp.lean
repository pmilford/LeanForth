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

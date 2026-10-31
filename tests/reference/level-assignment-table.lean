import Lean

open Lean

-- Instantiate a symbolic level using Lean's own parameter substitution and
-- normalize each finite instance. This does not prove a polymorphic theorem.
def main : IO Unit := do
  let u := Level.param `u
  let v := Level.param `v
  let expression := Level.imax (Level.max (.succ u) v) (Level.imax v u)
  for left in [0:6] do
    for right in [0:6] do
      let instantiated := expression.instantiateParams [`u, `v]
        [Level.ofNat left, Level.ofNat right]
      match instantiated.normalize.toNat with
      | some value => IO.println s!"{left} {right} {value}"
      | none => throw <| IO.userError "instantiated level is not concrete"

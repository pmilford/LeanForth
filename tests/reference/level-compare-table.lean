import Lean

open Lean

-- Compare constructed levels with Lean's own equivalence procedure. These
-- cases do not establish completeness of any external implementation.
def main : IO Unit := do
  let u := Level.param `u
  let v := Level.param `v
  let one := Level.succ .zero
  let cases := [(u, u), (Level.succ u, Level.succ u), (u, v),
    (u, Level.max u .zero), (one, Level.max one .zero), (.zero, one),
    (Level.imax u .zero, .zero), (Level.max u v, Level.max v u)]
  for ((left, right), index) in cases.zipIdx do
    IO.println s!"{index} {if left.isEquiv right then 1 else 0}"

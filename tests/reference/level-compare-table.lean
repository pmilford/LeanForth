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
    (Level.imax u .zero, .zero), (Level.max u v, Level.max v u),
    (u, Level.max .zero u), (Level.succ (Level.max u .zero), Level.succ u),
    (Level.imax (Level.succ u) .zero, .zero),
    (Level.max .zero (Level.max u .zero), u),
    (Level.max (Level.succ (Level.max u .zero)) v, Level.max (Level.succ u) v),
    (Level.imax (Level.succ (Level.max u .zero)) v, Level.imax (Level.succ u) v),
    (Level.imax .zero u, .zero)]
  for ((left, right), index) in cases.zipIdx do
    IO.println s!"{index} {if left.isEquiv right then 1 else 0}"

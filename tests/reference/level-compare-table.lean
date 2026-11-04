import Lean

open Lean Elab Command

-- Compare constructed levels as Lean's kernel does: Kernel.isDefEq on two
-- Sorts, which quick_is_def_eq decides by is_equivalent (type_checker.cpp
-- 810-811; ADR 0011, Amendment 1). Until 2026-11-03 this table used
-- Level.isEquiv, the elaborator's own normalisation, which is not the
-- kernel's. These cases do not establish completeness of any external
-- implementation.
run_cmd do
  let env ← getEnv
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
    let equal := match Kernel.isDefEq env {} (.sort left) (.sort right) with
      | .ok true => 1
      | _ => 0
    IO.println s!"{index} {equal}"

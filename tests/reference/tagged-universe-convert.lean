import Lean
open Lean Elab Command

-- Compare the exact symbolic levels used by the tagged Forth fixture. This is
-- finite evidence for conversion, not proof-checker or Mathlib compatibility.
run_cmd do
  let u := Level.param `u
  let v := Level.param `v
  let cases := [(u, .max u .zero), (.imax u .zero, .zero), (u, v),
    (.zero, .succ .zero), (.succ (.max u .zero), .succ u),
    (.imax .zero u, .zero), (.max u v, .max v u)]
  for ((left, right), index) in cases.zipIdx do
    let equal ← match Kernel.isDefEq (← getEnv) {} (.sort left) (.sort right) with
      | .ok result => pure result
      | .error _ => throwError "Lean conversion failed for universe case {index}"
    liftIO <| IO.println s!"{index} {if equal then 1 else 0}"

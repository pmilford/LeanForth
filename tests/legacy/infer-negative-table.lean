import Lean

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let lctx : LocalContext := {}
  let prop := Expr.sort .zero
  let var0 := Expr.bvar 0
  let identity := Expr.lam `P prop var0 .default
  let cases := [var0, Expr.app prop prop, Expr.app prop var0,
    Expr.forallE `x identity var0 .default, Expr.app identity prop,
    Expr.forallE `P prop (Expr.bvar 1) .default]
  for (expression, index) in cases.zipIdx do
    match Kernel.check env lctx expression with
      | .error _ => liftIO <| IO.println s!"{index} 1 "
      | .ok _ => throwError "Lean kernel unexpectedly inferred negative case {index}"

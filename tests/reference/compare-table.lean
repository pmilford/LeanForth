import Lean

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let lctx : LocalContext := {}
  let prop := Expr.sort .zero
  let type0 := Expr.sort (.succ .zero)
  let var0 := Expr.bvar 0
  let beta := Expr.app (Expr.lam `P type0 var0 .default) prop
  let identity := Expr.lam `P prop (Expr.lam `proof var0 var0 .default) .default
  let plainDomain := Expr.lam `P prop var0 .default
  let betaDomain := Expr.lam `P beta var0 .default
  let cases := [(prop, prop), (prop, type0), (beta, prop),
                (identity, identity), (prop, identity), (plainDomain, betaDomain)]
  for ((left, right), index) in cases.zipIdx do
    for expression in [left, right] do
      match Kernel.check env lctx expression with
        | .ok _ => pure ()
        | .error _ => throwError "comparison case {index} is not well typed"
    let equal ← match Kernel.isDefEq env lctx left right with
      | .ok result => pure result
      | .error _ => throwError "Lean comparison failed for case {index}"
    let flag : Nat := if equal then 1 else 0
    liftIO <| IO.println s!"{index} {flag} "

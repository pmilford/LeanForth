import Lean

open Lean Elab Command

-- Direct oracle outcomes for closed declaration candidates. Each declaration
-- is checked against the original environment with no assumed new axioms.
run_cmd do
  let env := (← getEnv).toKernelEnv
  let prop := Expr.sort .zero
  let target := Expr.forallE `P prop
    (Expr.forallE `proof (Expr.bvar 0) (Expr.bvar 1) .default) .default
  let identity := Expr.lam `P prop
    (Expr.lam `proof (Expr.bvar 0) (Expr.bvar 0) .default) .default
  let wrong := Expr.lam `P prop
    (Expr.lam `proof (Expr.bvar 0) (Expr.bvar 1) .default) .default
  let betaDomain := Expr.app
    (Expr.lam `X (Expr.sort (.succ .zero)) (Expr.bvar 0) .default) prop
  let betaTarget := Expr.forallE `P betaDomain
    (Expr.forallE `proof (Expr.bvar 0) (Expr.bvar 1) .default) .default
  let cases := [(target, identity), (target, wrong), (identity, identity),
    (Expr.sort (.succ .zero), prop), (betaTarget, identity)]
  for ((type, value), index) in cases.zipIdx do
    let decl : Declaration := .thmDecl {
      name := Name.mkSimple s!"LeanForthDeclarationProbe{index}"
      levelParams := [], type, value
    }
    let outcome := match env.addDeclCore 1000000 1000 decl none with
      | .ok _ => 0
      | .error _ => 1
    liftIO <| IO.println s!"{index} {outcome}"

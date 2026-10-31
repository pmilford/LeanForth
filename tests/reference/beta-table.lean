import Lean

open Lean Elab Command

partial def renderBetaTerm : Expr → String
  | .sort level => match level.toNat with
    | some number => s!"S {number} "
    | none => "UNSUPPORTED "
  | .bvar index => s!"V {index} "
  | .app fn arg => "A " ++ renderBetaTerm fn ++ renderBetaTerm arg
  | .lam _ domain body _ => "L " ++ renderBetaTerm domain ++ renderBetaTerm body
  | .forallE _ domain body _ => "P " ++ renderBetaTerm domain ++ renderBetaTerm body
  | _ => "UNSUPPORTED "

run_cmd do
  let env ← getEnv
  let lctx : LocalContext := {}
  let prop := Expr.sort .zero
  let type0 := Expr.sort (.succ .zero)
  let type1 := Expr.sort (.succ (.succ .zero))
  let var0 := Expr.bvar 0
  let simpleBeta := Expr.app (Expr.lam `P type0 var0 .default) prop
  let dependentBeta := Expr.app
    (Expr.lam `A type0 (Expr.lam `x var0 var0 .default) .default) prop
  let polyIdentity := Expr.lam `A type1 (Expr.lam `x var0 var0 .default) .default
  let nestedBeta := Expr.app (Expr.app polyIdentity type0) prop
  let quantified := Expr.forallE `P prop var0 .default
  let underBinder := Expr.lam `A type0
    (Expr.app (Expr.lam `B type0 var0 .default) var0) .default
  let mut cases := #[prop, quantified, simpleBeta, dependentBeta, nestedBeta, underBinder]
  for level in [0:3] do
    for depth in [1:4] do
      let identity := Expr.lam `X (.sort (Level.ofNat (level + 1))) var0 .default
      let mut expression := Expr.sort (Level.ofNat level)
      for _ in [0:depth] do
        expression := Expr.app identity expression
      cases := cases.push expression
  for (expression, index) in cases.toList.zipIdx do
    match Kernel.check env lctx expression with
      | .error _ => throwError "beta reference case {index} is not well typed"
      | .ok _ => pure ()
    let reduced ← match Kernel.whnf env lctx expression with
      | .ok result => pure result
      | .error _ => throwError "Lean kernel failed to normalize beta case {index}"
    liftIO <| IO.println s!"{index} {renderBetaTerm reduced}"

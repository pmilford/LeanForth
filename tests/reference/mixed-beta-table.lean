import Lean
open Lean Elab Command

axiom mixedBetaC : Prop
axiom mixedBetaD : Prop
axiom mixedBetaF : Prop → Prop

partial def renderMixedBeta : Expr → String
  | .sort .zero => "S "
  | .const `mixedBetaC [] => "C "
  | .const `mixedBetaD [] => "D "
  | .const `mixedBetaF [] => "F "
  | .bvar i => s!"V {i} "
  | .app f a => "A " ++ renderMixedBeta f ++ renderMixedBeta a
  | .lam _ d b _ => "L " ++ renderMixedBeta d ++ renderMixedBeta b
  | .forallE _ d b _ => "P " ++ renderMixedBeta d ++ renderMixedBeta b
  | _ => "UNSUPPORTED "

-- Local oracle axioms only furnish constant types to the Lean kernel;
-- no declaration is imported or trusted by LeanForth.
run_cmd do
  let env ← getEnv
  let lctx : LocalContext := {}
  let s := Expr.sort .zero
  let c := Expr.const `mixedBetaC []
  let d := Expr.const `mixedBetaD []
  let f := Expr.const `mixedBetaF []
  let v0 := Expr.bvar 0
  let v1 := Expr.bvar 1
  let identity := Expr.lam `x s v0 .default
  let constD := Expr.lam `x s d .default
  let first := Expr.lam `x s (Expr.lam `y s v1 .default) .default
  let applyF := Expr.lam `x s (Expr.app f v0) .default
  let cases := [c, Expr.app identity c, Expr.app constD c,
    Expr.app (Expr.app first c) d,
    Expr.app f (Expr.app identity c), Expr.app applyF c,
    Expr.lam `x s (Expr.app identity v0) .default]
  for (expression, index) in cases.zipIdx do
    match Kernel.check env lctx expression with
      | .error _ => throwError "ill-typed mixed beta reference case {index}"
      | .ok _ => pure ()
    let result ← match Kernel.whnf env lctx expression with
      | .ok result => pure result
      | .error _ => throwError "kernel WHNF failed at case {index}"
    liftIO <| IO.println s!"{index} {renderMixedBeta result}"

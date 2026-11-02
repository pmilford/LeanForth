import Lean

open Lean Elab Command

partial def renderInferredTerm : Expr → String
  | .sort level => match level.toNat with
    | some number => s!"S {number} "
    | none => "UNSUPPORTED "
  | .bvar index => s!"V {index} "
  | .app fn arg => "A " ++ renderInferredTerm fn ++ renderInferredTerm arg
  | .lam _ domain body _ => "L " ++ renderInferredTerm domain ++ renderInferredTerm body
  | .forallE _ domain body _ => "P " ++ renderInferredTerm domain ++ renderInferredTerm body
  | _ => "UNSUPPORTED "

run_cmd do
  let env ← getEnv
  let lctx : LocalContext := {}
  let prop := Expr.sort .zero
  let type0 := Expr.sort (.succ .zero)
  let var0 := Expr.bvar 0
  let arrow := Expr.forallE `argument (Expr.bvar 2) (Expr.bvar 2) .default
  let composition := Expr.lam `A prop (Expr.lam `B prop (Expr.lam `C prop
    (Expr.lam `f arrow (Expr.lam `g arrow (Expr.lam `value (Expr.bvar 4)
      (Expr.app (Expr.bvar 1) (Expr.app (Expr.bvar 2) var0))
      .default) .default) .default) .default) .default) .default
  let cases := [prop, type0, Expr.forallE `P prop var0 .default,
    Expr.forallE `A type0 var0 .default,
    Expr.lam `P prop (Expr.lam `proof var0 var0 .default) .default,
    Expr.app (Expr.lam `P type0 var0 .default) prop, composition]
  for (expression, index) in cases.zipIdx do
    let inferred ← match Kernel.check env lctx expression with
      | .ok result => pure result
      | .error _ => throwError "Lean kernel rejected positive inference case {index}"
    liftIO <| IO.println s!"{index} {renderInferredTerm inferred}"

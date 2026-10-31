import Lean

open Lean Elab Command

-- Test-only prefix syntax; binders' names do not affect their de Bruijn trees.
partial def renderBinderType : Expr → String
  | .sort level => match level.toNat with
    | some n => s!"S {n} "
    | none => panic! "non-concrete universe in result"
  | .bvar n => s!"V {n} "
  | .forallE _ a b _ => "P " ++ renderBinderType a ++ renderBinderType b
  | .lam _ a b _ => "L " ++ renderBinderType a ++ renderBinderType b
  | .app f a => "A " ++ renderBinderType f ++ renderBinderType a
  | _ => panic! "unsupported inferred syntax"

run_cmd do
  let env ← getEnv
  let lctx : LocalContext := {}
  for uval in [0:3] do
    let s := Expr.sort (Level.ofNat uval)
    let v0 := Expr.bvar 0
    let v1 := Expr.bvar 1
    let lam := fun a b => Expr.lam `x a b .default
    let pi := fun a b => Expr.forallE `x a b .default
    let cases := [lam s (lam v0 v0), lam s (lam v0 (lam v1 v1)),
      pi s (pi v0 v1), lam s (lam (pi v0 v1) (lam v1 v1)), v0, lam s v1]
    for (e, index) in cases.zipIdx do
      match Kernel.check env lctx e with
      | .ok ty =>
        if index ≥ 4 then throwError "Lean accepted unbound case {index}"
        liftIO <| IO.println s!"{uval} {index} OK {renderBinderType ty}"
      | .error _ =>
        if index < 4 then throwError "Lean rejected positive case {index}"
        liftIO <| IO.println s!"{uval} {index} REJECT "

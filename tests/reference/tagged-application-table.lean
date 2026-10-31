import Lean
open Lean Elab Command

-- Finite direct oracle for the candidate tagged application inference path.
-- This checks Lean's types and rejection, not a LeanForth theorem receipt.
partial def renderApplicationType : Expr → String
  | .sort level => match level.toNat with
    | some n => s!"S {n} "
    | none => panic! "non-concrete universe"
  | .bvar n => s!"V {n} "
  | .forallE _ a b _ => "P " ++ renderApplicationType a ++ renderApplicationType b
  | .lam _ a b _ => "L " ++ renderApplicationType a ++ renderApplicationType b
  | .app f a => "A " ++ renderApplicationType f ++ renderApplicationType a
  | _ => panic! "unsupported inferred syntax"

run_cmd do
  let env ← getEnv
  for uval in [0:3] do
    let s := Expr.sort (Level.ofNat uval)
    let v0 := Expr.bvar 0
    let v1 := Expr.bvar 1
    let lam := fun a b => Expr.lam `x a b .default
    let cases := [
      lam s (lam v0 (Expr.app (lam v1 v0) v0)),
      lam s (Expr.app (lam s v0) v0),
      lam s (Expr.app v0 v0),
      lam s (lam v0 (Expr.app (lam s v0) v0))]
    for (e, index) in cases.zipIdx do
      match Kernel.check env {} e with
      | .ok ty =>
        if index ≥ 2 then throwError "Lean accepted invalid application {index}"
        liftIO <| IO.println s!"{uval} {index} OK {renderApplicationType ty}"
      | .error _ =>
        if index < 2 then throwError "Lean rejected valid application {index}"
        liftIO <| IO.println s!"{uval} {index} REJECT "

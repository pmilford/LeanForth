import Lean
open Lean Elab Command

-- Check the same nested-binder beta equalities used by the tagged Forth test.
-- This is finite differential evidence, not a LeanForth proof certificate.
run_cmd do
  let prop := Expr.sort .zero
  let v0 := Expr.bvar 0
  let v1 := Expr.bvar 1
  let lam := fun a b => Expr.lam `x a b .default
  let left := lam prop (.app (lam prop (lam prop v1)) v0)
  let right := lam prop (lam prop v1)
  let wrong := lam prop (lam prop v0)
  let env ← getEnv
  for expression in [left, right, wrong] do
    match Kernel.check env {} expression with
    | .ok _ => pure ()
    | .error _ => throwError "Lean rejected the capture-avoidance input"
  match Kernel.isDefEq env {} left right, Kernel.isDefEq env {} left wrong with
  | .ok true, .ok false => pure ()
  | _, _ => throwError "Lean disagreed with capture-avoidance expectations"

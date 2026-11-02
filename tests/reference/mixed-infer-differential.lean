import Lean
open Lean Elab Command

-- The corresponding Forth signature is only an assumption. This observes
-- Lean's kernel on finite expressions and does not certify Forth declarations.
universe u
def mixedDifferentialId {A : Sort u} (x : A) : A := x

run_cmd do
  let env ← getEnv
  for n in [0:3] do
    let u := Level.ofNat n
    let s := Expr.sort u
    let v0 := Expr.bvar 0
    let v1 := Expr.bvar 1
    let lam := fun a b => Expr.lam `x a b .default
    let pi := fun a b => Expr.forallE `x a b .default
    let id := Expr.const `mixedDifferentialId [u]
    let idA := Expr.app id v1
    let idx := Expr.app idA v0
    let polyType := pi s (pi v0 v1)
    let cases := [
      (id, polyType),
      (lam s (lam v0 idx), polyType),
      (lam s (lam v0 (Expr.app idA idx)), polyType),
      (lam s (Expr.app (Expr.app (Expr.const `mixedDifferentialId [.succ u]) s) v0), pi s s)]
    for ((term, expected), index) in cases.zipIdx do
      let ty ← match Kernel.check env {} term with
        | .ok ty => pure ty
        | .error _ => throwError "Lean rejected positive case {n}/{index}"
      match Kernel.isDefEq env {} ty expected with
      | .ok true => liftIO <| IO.println s!"{n} {index} ACCEPT"
      | _ => throwError "Lean inferred unexpected type for {n}/{index}"
    -- The kernel's failure reason is not inspected in these negative cases.
    let negatives := [Expr.app id s, Expr.const `mixedDifferentialMissing [.succ u], lam v0 v0]
    for (term, index) in negatives.zipIdx do
      match Kernel.check env {} term with
      | .ok _ => throwError "Lean accepted negative case {n}/{index + 4}"
      | .error _ => liftIO <| IO.println s!"{n} {index + 4} REJECT"

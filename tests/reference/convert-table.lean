import Lean

open Lean Elab Command

-- Definitional equality oracle for tests/core/mixed-convert-plain-table.fs.
-- It joins three earlier tables: closed beta comparisons (section 0), nested
-- binder capture (section 1) and symbolic universes (section 2). Each row is
-- "section index flag", flag 1 when Lean's kernel finds the terms equal.
-- Finite differential evidence only, not a LeanForth proof certificate.
def defEqFlag (env : Environment) (left right : Expr) (label : String) :
    CommandElabM Nat := do
  for expression in [left, right] do
    match Kernel.check env {} expression with
    | .ok _ => pure ()
    | .error _ => throwError "conversion case {label} is not well typed"
  match Kernel.isDefEq env {} left right with
  | .ok result => pure (if result then 1 else 0)
  | .error _ => throwError "Lean comparison failed for case {label}"

run_cmd do
  let env ← getEnv
  let prop := Expr.sort .zero
  let type0 := Expr.sort (.succ .zero)
  let v0 := Expr.bvar 0
  let v1 := Expr.bvar 1
  let lam := fun a b => Expr.lam `x a b .default
  let beta := Expr.app (lam type0 v0) prop
  let identity := lam prop (lam v0 v0)
  let closed := [(prop, prop), (prop, type0), (beta, prop),
    (identity, identity), (prop, identity), (lam prop v0, lam beta v0)]
  let capture := [(lam prop (.app (lam prop (lam prop v1)) v0), lam prop (lam prop v1)),
    (lam prop (.app (lam prop (lam prop v1)) v0), lam prop (lam prop v0))]
  let u := Level.param `u
  let v := Level.param `v
  let universes := [(u, .max u .zero), (.imax u .zero, .zero), (u, v),
    (.zero, .succ .zero), (.succ (.max u .zero), .succ u),
    (.imax .zero u, .zero), (.max u v, .max v u)]
  let sections := [closed, capture,
    universes.map fun (left, right) => (Expr.sort left, Expr.sort right)]
  for (cases, part) in sections.zipIdx do
    for ((left, right), index) in cases.zipIdx do
      let flag ← defEqFlag env left right s!"{part} {index}"
      liftIO <| IO.println s!"{part} {index} {flag}"

import Lean
open Lean Elab Command

axiom mixedConvertC : Prop
axiom mixedConvertD : Prop
axiom mixedConvertF : Prop → Prop

-- These local oracle axioms provide types only. LeanForth does not import
-- them or accept them as trusted declarations.
run_cmd do
  let env ← getEnv
  let s := Expr.sort .zero
  let s1 := Expr.sort (.succ .zero)
  let c := Expr.const `mixedConvertC []
  let d := Expr.const `mixedConvertD []
  let f := Expr.const `mixedConvertF []
  let identity := Expr.lam `x s (.bvar 0) .default
  let bc := Expr.app identity c
  let bd := Expr.app identity d
  let cases := [(bc, c, true), (bd, c, false),
    (Expr.forallE `x bc c .default, Expr.forallE `x c c .default, true),
    (Expr.lam `x c bc .default, Expr.lam `x c c .default, true),
    (Expr.app f bc, Expr.app f c, true), (c, d, false), (s, s1, false)]
  for ((left, right, expected), i) in cases.zipIdx do
    for term in [left, right] do
      match Kernel.check env {} term with
        | .ok _ => pure ()
        | .error _ => throwError "ill-typed mixed conversion case {i}"
    let equal ← match Kernel.isDefEq env {} left right with
      | .ok result => pure result
      | .error _ => throwError "kernel conversion failed at case {i}"
    unless equal == expected do throwError "unexpected Lean result at case {i}"
    liftIO <| IO.println s!"{i} {if equal then "E" else "N"}"

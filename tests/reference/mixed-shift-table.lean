import Lean

open Lean

-- A small independent oracle for shifts through constant-bearing syntax.
-- This observes syntax only; it does not assert that the expressions typecheck.
partial def renderMixedShift : Expr → String
  | .sort .zero => "S "
  | .bvar i => s!"V {i} "
  | .const `c [.param `u] => "C "
  | .app f a => "A " ++ renderMixedShift f ++ renderMixedShift a
  | .lam _ d b _ => "L " ++ renderMixedShift d ++ renderMixedShift b
  | .forallE _ d b _ => "P " ++ renderMixedShift d ++ renderMixedShift b
  | _ => "UNSUPPORTED "

def main : IO Unit := do
  let s := Expr.sort .zero
  let c := Expr.const `c [.param `u]
  let v0 := Expr.bvar 0
  let v1 := Expr.bvar 1
  let v2 := Expr.bvar 2
  let cases := [c, Expr.app c v0,
    Expr.lam `x c (Expr.app v0 (Expr.app c v1)) .default,
    Expr.forallE `x (Expr.app c v0) (Expr.app v1 c) .default,
    Expr.lam `x s (Expr.lam `y c (Expr.app v2 (Expr.app v1 c)) .default) .default]
  for (expression, index) in cases.zipIdx do
    for cutoff in [0:3] do
      for amount in [0:3] do
        IO.println s!"{index} {cutoff} {amount} {renderMixedShift (expression.liftLooseBVars cutoff amount)}"

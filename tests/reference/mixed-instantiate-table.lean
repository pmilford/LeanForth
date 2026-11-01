import Lean
open Lean

-- Syntax oracle only: terms deliberately include open and untyped expressions.
partial def renderMixedInst : Expr → String
  | .sort .zero => "S "
  | .sort (.param `u) => "U "
  | .const `c [.param `u] => "C "
  | .const `d [.zero] => "D "
  | .bvar i => s!"V {i} "
  | .app f a => "A " ++ renderMixedInst f ++ renderMixedInst a
  | .lam _ d b _ => "L " ++ renderMixedInst d ++ renderMixedInst b
  | .forallE _ d b _ => "P " ++ renderMixedInst d ++ renderMixedInst b
  | _ => "UNSUPPORTED "

def main : IO Unit := do
  let s := Expr.sort .zero
  let u := Expr.sort (.param `u)
  let c := Expr.const `c [.param `u]
  let d := Expr.const `d [.zero]
  let v0 := Expr.bvar 0
  let v1 := Expr.bvar 1
  let v2 := Expr.bvar 2
  let cases := [c, Expr.app c v0,
    Expr.lam `x d (Expr.app v0 (Expr.app c v1)) .default,
    Expr.forallE `x (Expr.app d v0) (Expr.app v1 c) .default,
    Expr.lam `x u (Expr.lam `y c (Expr.app v2 (Expr.app v1 d)) .default) .default,
    Expr.app v0 (Expr.lam `x d (Expr.app v1 (Expr.app v0 v1)) .default)]
  let replacements := [v0, Expr.app d v0, c, u,
    Expr.lam `x s (Expr.app v0 (Expr.app c v1)) .default]
  for (expression, index) in cases.zipIdx do
    for (replacement, replacementIndex) in replacements.zipIdx do
      IO.println s!"{index} {replacementIndex} {renderMixedInst (expression.instantiate1 replacement)}"

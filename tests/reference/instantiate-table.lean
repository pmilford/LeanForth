import Lean

open Lean

partial def renderInstantiationTerm : Expr → String
  | .sort .zero => "S 0 "
  | .bvar index => s!"V {index} "
  | .app fn arg => "A " ++ renderInstantiationTerm fn ++ renderInstantiationTerm arg
  | .lam _ domain body _ => "L " ++ renderInstantiationTerm domain ++ renderInstantiationTerm body
  | .forallE _ domain body _ => "P " ++ renderInstantiationTerm domain ++ renderInstantiationTerm body
  | _ => "UNSUPPORTED "

def main : IO Unit := do
  let prop := Expr.sort .zero
  let var0 := Expr.bvar 0
  let var1 := Expr.bvar 1
  let var2 := Expr.bvar 2
  let cases := [var0, var1,
    Expr.lam `x prop (Expr.app var0 var1) .default,
    Expr.forallE `x var0 (Expr.app var1 var0) .default,
    Expr.lam `x prop (Expr.lam `y prop (Expr.app var2 var1) .default) .default]
  let replacements := [var0, var1, var2, prop, Expr.lam `x prop var0 .default]
  for (expression, index) in cases.zipIdx do
    for (replacement, replacementIndex) in replacements.zipIdx do
      let result := expression.instantiate1 replacement
      IO.println s!"{index} {replacementIndex} {renderInstantiationTerm result}"

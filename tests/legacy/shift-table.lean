import Lean

open Lean

partial def renderShiftTerm : Expr → String
  | .sort .zero => "S 0 "
  | .bvar index => s!"V {index} "
  | .app fn arg => "A " ++ renderShiftTerm fn ++ renderShiftTerm arg
  | .lam _ domain body _ => "L " ++ renderShiftTerm domain ++ renderShiftTerm body
  | .forallE _ domain body _ => "P " ++ renderShiftTerm domain ++ renderShiftTerm body
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
  for (expression, index) in cases.zipIdx do
    for cutoff in [0:4] do
      for amount in [0:4] do
        let shifted := expression.liftLooseBVars cutoff amount
        IO.println s!"{index} {cutoff} {amount} {renderShiftTerm shifted}"

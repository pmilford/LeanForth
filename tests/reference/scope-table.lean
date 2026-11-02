import Lean

open Lean

def main : IO Unit := do
  let prop := Expr.sort .zero
  let base := #[prop, Expr.bvar 0, Expr.bvar 1, Expr.bvar 2]
  let mut cases := base
  for tag in [0:3] do
    for left in [0:4] do
      for right in [0:4] do
        let first := base[left]!
        let second := base[right]!
        let expression := match tag with
          | 0 => Expr.app first second
          | 1 => Expr.lam `x first second .default
          | _ => Expr.forallE `x first second .default
        cases := cases.push expression
  for index in [0:12] do
    cases := cases.push (Expr.lam `x prop cases[index + 4]! .default)
  for (expression, index) in cases.toList.zipIdx do
    let status : Nat := if expression.hasLooseBVars then 1 else 0
    IO.println s!"{index} {status} "

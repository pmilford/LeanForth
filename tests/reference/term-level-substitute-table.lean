import Lean

open Lean

-- Emit a prefix syntax tree with concrete normalized Sort levels. Binder
-- names are presentation only; every supported constructor is emitted.
partial def shape (e : Expr) : Except String (List Nat) := do
  match e with
  | .sort level =>
    let some n := level.normalize.toNat | throw "non-concrete level"
    pure [1, n]
  | .bvar n => pure [2, n]
  | .app f x => pure ([3] ++ (← shape f) ++ (← shape x))
  | .lam _ d b _ => pure ([4] ++ (← shape d) ++ (← shape b))
  | .forallE _ d b _ => pure ([5] ++ (← shape d) ++ (← shape b))
  | _ => throw "unsupported expression"

def main : IO Unit := do
  let u := Level.param `u
  let v := Level.param `v
  let expr := Expr.forallE `A (.sort (.max u (.succ v)))
    (.lam `x (.sort u) (.app (.bvar 0) (.sort (.imax v u))) .default) .default
  let replacements := [[v, u], [.succ v, .max u v], [v, .succ u]]
  for (args, caseNo) in replacements.zipIdx do
    let result := expr.instantiateLevelParams [`u, `v] args
    for a in [0:4] do
      for b in [0:4] do
        let concrete := result.instantiateLevelParams [`u, `v] [Level.ofNat a, Level.ofNat b]
        let .ok tokens := shape concrete | throw <| IO.userError "unsupported output"
        let row := [caseNo, a, b] ++ tokens
        IO.println <| String.intercalate " " (row.map toString)

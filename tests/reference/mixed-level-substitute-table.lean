import Lean
open Lean

-- Observes simultaneous universe substitution in expressions and constants.
-- It is a syntax oracle, not a declaration checker.
def renderLevel (level : Level) : String :=
  match level.normalize.toNat with
  | some n => s!"{n} "
  | none => "UNSUPPORTED "

partial def renderExpr : Expr → String
  | .sort l => "T " ++ renderLevel l
  | .const `f levels => "C " ++ toString levels.length ++ " " ++
      String.join (levels.map renderLevel)
  | .const `g levels => "D " ++ toString levels.length ++ " " ++
      String.join (levels.map renderLevel)
  | .bvar i => s!"V {i} "
  | .app f a => "A " ++ renderExpr f ++ renderExpr a
  | .lam _ d b _ => "L " ++ renderExpr d ++ renderExpr b
  | .forallE _ d b _ => "P " ++ renderExpr d ++ renderExpr b
  | _ => "UNSUPPORTED "

def main : IO Unit := do
  let u := Level.param `u
  let v := Level.param `v
  let expression := Expr.forallE `A (.sort (.max u (.succ v)))
    (.lam `x (.sort u)
      (.app (.const `f [u, .imax v u]) (.app (.const `g [v]) (.bvar 0))) .default) .default
  let actuals := [[v, u], [.succ v, .max u v], [v, .succ u]]
  for (levels, i) in actuals.zipIdx do
    let result := expression.instantiateLevelParams [`u, `v] levels
    for a in [0:3] do
      for b in [0:3] do
        let concrete := result.instantiateLevelParams [`u, `v] [Level.ofNat a, Level.ofNat b]
        IO.println s!"{i} {a} {b} {renderExpr concrete}"

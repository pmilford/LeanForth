import Lean
import LeanForthPolyIdentity

open Lean Elab Command

-- Only syntax shapes are compared; this is not a LeanForth declaration check.
partial def fixtureShape (e : Expr) : Except String String := do
  match e with
  | .sort l =>
    let some n := l.normalize.toNat | throw "non-concrete level"
    pure s!"s{n}"
  | .bvar n => pure s!"v{n}"
  | .app f a => pure s!"a({← fixtureShape f},{← fixtureShape a})"
  | .lam _ d b _ => pure s!"l({← fixtureShape d},{← fixtureShape b})"
  | .forallE _ d b _ => pure s!"p({← fixtureShape d},{← fixtureShape b})"
  | _ => throw "unsupported expression"

run_cmd do
  let some (.thmInfo info) := (← getEnv).find? `poly_identity
    | throwError "missing theorem"
  unless info.levelParams.length == 1 do throwError "unexpected arity"
  for n in [0:2] do
    let type := info.type.instantiateLevelParams info.levelParams [Level.ofNat n]
    let .ok shape := fixtureShape type | throwError "unsupported shape"
    liftIO <| IO.println s!"{n} {shape}"

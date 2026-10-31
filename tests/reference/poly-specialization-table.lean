import Lean
import LeanForthPolyIdentity

open Lean Elab Command

-- Canonicalize only the supported core syntax, ignoring binder display data.
-- Failing on other constructors keeps the comparison from silently omitting it.
partial def specializationShape (expression : Expr) : Except String String := do
  match expression with
  | .sort level =>
    let some value := level.normalize.toNat | throw "non-concrete universe"
    pure s!"s{value}"
  | .bvar index => pure s!"v{index}"
  | .app fn arg => pure s!"a({← specializationShape fn},{← specializationShape arg})"
  | .lam _ domain body _ => pure s!"l({← specializationShape domain},{← specializationShape body})"
  | .forallE _ domain body _ => pure s!"p({← specializationShape domain},{← specializationShape body})"
  | _ => throw "unsupported expression constructor"

-- Ask Lean's kernel to check concrete substitutions of the actual exported
-- theorem and reject a candidate whose value is the theorem's type instead.
run_cmd do
  let env ← getEnv
  let some (.thmInfo info) := env.find? `poly_identity
    | throwError "missing polymorphic identity theorem"
  for level in [0:4] do
    let levels := [Level.ofNat level]
    let type := info.type.instantiateLevelParams info.levelParams levels
    let value := info.value.instantiateLevelParams info.levelParams levels
    for kind in [0:2] do
      let candidateValue := if kind == 0 then value else type
      let candidate : Declaration := .thmDecl {
        name := Name.mkSimple s!"LeanForthSpecialized{level}_{kind}"
        levelParams := [], type, value := candidateValue
      }
      let outcome := match env.toKernelEnv.addDeclCore 1000000 1000 candidate none with
        | .ok _ => 0
        | .error _ => 1
      let .ok typeShape := specializationShape type | throwError "cannot encode type"
      let .ok valueShape := specializationShape candidateValue | throwError "cannot encode value"
      liftIO <| IO.println s!"{level} {kind} {outcome} {typeShape} {valueShape}"

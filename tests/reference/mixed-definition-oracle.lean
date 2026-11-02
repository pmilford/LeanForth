import Lean
open Lean Elab Command

-- Lean-only declaration checks for the same narrow mixed-definition shape.
-- The Forth side must not treat its assumed candidate metadata as checked.
run_cmd do
  let initial := (← getEnv).toKernelEnv
  let u := Level.param `u
  let sortU := Expr.sort u
  let expected := Expr.forallE `A sortU
    (Expr.forallE `x (.bvar 0) (.bvar 1) .default) .default
  let identity := Expr.lam `A sortU
    (Expr.lam `x (.bvar 0) (.bvar 0) .default) .default
  let mkDef (name : Name) (type value : Expr) : Declaration :=
    .defnDecl { name, levelParams := [`u], type, value, hints := .abbrev, safety := .safe }
  let idName := `LeanForthMixedDefinition.id
  let env ← match initial.addDeclCore 1000000 1000 (mkDef idName expected identity) none with
    | .ok env => pure env
    | .error _ => throwError "Lean rejected identity dependency"
  let body (lastArg : Nat) := Expr.lam `A sortU
    (Expr.lam `x (.bvar 0)
      (.app (.app (.const idName [u]) (.bvar 1)) (.bvar lastArg)) .default) .default
  let wrongType := Expr.forallE `A sortU
    (Expr.forallE `x (.bvar 0) (.sort u) .default) .default
  let missingBody := Expr.lam `A sortU
    (Expr.lam `x (.bvar 0)
      (.app (.app (.const `LeanForthMixedDefinition.missing [u]) (.bvar 1)) (.bvar 0)) .default) .default
  for (name, ty, val, shouldAccept) in
      [(`LeanForthMixedDefinition.good, expected, body 0, true),
       (`LeanForthMixedDefinition.wrongArg, expected, body 1, false),
       (`LeanForthMixedDefinition.wrongType, wrongType, body 0, false),
       (`LeanForthMixedDefinition.missingRef, expected, missingBody, false)] do
    match env.addDeclCore 1000000 1000 (mkDef name ty val) none, shouldAccept with
    | .ok _, true => pure ()
    | .error _, false => pure ()
    | _, _ => throwError "unexpected Lean declaration outcome for {name}"

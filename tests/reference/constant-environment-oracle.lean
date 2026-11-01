import Lean

-- Direct kernel declaration tests. These are reference observations, not a
-- LeanForth implementation, declaration importer, or theorem acceptance path.
open Lean Elab Command

run_cmd do
  let initial := (← getEnv).toKernelEnv
  let u := Level.param `u
  let target := Expr.forallE `A (Expr.sort u)
    (Expr.forallE `x (Expr.bvar 0) (Expr.bvar 1) .default) .default
  let identity := Expr.lam `A (Expr.sort u)
    (Expr.lam `x (Expr.bvar 0) (Expr.bvar 0) .default) .default
  let mkDef (name : Name) (params : List Name) (type value : Expr) : Declaration :=
    .defnDecl { name, levelParams := params, type, value, hints := .abbrev, safety := .safe }
  let idName := `LeanForthConstants.Identity
  let idDecl := mkDef idName [`u] target identity
  let wrongBody := Expr.lam `A (.sort u)
    (Expr.forallE `x (.bvar 0) (.bvar 1) .default) .default
  match initial.addDeclCore 1000000 1000
      (mkDef `LeanForthConstants.WrongBody [`u] target wrongBody) none with
    | .error _ => pure ()
    | .ok _ => throwError "kernel accepted a Pi in place of the identity body"
  let env ← match initial.addDeclCore 1000000 1000 idDecl none with
    | .ok env => pure env
    | .error _ => throwError "kernel rejected polymorphic identity"
  let expectValid (label : String) (decl : Declaration) : CommandElabM Unit := do
    match env.addDeclCore 1000000 1000 decl none with
    | .ok _ => pure ()
    | .error _ => throwError "kernel rejected valid constant case: {label}"
  let expectInvalid (label : String) (decl : Declaration) : CommandElabM Unit := do
    match env.addDeclCore 1000000 1000 decl none with
    | .error _ => pure ()
    | .ok _ => throwError "kernel accepted invalid constant case: {label}"
  -- The alias checks the value using the prior environment, not its own name.
  expectValid "polymorphic alias" <| mkDef `LeanForthConstants.Alias [`u] target (.const idName [u])
  -- Reconstruct the fixturePoly shape: lambda A, lambda x, Identity A x.
  -- The prior environment, not the candidate itself, supplies Identity.
  let dependencyBody := Expr.lam `A (.sort u)
    (Expr.lam `x (.bvar 0)
      (.app (.app (.const idName [u]) (.bvar 1)) (.bvar 0)) .default) .default
  let wrongDependencyBody := Expr.lam `A (.sort u)
    (Expr.lam `x (.bvar 0)
      (.app (.app (.const idName [u]) (.bvar 1)) (.bvar 1)) .default) .default
  expectValid "definition with constant application" <|
    mkDef `LeanForthConstants.Dependent [`u] target dependencyBody
  expectInvalid "wrong constant argument under binders" <|
    mkDef `LeanForthConstants.DependentWrong [`u] target wrongDependencyBody
  let zeroTarget := target.instantiateLevelParams [`u] [.zero]
  expectValid "monomorphic specialization" <|
    mkDef `LeanForthConstants.Specialized [] zeroTarget (.const idName [.zero])
  expectInvalid "too few levels" <|
    mkDef `LeanForthConstants.TooFew [`u] target (.const idName [])
  expectInvalid "too many levels" <|
    mkDef `LeanForthConstants.TooMany [`u] target (.const idName [u, u])
  expectInvalid "unknown dependency" <|
    mkDef `LeanForthConstants.Unknown [`u] target (.const `LeanForthConstants.Missing [u])
  expectInvalid "self dependency" <|
    mkDef `LeanForthConstants.Self [`u] target (.const `LeanForthConstants.Self [u])
  expectInvalid "duplicate name" idDecl
  expectInvalid "unbound universe parameter" <|
    mkDef `LeanForthConstants.Unbound [`u] target (.const idName [.param `v])
  let v := Level.param `v
  -- Build explicitly so that binders have the same order in type and value.
  let twoType := Expr.forallE `A (Expr.sort u)
    (Expr.forallE `B (Expr.sort v)
      (Expr.forallE `x (Expr.bvar 1) (Expr.bvar 2) .default) .default) .default
  let twoValue := Expr.lam `A (Expr.sort u)
    (Expr.lam `B (Expr.sort v)
      (Expr.lam `x (Expr.bvar 1) (Expr.bvar 0) .default) .default) .default
  let twoName := `LeanForthConstants.TwoUniverses
  let twoEnv ← match env.addDeclCore 1000000 1000 (mkDef twoName [`u, `v] twoType twoValue) none with
    | .ok env => pure env
    | .error _ => throwError "kernel rejected two-universe definition"
  let swappedType := twoType.instantiateLevelParams [`u, `v] [v, u]
  let swapped := mkDef `LeanForthConstants.Swapped [`u, `v] swappedType (.const twoName [v, u])
  match twoEnv.addDeclCore 1000000 1000 swapped none with
    | .ok _ => pure ()
    | .error _ => throwError "kernel rejected swapped universe substitution"
  let wrongOrder := mkDef `LeanForthConstants.WrongOrder [`u, `v] swappedType (.const twoName [u, v])
  match twoEnv.addDeclCore 1000000 1000 wrongOrder none with
    | .error _ => pure ()
    | .ok _ => throwError "kernel accepted unswapped universe arguments"
  let nested := Level.max u (.imax v (.succ u))
  let nestedType := target.instantiateLevelParams [`u] [nested]
  expectValid "nested universe expression" <|
    mkDef `LeanForthConstants.Nested [`u, `v] nestedType (.const idName [nested])

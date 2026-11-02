import Lean

open Lean Elab Command

-- Kernel outcomes for the declaration pairs of
-- tests/core/mixed-definition-table.fs. Each row is
-- "section index theorem definition": 0 when Lean's kernel accepts the pair
-- as a theorem (claim must be a Prop) or as a definition, 1 when it rejects
-- it. Section 0 has five closed pairs, section 1 four pairs with universe
-- parameter u that use an already checked `id`. Finite differential
-- evidence only; nothing here is a LeanForth proof certificate.
def outcome (env : Kernel.Environment) (decl : Declaration) : Nat :=
  match env.addDeclCore 1000000 1000 decl none with
  | .ok _ => 0
  | .error _ => 1

def emitPair (env : Kernel.Environment) (part index : Nat) (params : List Name)
    (type value : Expr) : CommandElabM Unit := do
  let name := Name.mkSimple s!"LeanForthDefinitionTable{part}_{index}"
  let asTheorem := outcome env (.thmDecl { name, levelParams := params, type, value })
  let defn : DefinitionVal :=
    { name, levelParams := params, type, value, hints := .abbrev, safety := .safe }
  let asDefinition := outcome env (.defnDecl defn)
  liftIO <| IO.println s!"{part} {index} {asTheorem} {asDefinition}"

run_cmd do
  let initial := (← getEnv).toKernelEnv
  let prop := Expr.sort .zero
  let pi := fun a b => Expr.forallE `x a b .default
  let lam := fun a b => Expr.lam `x a b .default
  let target := pi prop (pi (.bvar 0) (.bvar 1))
  let identity := lam prop (lam (.bvar 0) (.bvar 0))
  let wrong := lam prop (lam (.bvar 0) (.bvar 1))
  let betaDomain := Expr.app (lam (.sort (.succ .zero)) (.bvar 0)) prop
  let betaTarget := pi betaDomain (pi (.bvar 0) (.bvar 1))
  let closed := [(target, identity), (target, wrong), (identity, identity),
    (Expr.sort (.succ .zero), prop), (betaTarget, identity)]
  for ((type, value), index) in closed.zipIdx do
    emitPair initial 0 index [] type value
  let u := Level.param `u
  let sortU := Expr.sort u
  let expected := pi sortU (pi (.bvar 0) (.bvar 1))
  let idName := `LeanForthDefinitionTable.id
  let idValue := lam sortU (lam (.bvar 0) (.bvar 0))
  let idDefn : DefinitionVal :=
    { name := idName, levelParams := [`u], type := expected, value := idValue,
      hints := .abbrev, safety := .safe }
  let env ← match initial.addDeclCore 1000000 1000 (.defnDecl idDefn) none with
    | .ok env => pure env
    | .error _ => throwError "Lean rejected the id dependency"
  let body (lastArg : Nat) (head : Name) := lam sortU (lam (.bvar 0)
    (.app (.app (.const head [u]) (.bvar 1)) (.bvar lastArg)))
  let wrongType := pi sortU (pi (.bvar 0) sortU)
  let missingName := `LeanForthDefinitionTable.missing
  let polymorphic := [(expected, body 0 idName), (expected, body 1 idName),
    (wrongType, body 0 idName), (expected, body 0 missingName)]
  for ((type, value), index) in polymorphic.zipIdx do
    emitPair env 1 index [`u] type value

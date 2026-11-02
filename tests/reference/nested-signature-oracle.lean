import Lean
open Lean Elab Command

-- Kernel-only reference observations. No declaration from this environment is
-- registered or accepted by LeanForth; there are no extra reference axioms.
run_cmd do
  let base := (← getEnv).toKernelEnv
  let u := Level.param `u
  let identityType := Expr.forallE `A (.sort u)
    (Expr.forallE `x (.bvar 0) (.bvar 1) .default) .default
  let identityValue := Expr.lam `A (.sort u)
    (Expr.lam `x (.bvar 0) (.bvar 0) .default) .default
  let mkDef (name : Name) (type value : Expr) : Declaration :=
    .defnDecl { name, levelParams := [`u], type, value, hints := .abbrev, safety := .safe }
  let idName := `LeanForthNestedSignature.id
  let env ← match base.addDeclCore 1000000 1000 (mkDef idName identityType identityValue) none with
    | .ok env => pure env
    | .error _ => throwError "kernel rejected identity dependency"
  -- Inside two binders A and x, identity at level u+1 maps Sort u to itself.
  -- Its application to A is a type that reduces to A. The constant appears
  -- inside the type of Eq, rather than only inside the candidate value.
  let idType := Expr.app (Expr.app (.const idName [.succ u]) (.sort u)) (.bvar 1)
  let equality := Expr.app (Expr.app (Expr.app (.const `Eq [u]) idType) (.bvar 0)) (.bvar 0)
  let target := Expr.forallE `A (.sort u)
    (Expr.forallE `x (.bvar 0) equality .default) .default
  let refl := Expr.app (Expr.app (.const `Eq.refl [u]) (.bvar 1)) (.bvar 0)
  let value := Expr.lam `A (.sort u) (Expr.lam `x (.bvar 0) refl .default) .default
  match env.addDeclCore 1000000 1000 (mkDef `LeanForthNestedSignature.good target value) none with
    | .ok _ => pure ()
    | .error _ => throwError "kernel rejected nested-constant type"
  let wrongType := Expr.app (Expr.app (.const idName [u]) (.sort u)) (.bvar 1)
  let wrongEq := Expr.app (Expr.app (Expr.app (.const `Eq [u]) wrongType) (.bvar 0)) (.bvar 0)
  let wrong := Expr.forallE `A (.sort u)
    (Expr.forallE `x (.bvar 0) wrongEq .default) .default
  match env.addDeclCore 1000000 1000 (mkDef `LeanForthNestedSignature.bad wrong value) none with
    | .error _ => pure ()
    | .ok _ => throwError "kernel accepted the wrong universe in nested type"

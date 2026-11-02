import Lean
open Lean Elab Command

-- Lean-only reference for dependency order. No result is imported as a
-- LeanForth declaration, theorem, or trusted assumption.
run_cmd do
  let initial := (← getEnv).toKernelEnv
  let u := Level.param `u
  let idName := `LeanForthChain.id
  let polyName := `LeanForthChain.poly
  let idType := Expr.forallE `A (.sort u)
    (Expr.forallE `x (.bvar 0) (.bvar 1) .default) .default
  let idValue := Expr.lam `A (.sort u)
    (Expr.lam `x (.bvar 0) (.bvar 0) .default) .default
  let mkDef (name : Name) (value : Expr) : Declaration :=
    .defnDecl { name, levelParams := [`u], type := idType, value, hints := .abbrev, safety := .safe }
  let polyValue := Expr.lam `A (.sort u)
    (Expr.lam `x (.bvar 0)
      (.app (.app (.const idName [u]) (.bvar 1)) (.bvar 0)) .default) .default
  let polyDecl := mkDef polyName polyValue
  match initial.addDeclCore 1000000 1000 polyDecl none with
    | .error _ => pure ()
    | .ok _ => throwError "Lean accepted a forward dependency"
  let afterId ← match initial.addDeclCore 1000000 1000 (mkDef idName idValue) none with
    | .ok env => pure env
    | .error _ => throwError "Lean rejected identity"
  let prop := Expr.sort .zero
  let claim := Expr.forallE `P prop
    (Expr.forallE `h (.bvar 0) (.bvar 1) .default) .default
  let proof (dependency : Name) (arg : Nat) := Expr.lam `P prop
    (Expr.lam `h (.bvar 0)
      (.app (.app (.const dependency [.zero]) (.bvar 1)) (.bvar arg)) .default) .default
  let mkTheorem (name : Name) (value : Expr) : Declaration :=
    .thmDecl { name, levelParams := [], type := claim, value }
  let direct := mkTheorem `LeanForthChain.direct (proof idName 0)
  match afterId.addDeclCore 1000000 1000 direct none with
    | .ok _ => pure ()
    | .error _ => throwError "Lean rejected theorem using identity directly"
  let valid := mkTheorem `LeanForthChain.use (proof polyName 0)
  match afterId.addDeclCore 1000000 1000 valid none with
    | .error _ => pure ()
    | .ok _ => throwError "Lean accepted a theorem before its dependency"
  let afterPoly ← match afterId.addDeclCore 1000000 1000 polyDecl none with
    | .ok env => pure env
    | .error _ => throwError "Lean rejected valid dependent definition"
  match afterPoly.addDeclCore 1000000 1000 valid none with
    | .ok _ => pure ()
    | .error _ => throwError "Lean rejected valid dependent theorem"
  match afterPoly.addDeclCore 1000000 1000
      (mkTheorem `LeanForthChain.bad (proof polyName 1)) none with
    | .error _ => pure ()
    | .ok _ => throwError "Lean accepted wrong theorem argument"
  -- addDeclCore returns a new environment. Failing a candidate cannot add it
  -- to the original snapshot, as demonstrated by the unchanged rejection.
  match afterId.addDeclCore 1000000 1000 valid none with
    | .error _ => pure ()
    | .ok _ => throwError "prior environment unexpectedly changed"

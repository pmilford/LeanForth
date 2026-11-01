import Lean

open Lean Elab Command

-- Kernel oracle for binders whose earlier variable types must be shifted
-- across later binders. Acceptance is for a closed declaration, not a claim
-- that an arbitrary external context is well formed.
run_cmd do
  let env := (← getEnv).toKernelEnv
  let sortOne := Expr.sort (.succ .zero)
  let expected := Expr.forallE `A sortOne
    (Expr.forallE `a (.bvar 0)
      (Expr.forallE `B sortOne
        (Expr.forallE `b (.bvar 0) (.bvar 3) .default) .default) .default) .default
  let mkValue (result : Nat) := Expr.lam `A sortOne
    (Expr.lam `a (.bvar 0)
      (Expr.lam `B sortOne
        (Expr.lam `b (.bvar 0) (.bvar result) .default) .default) .default) .default
  let mkDef (name : Name) (body : Expr) : Declaration := .defnDecl {
    name, levelParams := [], type := expected, value := body,
    hints := .abbrev, safety := .safe
  }
  match env.addDeclCore 1000000 1000 (mkDef `ContextOracle.Valid (mkValue 2)) none with
  | .ok _ => pure ()
  | .error _ => throwError "kernel rejected the valid shifted variable"
  match env.addDeclCore 1000000 1000 (mkDef `ContextOracle.Wrong (mkValue 0)) none with
  | .error _ => pure ()
  | .ok _ => throwError "kernel accepted a value from the wrong binder"
  -- A domain cannot refer to a future binder, or be an expression whose type
  -- is a function rather than a Sort. The rejection reason is not inspected.
  let badScope := Expr.forallE `x (.bvar 0) (.sort .zero) .default
  let notAType := Expr.lam `x sortOne (.bvar 0) .default
  let badDomain := Expr.forallE `x notAType (.sort .zero) .default
  for (name, badType) in [("scope", badScope), ("domain", badDomain)] do
    let decl : Declaration := .defnDecl {
      name := Name.mkSimple s!"ContextOracleBad_{name}", levelParams := [],
      type := badType, value := .sort .zero, hints := .abbrev, safety := .safe
    }
    match env.addDeclCore 1000000 1000 decl none with
    | .error _ => pure ()
    | .ok _ => throwError "kernel accepted invalid {name}"

import Lean

open Lean Elab Command

run_cmd do
  let env := (← getEnv).toKernelEnv
  let prop := Expr.sort .zero
  let target := Expr.forallE `P prop
    (Expr.forallE `proof (Expr.bvar 0) (Expr.bvar 1) .default) .default
  let identity := Expr.lam `P prop
    (Expr.lam `proof (Expr.bvar 0) (Expr.bvar 0) .default) .default
  let wrongBinder := Expr.lam `P prop
    (Expr.lam `proof (Expr.bvar 0) (Expr.bvar 1) .default) .default
  let valid : Declaration := .thmDecl {
    name := `LeanForthOracle.ValidIdentity
    levelParams := []
    type := target
    value := identity
  }
  let wrongValue : Declaration := .thmDecl {
    name := `LeanForthOracle.WrongValue
    levelParams := []
    type := target
    value := wrongBinder
  }
  let nonType : Declaration := .thmDecl {
    name := `LeanForthOracle.NonType
    levelParams := []
    type := identity
    value := identity
  }
  let nonProposition : Declaration := .thmDecl {
    name := `LeanForthOracle.NonProposition
    levelParams := []
    type := Expr.sort (.succ .zero)
    value := prop
  }
  let nonPropositionDefinition : Declaration := .defnDecl {
    name := `LeanForthOracle.TypeDefinition
    levelParams := []
    type := Expr.sort (.succ .zero)
    value := prop
    hints := .abbrev
    safety := .safe
  }
  match env.addDeclCore 1000000 1000 valid none with
    | .ok _ => pure ()
    | .error _ => throwError "Lean kernel rejected valid identity declaration"
  match env.addDeclCore 1000000 1000 wrongValue none with
    | .error _ => pure ()
    | .ok _ => throwError "Lean kernel accepted the wrong declared value"
  match env.addDeclCore 1000000 1000 nonType none with
    | .error _ => pure ()
    | .ok _ => throwError "Lean kernel accepted a non-type as declaration type"
  match env.addDeclCore 1000000 1000 nonProposition none with
    | .error _ => pure ()
    | .ok _ => throwError "Lean kernel accepted a non-proposition theorem"
  match env.addDeclCore 1000000 1000 nonPropositionDefinition none with
    | .ok _ => pure ()
    | .error _ => throwError "Lean kernel rejected a well-typed data definition"

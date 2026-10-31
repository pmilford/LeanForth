import Lean

open Lean Elab Command

partial def candidateShift (expression : Expr) (cutoff amount : Nat) : Except String Expr :=
  match expression with
  | .sort _ => .ok expression
  | .bvar index => .ok (.bvar (if index < cutoff then index else index + amount))
  | .app fn arg => do
      return .app (← candidateShift fn cutoff amount) (← candidateShift arg cutoff amount)
  | .lam name domain body info => do
      return .lam name (← candidateShift domain cutoff amount)
        (← candidateShift body (cutoff + 1) amount) info
  | .forallE name domain body info => do
      return .forallE name (← candidateShift domain cutoff amount)
        (← candidateShift body (cutoff + 1) amount) info
  | _ => .error "unsupported expression"

partial def candidateInstantiate (expression replacement : Expr) (depth : Nat) : Except String Expr :=
  match expression with
  | .sort _ => .ok expression
  | .bvar index =>
      if index < depth then .ok expression
      else if index == depth then candidateShift replacement 0 depth
      else .ok (.bvar (index - 1))
  | .app fn arg => do
      return .app (← candidateInstantiate fn replacement depth)
        (← candidateInstantiate arg replacement depth)
  | .lam name domain body info => do
      return .lam name (← candidateInstantiate domain replacement depth)
        (← candidateInstantiate body replacement (depth + 1)) info
  | .forallE name domain body info => do
      return .forallE name (← candidateInstantiate domain replacement depth)
        (← candidateInstantiate body replacement (depth + 1)) info
  | _ => .error "unsupported expression"

run_cmd do
  let prop := Expr.sort .zero
  let base := #[prop, Expr.bvar 0, Expr.bvar 1, Expr.bvar 2, Expr.bvar 3]
  let mut cases := base
  let mut replacements := base
  for first in base do
    for second in base do
      cases := cases.push (.app first second)
      cases := cases.push (.lam `x first second .default)
      cases := cases.push (.forallE `x first second .default)
      cases := cases.push (.lam `x prop (.app first second) .default)
      cases := cases.push (.forallE `x prop (.app first second) .default)
      cases := cases.push (.lam `outer prop (.lam `inner first second .default) .default)
      replacements := replacements.push (.app first second)
      replacements := replacements.push (.lam `x first second .default)
  unless cases.size == 155 && replacements.size == 55 do
    throwError "unexpected generated expression count"
  for expression in cases do
    for cutoff in [0:4] do
      for amount in [0:4] do
        match candidateShift expression cutoff amount with
          | .error reason => throwError "shift model rejected a supported case: {reason}"
          | .ok actual =>
            unless actual == expression.liftLooseBVars cutoff amount do
              throwError "shift model differs from Lean at cutoff {cutoff} amount {amount}"
    for replacement in replacements do
      match candidateInstantiate expression replacement 0 with
        | .error reason => throwError "instantiation model rejected a supported case: {reason}"
        | .ok actual =>
          unless actual == expression.instantiate1 replacement do
            throwError "instantiation model differs from Lean"
  match candidateShift (mkConst ``Nat) 0 1 with
    | .error _ => pure ()
    | .ok _ => throwError "shift model accepted an unsupported expression"
  match candidateInstantiate (mkConst ``Nat) prop 0 with
    | .error _ => pure ()
    | .ok _ => throwError "instantiation model accepted an unsupported expression"
  match candidateInstantiate (Expr.bvar 0) (mkConst ``Nat) 0 with
    | .error _ => pure ()
    | .ok _ => throwError "instantiation model accepted an unsupported replacement"

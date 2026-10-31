import Lean

open Lean Elab Command

/- This is an untrusted finite-test model, not a proof checker or theorem API.
   It uses Lean's instantiate1 and unbounded Nat, and its fuel limits recursion
   depth rather than total work. It must never confer LeanForth validity. -/

def modelLevel : Level → Option Nat
  | .zero => some 0
  | .succ level => (modelLevel level).map (· + 1)
  | _ => none

partial def modelWhnf (expression : Expr) (fuel : Nat) : Except String Expr := do
  if fuel == 0 then throw "exhausted"
  match expression with
  | .sort _ | .bvar _ | .lam .. | .forallE .. => return expression
  | .app fn arg =>
    let reduced ← modelWhnf fn (fuel - 1)
    match reduced with
    | .lam _ _ body _ => modelWhnf (body.instantiate1 arg) (fuel - 1)
    | _ => return .app reduced arg
  | _ => throw "unsupported"

partial def modelSameSyntax (left right : Expr) (fuel : Nat) : Except String Bool := do
  if fuel == 0 then throw "exhausted"
  match left, right with
  | .sort l, .sort r => return l == r
  | .bvar l, .bvar r => return l == r
  | .app lf la, .app rf ra =>
    if !(← modelSameSyntax lf rf (fuel - 1)) then return false
    modelSameSyntax la ra (fuel - 1)
  | .lam _ ld lb _, .lam _ rd rb _
  | .forallE _ ld lb _, .forallE _ rd rb _ =>
    if !(← modelSameSyntax ld rd (fuel - 1)) then return false
    modelSameSyntax lb rb (fuel - 1)
  | _, _ => return false

partial def modelCompare (left right : Expr) (fuel : Nat) : Except String Bool := do
  if fuel == 0 then throw "exhausted"
  let left ← modelWhnf left (fuel - 1)
  let right ← modelWhnf right (fuel - 1)
  match left, right with
  | .sort l, .sort r => return l == r
  | .bvar l, .bvar r => return l == r
  | .app lf la, .app rf ra =>
    if !(← modelCompare lf rf (fuel - 1)) then return false
    modelCompare la ra (fuel - 1)
  | .lam _ ld lb _, .lam _ rd rb _
  | .forallE _ ld lb _, .forallE _ rd rb _ =>
    if !(← modelSameSyntax ld rd (fuel - 1)) then return false
    modelCompare lb rb (fuel - 1)
  | _, _ => return false

partial def modelInfer (context : List Expr) (expression : Expr) (fuel : Nat) : Except String Expr := do
  if fuel == 0 then throw "exhausted"
  match expression with
  | .sort level =>
    match modelLevel level with
    | some number => return .sort (Level.ofNat (number + 1))
    | none => throw "unsupported"
  | .bvar index =>
    match context[index]? with
    | some domain => return domain.liftLooseBVars 0 (index + 1)
    | none => throw "invalid"
  | .forallE _ domain body _ =>
    let domainType ← modelWhnf (← modelInfer context domain (fuel - 1)) (fuel - 1)
    match domainType with
    | .sort u =>
      let left ← match modelLevel u with
        | some number => pure number
        | none => throw "unsupported"
      let bodyType ← modelWhnf (← modelInfer (domain :: context) body (fuel - 1)) (fuel - 1)
      match bodyType with
      | .sort v =>
        match modelLevel v with
        | some right => return .sort (Level.ofNat (if right == 0 then 0 else max left right))
        | none => throw "unsupported"
      | _ => throw "unknown"
    | _ => throw "unknown"
  | .lam name domain body info =>
    let domainType ← modelWhnf (← modelInfer context domain (fuel - 1)) (fuel - 1)
    match domainType with
    | .sort level =>
      if (modelLevel level).isNone then throw "unsupported"
      let bodyType ← modelInfer (domain :: context) body (fuel - 1)
      return .forallE name domain bodyType info
    | _ => throw "unknown"
  | .app fn arg =>
    let functionType ← modelWhnf (← modelInfer context fn (fuel - 1)) (fuel - 1)
    match functionType with
    | .forallE _ domain body _ =>
      let argumentType ← modelInfer context arg (fuel - 1)
      if !(← modelCompare argumentType domain (fuel - 1)) then throw "unknown"
      return body.instantiate1 arg
    | .sort _ => throw "invalid"
    | _ => throw "unknown"
  | _ => throw "unsupported"

run_cmd do
  let env ← getEnv
  let lctx : LocalContext := {}
  let prop := Expr.sort .zero
  let type0 := Expr.sort (.succ .zero)
  let identity := Expr.lam `P prop
    (Expr.lam `proof (Expr.bvar 0) (Expr.bvar 0) .default) .default
  let renamedIdentity := Expr.lam `Changed prop
    (Expr.lam `evidence (Expr.bvar 0) (Expr.bvar 0) .implicit) .implicit
  let wrongBinder := Expr.lam `P prop
    (Expr.lam `proof (Expr.bvar 0) (Expr.bvar 1) .default) .default
  let arrow := Expr.forallE `argument (Expr.bvar 2) (Expr.bvar 2) .default
  let composition := Expr.lam `A prop (Expr.lam `B prop (Expr.lam `C prop
    (Expr.lam `f arrow (Expr.lam `g arrow (Expr.lam `value (Expr.bvar 4)
      (Expr.app (Expr.bvar 1) (Expr.app (Expr.bvar 2) (Expr.bvar 0)))
      .default) .default) .default) .default) .default) .default
  let piProp := Expr.forallE `P prop (Expr.bvar 0) .default
  let piData := Expr.forallE `A type0 (Expr.bvar 0) .default
  let beta := Expr.app (Expr.lam `P type0 (Expr.bvar 0) .default) prop
  let betaDomainIdentity := Expr.lam `P beta
    (Expr.lam `proof (Expr.bvar 0) (Expr.bvar 0) .default) .default
  let valid := [prop, type0, identity, wrongBinder, composition, piProp, piData, beta]
  for expression in valid do
    let model ← match modelInfer [] expression 100 with
      | .ok result => pure result
      | .error reason => throwError "inference model failed on a valid case: {reason}"
    let oracle ← match Kernel.check env lctx expression with
      | .ok result => pure result
      | .error _ => throwError "Lean kernel rejected a positive inference case"
    match Kernel.isDefEq env lctx model oracle with
      | .ok true => pure ()
      | _ => throwError "model-inferred type differs from Lean"
  for expression in [Expr.bvar 0, Expr.app prop prop,
                     Expr.lam `x (Expr.bvar 0) (Expr.bvar 0) .default,
                     Expr.forallE `P prop (Expr.bvar 1) .default] do
    match modelInfer [] expression 100, Kernel.check env lctx expression with
      | .error _, .error _ => pure ()
      | _, _ => throwError "negative inference case did not fail both checks"
  match modelInfer [] identity 0 with
    | .error "exhausted" => pure ()
    | _ => throwError "model accepted a zero-budget inference"
  match modelInfer [] (mkConst ``Nat) 100 with
    | .error "unsupported" => pure ()
    | _ => throwError "model accepted an unsupported constant"
  match modelCompare beta prop 100 with
    | .ok true => pure ()
    | _ => throwError "model failed the beta-conversion case"
  match modelCompare identity renamedIdentity 100,
      Kernel.isDefEq env lctx identity renamedIdentity with
    | .ok true, .ok true => pure ()
    | _, _ => throwError "model did not ignore binder names and annotations"
  match modelCompare prop prop 0 with
    | .error "exhausted" => pure ()
    | _ => throwError "model accepted a zero-budget comparison"
  match modelCompare identity betaDomainIdentity 100,
      Kernel.isDefEq env lctx identity betaDomainIdentity with
    | .ok false, .ok true => pure ()
    | _, _ => throwError "different but convertible binder domains were not inconclusive"
  let betaDeclaredType := Expr.forallE `P beta
    (Expr.forallE `proof (Expr.bvar 0) (Expr.bvar 1) .default) .default
  let inferredIdentity ← match modelInfer [] identity 100 with
    | .ok inferred => pure inferred
    | .error reason => throwError "identity inference unexpectedly failed: {reason}"
  let betaDeclaration : Declaration := .thmDecl {
    name := `LeanForthOracle.BetaDomain
    levelParams := []
    type := betaDeclaredType
    value := identity
  }
  match modelCompare inferredIdentity betaDeclaredType 100,
      env.toKernelEnv.addDeclCore 1000000 1000 betaDeclaration none with
    | .ok false, .ok _ => pure ()
    | _, _ => throwError "Lean-valid beta-domain declaration did not remain inconclusive in the model"
  let dataIdentityType := Expr.forallE `A type0
    (Expr.forallE `x (Expr.bvar 0) (Expr.bvar 1) .default) .default
  let etaExpanded := Expr.lam `f dataIdentityType
    (Expr.lam `A type0 (Expr.lam `x (Expr.bvar 0)
      (Expr.app (Expr.app (Expr.bvar 2) (Expr.bvar 1)) (Expr.bvar 0)) .default) .default)
    .default
  let etaContracted := Expr.lam `f dataIdentityType (Expr.bvar 0) .default
  match modelCompare etaExpanded etaContracted 100, Kernel.isDefEq env lctx etaExpanded etaContracted with
    | .ok false, .ok true => pure ()
    | _, _ => throwError "model failed to report unknown for Lean function eta"
  let mismatchedArgument := Expr.app (Expr.lam `P prop (Expr.bvar 0) .default) prop
  match modelInfer [] mismatchedArgument 100, Kernel.check env lctx mismatchedArgument with
    | .error "unknown", .error _ => pure ()
    | _, _ => throwError "model did not conservatively handle a mismatched argument"
  let invalidDomain := Expr.forallE `x identity (Expr.bvar 1) .default
  match modelInfer [] invalidDomain 100, Kernel.check env lctx invalidDomain with
    | .error "unknown", .error _ => pure ()
    | _, _ => throwError "model examined a body under an invalid binder domain"
  let base := #[prop, type0, Expr.bvar 0, Expr.bvar 1, Expr.bvar 2]
  let mut generated := base
  for first in base do
    for second in base do
      generated := generated.push (.app first second)
      generated := generated.push (.lam `x first second .default)
      generated := generated.push (.forallE `x first second .default)
      generated := generated.push (.lam `outer prop (.lam `inner first second .default) .default)
  unless generated.size == 105 do
    throwError "unexpected generated inference case count"
  let mut bothAccepted : Nat := 0
  let mut bothFailed : Nat := 0
  let mut modelInconclusive : Nat := 0
  for expression in generated do
    match modelInfer [] expression 100, Kernel.check env lctx expression with
      | .ok inferred, .ok oracle =>
        match Kernel.isDefEq env lctx inferred oracle with
          | .ok true => bothAccepted := bothAccepted + 1
          | _ => throwError "generated case inferred a different type from Lean"
      | .ok _, .error _ => throwError "model inferred a type for a Lean-rejected term"
      | .error _, .error _ => bothFailed := bothFailed + 1
      | .error _, .ok _ => modelInconclusive := modelInconclusive + 1
  unless bothAccepted != 0 && bothFailed != 0 do
    throwError "generated inference cases did not exercise both outcomes"
  logInfo m!"Untrusted inference model: {bothAccepted} matched, {bothFailed} both failed, {modelInconclusive} model-inconclusive."

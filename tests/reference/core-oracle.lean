import Lean

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let proposition := Expr.sort .zero
  let propositionToProposition := Expr.forallE `P proposition
    (Expr.forallE `proof (Expr.bvar 0) (Expr.bvar 1) .default) .default
  let identity := Expr.lam `P proposition
    (Expr.lam `proof (Expr.bvar 0) (Expr.bvar 0) .default) .default
  let renamedIdentity := Expr.lam `Renamed proposition
    (Expr.lam `evidence (Expr.bvar 0) (Expr.bvar 0) .implicit) .implicit
  let wrongBinder := Expr.lam `P proposition
    (Expr.lam `proof (Expr.bvar 0) (Expr.bvar 1) .default) .default
  let invalidApplication := Expr.app proposition proposition
  let sortOne := Expr.sort (.succ .zero)
  let sortTwo := Expr.sort (.succ (.succ .zero))
  let betaTerm := Expr.app (Expr.lam `P sortOne (Expr.bvar 0) .default) proposition
  let betaDomainIdentity := Expr.lam `P betaTerm
    (Expr.lam `proof (Expr.bvar 0) (Expr.bvar 0) .default) .default
  let quantifiedProposition := Expr.forallE `P proposition (Expr.bvar 0) .default
  let quantifiedData := Expr.forallE `A sortOne (Expr.bvar 0) .default
  let dependentBeta := Expr.app
    (Expr.lam `A sortOne (Expr.lam `x (Expr.bvar 0) (Expr.bvar 0) .default) .default)
    proposition
  let dependentBetaResult := Expr.lam `x proposition (Expr.bvar 0) .default
  let dataIdentityType := Expr.forallE `A sortOne
    (Expr.forallE `x (Expr.bvar 0) (Expr.bvar 1) .default) .default
  let etaExpanded := Expr.lam `f dataIdentityType
    (Expr.lam `A sortOne (Expr.lam `x (Expr.bvar 0)
      (Expr.app (Expr.app (Expr.bvar 2) (Expr.bvar 1)) (Expr.bvar 0)) .default) .default)
    .default
  let etaContracted := Expr.lam `f dataIdentityType (Expr.bvar 0) .default
  let firstProof := Expr.lam `P proposition
    (Expr.lam `p (Expr.bvar 0)
      (Expr.lam `q (Expr.bvar 1) (Expr.bvar 1) .default) .default) .default
  let secondProof := Expr.lam `P proposition
    (Expr.lam `p (Expr.bvar 0)
      (Expr.lam `q (Expr.bvar 1) (Expr.bvar 0) .default) .default) .default
  let emptyContext : LocalContext := {}
  match Kernel.check env emptyContext proposition with
    | .ok result =>
      match Kernel.isDefEq env emptyContext result sortOne with
        | .ok true => pure ()
        | _ => throwError "kernel inferred the wrong type for Sort 0"
    | .error _ => throwError "kernel rejected Sort 0"
  match Kernel.isDefEq env emptyContext sortOne sortTwo with
    | .ok false => pure ()
    | _ => throwError "distinct concrete sorts unexpectedly matched"
  for (expression, expectedSort) in [(quantifiedProposition, proposition),
                                     (quantifiedData, sortTwo)] do
    let inferred ← match Kernel.check env emptyContext expression with
      | .ok result => pure result
      | .error _ => throwError "kernel rejected a quantified sort example"
    match Kernel.isDefEq env emptyContext inferred expectedSort with
      | .ok true => pure ()
      | _ => throwError "kernel inferred an unexpected quantified sort"
  match Kernel.check env emptyContext betaTerm with
    | .error _ => throwError "kernel rejected the beta-reduction example"
    | .ok _ => pure ()
  match Kernel.isDefEq env emptyContext betaTerm proposition with
    | .ok true => pure ()
    | _ => throwError "kernel did not recognize beta conversion"
  for expression in [dependentBeta, dependentBetaResult, etaExpanded, etaContracted,
                     firstProof, secondProof, renamedIdentity, betaDomainIdentity] do
    match Kernel.check env emptyContext expression with
      | .ok _ => pure ()
      | .error _ => throwError "kernel rejected a constructed conversion example"
  match Kernel.isDefEq env emptyContext dependentBeta dependentBetaResult with
    | .ok true => pure ()
    | _ => throwError "kernel did not substitute under a dependent binder"
  match Kernel.isDefEq env emptyContext etaExpanded etaContracted with
    | .ok true => pure ()
    | _ => throwError "kernel did not recognize function eta conversion"
  match Kernel.isDefEq env emptyContext firstProof secondProof with
    | .ok true => pure ()
    | _ => throwError "kernel did not recognize proof irrelevance"
  match Kernel.isDefEq env emptyContext identity renamedIdentity with
    | .ok true => pure ()
    | _ => throwError "kernel distinguished binder names or annotations"
  match Kernel.isDefEq env emptyContext identity betaDomainIdentity with
    | .ok true => pure ()
    | _ => throwError "kernel did not compare beta-equivalent binder domains"
  let identityType ← match Kernel.check env emptyContext identity with
    | .ok result => pure result
    | .error _ => throwError "kernel rejected the core identity term"
  match Kernel.isDefEq env emptyContext identityType propositionToProposition with
    | .ok true => pure ()
    | _ => throwError "kernel identity type did not match the expected type"
  let wrongType ← match Kernel.check env emptyContext wrongBinder with
    | .ok result => pure result
    | .error _ => throwError "kernel rejected the wrong-binder term itself"
  match Kernel.isDefEq env emptyContext wrongType propositionToProposition with
    | .ok false => pure ()
    | _ => throwError "wrong-binder term unexpectedly matched the identity type"
  match Kernel.check env emptyContext invalidApplication with
    | .error _ => pure ()
    | .ok _ => throwError "kernel accepted an application of a sort"
  match Kernel.isDefEq env emptyContext invalidApplication invalidApplication with
    | .ok true => pure ()
    | _ => throwError "expected equality to be distinct from type validation"
  match Kernel.check env emptyContext (Expr.bvar 0) with
    | .error _ => pure ()
    | .ok _ => throwError "kernel accepted an unbound variable"
  for expression in [Expr.lam `x (Expr.bvar 0) (Expr.bvar 0) .default,
                     Expr.forallE `P proposition (Expr.bvar 1) .default] do
    match Kernel.check env emptyContext expression with
      | .error _ => pure ()
      | .ok _ => throwError "kernel accepted a variable outside its binder scope"

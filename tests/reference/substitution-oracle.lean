import Lean

open Lean Elab Command

run_cmd do
  let proposition := Expr.sort .zero
  let freeAndBound := Expr.lam `x (Expr.bvar 0)
    (Expr.app (Expr.bvar 0) (Expr.bvar 1)) .default
  let lifted := Expr.lam `x (Expr.bvar 2)
    (Expr.app (Expr.bvar 0) (Expr.bvar 3)) .default
  unless (Expr.bvar 0).liftLooseBVars 0 2 == Expr.bvar 2 do
    throwError "lift failed for a loose variable"
  unless (Expr.bvar 0).liftLooseBVars 1 2 == Expr.bvar 0 do
    throwError "lift changed a variable below the cutoff"
  unless freeAndBound.liftLooseBVars 0 2 == lifted do
    throwError "lift did not preserve a nested binder or shift its domain"

  let replacement := Expr.bvar 1
  let capturesIfUnshifted := Expr.lam `x proposition
    (Expr.app (Expr.bvar 1) (Expr.bvar 0)) .default
  let avoidingCapture := Expr.lam `x proposition
    (Expr.app (Expr.bvar 2) (Expr.bvar 0)) .default
  unless capturesIfUnshifted.instantiate1 replacement == avoidingCapture do
    throwError "instantiation failed to shift the replacement under a binder"

  let outerReference := Expr.lam `x proposition
    (Expr.app (Expr.bvar 0) (Expr.bvar 2)) .default
  let loweredOuterReference := Expr.lam `x proposition
    (Expr.app (Expr.bvar 0) (Expr.bvar 1)) .default
  unless outerReference.instantiate1 (Expr.bvar 0) == loweredOuterReference do
    throwError "instantiation failed to lower an outer reference"

  let inDomainAndBody := Expr.lam `x (Expr.bvar 0) (Expr.bvar 1) .default
  let instantiatedBoth := Expr.lam `x proposition proposition .default
  unless inDomainAndBody.instantiate1 proposition == instantiatedBoth do
    throwError "instantiation did not visit both domain and body correctly"

  let boundOnly := Expr.lam `x proposition (Expr.bvar 0) .default
  unless boundOnly.instantiate1 (Expr.bvar 7) == boundOnly do
    throwError "instantiation changed a locally bound variable"

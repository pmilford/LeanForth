import Lean

/- Reference for the excluded symbolic inference draft, not a LeanForth proof.
   The Forth test inspects the unsimplified imax graph; Lean may simplify it. -/
open Lean Elab Command

run_cmd do
  let u := Level.param `u
  let sort := Expr.sort u
  let pi := Expr.forallE `A sort sort .default
  let expected := Level.imax (.succ u) (.succ u)
  match Kernel.check (← getEnv) {} pi with
  | .ok (.sort inferred) =>
      unless inferred.isEquiv expected do
        throwError "Lean inferred a non-equivalent universe for symbolic Pi"
  | .ok _ => throwError "Lean inferred a non-sort type for symbolic Pi"
  | .error _ => throwError "Lean rejected symbolic Pi"
  match Kernel.check (← getEnv) {} (.app sort sort) with
  | .ok _ => throwError "Lean accepted a sort applied as a function"
  | .error _ => pure ()
  liftIO <| IO.println "symbolic Pi universe equivalent; invalid application rejected"

import Lean
open Lean Elab Command

universe u
def mixedInferIdentity {A : Sort u} (x : A) : A := x

-- Direct kernel observation corresponding to the exported fixture's structure.
-- LeanForth's candidate metadata remains an untrusted assumption.
run_cmd do
  let env ← getEnv
  let level := Level.param `u
  let expected := Expr.forallE `A (.sort level)
    (Expr.forallE `x (.bvar 0) (.bvar 1) .default) .default
  let mkBody (arg : Nat) := Expr.lam `A (.sort level)
    (Expr.lam `x (.bvar 0)
      (.app (.app (.const `mixedInferIdentity [level]) (.bvar 1)) (.bvar arg)) .default) .default
  let inferred ← match Kernel.check env {} (mkBody 0) with
    | .ok type => pure type
    | .error _ => throwError "Lean rejected valid mixed inference fixture"
  match Kernel.isDefEq env {} inferred expected with
    | .ok true => pure ()
    | _ => throwError "Lean inferred a different type for the valid fixture"
  match Kernel.check env {} (mkBody 1) with
    | .error _ => pure ()
    | .ok _ => throwError "Lean accepted the wrong nested argument"
  -- The exported theorem-shaped fixture specializes identity at Prop.
  let prop := Expr.sort .zero
  let theoremType := Expr.forallE `P prop
    (Expr.forallE `h (.bvar 0) (.bvar 1) .default) .default
  let theoremBody (arg : Nat) := Expr.lam `P prop
    (Expr.lam `h (.bvar 0)
      (.app (.app (.const `mixedInferIdentity [.zero]) (.bvar 1)) (.bvar arg)) .default) .default
  let theoremInferred ← match Kernel.check env {} (theoremBody 0) with
    | .ok type => pure type
    | .error _ => throwError "Lean rejected valid theorem-shaped fixture"
  match Kernel.isDefEq env {} theoremInferred theoremType with
    | .ok true => pure ()
    | _ => throwError "Lean inferred a different theorem-shaped fixture type"
  match Kernel.check env {} (theoremBody 1) with
    | .error _ => pure ()
    | .ok _ => throwError "Lean accepted the wrong theorem argument"

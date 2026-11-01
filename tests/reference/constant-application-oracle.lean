import Lean

open Lean Elab Command

-- Direct Lean kernel observations for a previously added polymorphic identity.
-- This is an oracle, not a LeanForth proof or declaration acceptance test.
run_cmd do
  let env := (← getEnv).toKernelEnv
  let u := Level.param `u
  let type := Expr.forallE `A (.sort u)
    (Expr.forallE `x (.bvar 0) (.bvar 1) .default) .default
  let value := Expr.lam `A (.sort u)
    (Expr.lam `x (.bvar 0) (.bvar 0) .default) .default
  let mkDef (name : Name) (params : List Name) (type value : Expr) : Declaration :=
    .defnDecl { name, levelParams := params, type, value, hints := .abbrev, safety := .safe }
  let idName := `LeanForthApplicationOracle.Identity
  let env ← match env.addDeclCore 1000000 1000 (mkDef idName [`u] type value) none with
    | .ok env => pure env
    | .error _ => throwError "kernel rejected polymorphic identity"
  let prop := Expr.sort .zero
  let specializedType := Expr.forallE `x prop prop .default
  let function := Expr.const idName [.succ .zero]
  let valid := mkDef `LeanForthApplicationOracle.Valid [] specializedType (.app function prop)
  let proposition := Expr.forallE `P prop
    (Expr.forallE `h (.bvar 0) (.bvar 1) .default) .default
  let validTwo := mkDef `LeanForthApplicationOracle.ValidTwo [] prop
    (.app (.app function prop) proposition)
  let wrong := mkDef `LeanForthApplicationOracle.Wrong [] specializedType
    (.app function (.sort (.succ (.succ .zero))))
  let missing := mkDef `LeanForthApplicationOracle.Missing [] specializedType
    (.app (.const `LeanForthApplicationOracle.MissingName [.succ .zero]) prop)
  match env.addDeclCore 1000000 1000 valid none with
  | .ok _ => pure ()
  | .error _ => throwError "kernel rejected valid constant application"
  match env.addDeclCore 1000000 1000 validTwo none with
  | .ok _ => pure ()
  | .error _ => throwError "kernel rejected valid two-argument application"
  for (name, candidate) in [("wrong argument", wrong), ("missing constant", missing)] do
    match env.addDeclCore 1000000 1000 candidate none with
    | .error _ => pure ()
    | .ok _ => throwError "kernel accepted {name}"

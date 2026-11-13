/-
Binder names and binder information of Lean's own generated definitions
(plan row FE6; tests/front/constructions-init.sh): for every inductive
type T of Init, Lean's T.casesOn, T.recOn and T.ctorIdx as Lean's
environment holds them (getConstInfo, not an export, whose sharing of
terms equal up to binder names may show another term's), each binder of
the type and of the value in pre-order (binder, domain, body; function,
argument), as name:information with macro scopes erased
(eraseMacroScopes) and information 0 default, 1 implicit, 2 strict
implicit, 3 instance implicit; a letE as name:let. One line per
definition: name, a tab, the type's binders, a tab, the value's.
-/
import Lean
open Lean

def infoCode : BinderInfo → Nat
  | .default => 0
  | .implicit => 1
  | .strictImplicit => 2
  | .instImplicit => 3

def binderText (n : Name) (code : String) : String :=
  s!"{n.eraseMacroScopes.toString (escape := false)}:{code}"

partial def binders (e : Expr) (acc : Array String) : Array String :=
  match e with
  | .forallE n d b bi => binders b (binders d (acc.push (binderText n (toString (infoCode bi)))))
  | .lam n d b bi => binders b (binders d (acc.push (binderText n (toString (infoCode bi)))))
  | .letE n t v b _ => binders b (binders v (binders t (acc.push (binderText n "let"))))
  | .app f a => binders a (binders f acc)
  | .mdata _ e => binders e acc
  | .proj _ _ e => binders e acc
  | _ => acc

def line (n : Name) (ci : ConstantInfo) : Option String := do
  let v ← ci.value?
  let t := " ".intercalate (binders ci.type #[]).toList
  let w := " ".intercalate (binders v #[]).toList
  return s!"{n.toString (escape := false)}\t{t}\t{w}"

def generated (env : Environment) (n : Name) : Bool :=
  match n with
  | .str p s => (s == "casesOn" || s == "recOn" || s == "ctorIdx") &&
      (match env.find? p with | some (.inductInfo _) => true | _ => false)
  | _ => false

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Init }] {} (trustLevel := 1024)
  let mut out : Array String := #[]
  for (n, ci) in env.constants.toList do
    if generated env n then
      if let some l := line n ci then out := out.push l
  for l in out.qsort (· < ·) do IO.println l

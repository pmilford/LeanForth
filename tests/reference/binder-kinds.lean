/-
Binder information of every Init declaration's type as Lean's environment
holds it (plan S1, docs/design/S1_INTERFACE.md §4;
tests/front/check_binder_kinds.py compares it with the export's): each
binder of the type in pre-order (binder, domain, body; function,
argument; a let's type, value and body), as its information, 0 default,
1 implicit, 2 strict implicit, 3 instance implicit. One line per
declaration of an Init module: its name, a tab, the codes separated by
spaces. getConstInfo, not an export, whose sharing of terms equal up to
binder information may show another term's (review fe6a M1).
-/
import Lean
open Lean

def infoCode : BinderInfo → Nat
  | .default => 0
  | .implicit => 1
  | .strictImplicit => 2
  | .instImplicit => 3

partial def binders (e : Expr) (acc : Array Nat) : Array Nat :=
  match e with
  | .forallE _ d b bi => binders b (binders d (acc.push (infoCode bi)))
  | .lam _ d b bi => binders b (binders d (acc.push (infoCode bi)))
  | .letE _ t v b _ => binders b (binders v (binders t acc))
  | .app f a => binders a (binders f acc)
  | .mdata _ e => binders e acc
  | .proj _ _ e => binders e acc
  | _ => acc

def initModule? (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (`Init).isPrefixOf env.header.moduleNames[idx.toNat]!
  | none => false

#eval show CoreM Unit from do
  let env ← getEnv
  let mut lines : Array String := #[]
  for (n, ci) in env.constants.toList do
    if initModule? env n then
      let codes := " ".intercalate ((binders ci.type #[]).toList.map toString)
      lines := lines.push s!"{n.toString (escape := false)}\t{codes}"
  IO.println ("\n".intercalate (lines.qsort (· < ·)).toList)

import LeanForthFirstCheckerTerms
import LeanForthBinderDomains

/-!
# The binder-domain table's cases as declarations, in plain prefix text

Prints every case of `tests/reference/binder-domains.lean` (compiled to the
module `LeanForthBinderDomains` by `tests/core/lean-differential.py`) as the
declarations LeanForth's first checker must check, in the format of
`first-checker-terms.lean` (compiled to `LeanForthFirstCheckerTerms`, whose
printer this file uses), so that every row runs end to end through
check-declaration and the checked environment (plan task 2.2.3, ADR 0012
test matrix row 1).

A declaration row is its theorem. A comparison row, two closed terms `l` and
`r`, becomes one theorem whose check makes exactly that comparison:

* two types (`∀`s): `bdCompare : l → r := fun x : l => x`. The value's type
  is `l → l`; against the claim `l → r` the domains are identical and the
  bodies are `l` and `r`;
* two functions (`fun`s) of type `T`: `bdCompare : ∀ Q : T → Prop, Q l → Q r
  := fun Q h => h`. The value's type is `∀ Q, Q l → Q l`; against the claim
  the comparison reaches `Q l` and `Q r`, the same variable applied to `l`
  and to `r`. Neither side is a proof (their type is `Prop`), so Lean's
  kernel can only compare the arguments.

The run fails unless pinned Lean's kernel accepts each comparison's theorem
exactly when the table says the two terms are equal, and otherwise raises
`declTypeMismatch`. A row whose terms use `bdId` gets its definition as an
earlier declaration. These are reference observations, not a LeanForth
checker or theorem-acceptance path.
-/

open Lean Elab Command BinderDomains

/-- The theorem whose check makes Lean's comparison of `l` and `r`. -/
def encodeCompare (env : Environment) (id : String) (l r : Expr) :
    CommandElabM Declaration := do
  if l.isForall then
    pure (thm `bdCompare (arrow l r) (funs [(`x, l)] (v `x)))
  else
    let t ← inferIn env {} id l
    let q : Binder := (`Q, arrow t prop)
    let h : Binder := (`h, app (v `Q) [l])
    pure (thm `bdCompare (foralls [q, h] (app (v `Q) [r])) (funs [q, h] (v `h)))

/-- The declaration a row checks, and Lean's verdict it must get. -/
def rowDecl (env : Environment) (c : Case) : CommandElabM (Declaration × String) := do
  match c.subject with
  | .compare l r =>
    let d ← encodeCompare env c.id l r
    pure (d, if c.lean == "equal" then "accepted" else "declTypeMismatch")
  | .declare d .. => pure (d, c.lean)

/-- The definition of `bdId`, for the rows that use it. -/
def bdIdDecl (env : Environment) : CommandElabM Declaration := do
  match env.find? ``BinderDomains.bdId with
  | some (.defnInfo d) => pure (.defnDecl d)
  | _ => throwError "bdId is not a definition"

def usesBdId (d : Declaration) : Bool :=
  match d with
  | .thmDecl t => (t.type.getUsedConstants ++ t.value.getUsedConstants).contains
      ``BinderDomains.bdId
  | _ => false

run_cmd do
  let env ← getEnv
  let base := env.toKernelEnv
  let bdId ← bdIdDecl env
  for c in cases do
    let (d, expected) ← rowDecl env c
    -- Lean's environment already holds bdId, as in binder-domains.lean.
    let before := if usesBdId d then [bdId] else []
    let got := verdict (base.addDeclCore 1000000 1000 d none)
    unless got == expected do
      throwError "{c.id}: Lean's verdict is {got}, expected {expected}"
    IO.println s!"CASE {c.id}"
    for b in before do
      IO.println (declLine "before" b)
    IO.println (declLine "check" d)

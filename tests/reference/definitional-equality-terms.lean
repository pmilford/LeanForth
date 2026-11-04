import LeanForthFirstCheckerTerms
import LeanForthDefinitionalEquality

/-!
# The definitional-equality table's cases as declarations, in plain prefix text

Prints the cases of `tests/reference/definitional-equality.lean` (compiled to
the module `LeanForthDefinitionalEquality` by `tests/core/lean-differential.py`)
as the declarations LeanForth must check, in the format of
`first-checker-terms.lean` (compiled to `LeanForthFirstCheckerTerms`, whose
printer this file uses), so that every row runs end to end through
check-declaration and the checked environment (plan task 4.2.2c; the whole
table as a differential is plan task 4.3.1).

* A row that declares (`.declare`): its base -- the library, for a row of
  the file's environment, or the row's own earlier declarations -- as
  `before` declarations, then its declaration.
* A `whnf` row: the constant's declaration as Lean's elaborator made it,
  then `probe : T := c`, whose value LeanForth puts in whnf (the driver
  `tests/support/whnf-probe.fs`).
* A row that re-checks one of Lean's own elaborations (`later.*`, phase 5),
  or whose declaration names a constant of Lean's own library that its base
  does not declare (`And.rec` and the like, phase 5), is printed as
  `SKIP <id>` only: LeanForth would see an unknown constant there.

Lean's verdicts are those `definitional-equality.lean` checks. These are
reference observations, not a LeanForth checker or theorem-acceptance path.
-/

open Lean DefEq

/-- The declaration of a constant as Lean's elaborator added it. -/
def constDecl : ConstantInfo → Option Declaration
  | .defnInfo d => some (.defnDecl d)
  | .thmInfo t => some (.thmDecl t)
  | .opaqueInfo o => some (.opaqueDecl o)
  | .axiomInfo a => some (.axiomDecl a)
  | _ => none

/-- The probe of a `whnf` row: a definition whose value is the constant. -/
def probeDecl (info : ConstantInfo) : Declaration :=
  .defnDecl { name := `probe, levelParams := [], type := info.type,
              value := .const info.name [], hints := .opaque, safety := .safe }

/-- The terms of a declaration, and the names it declares. -/
def declExprs : Declaration → List Expr
  | .thmDecl t => [t.type, t.value]
  | .defnDecl d => [d.type, d.value]
  | .opaqueDecl o => [o.type, o.value]
  | .axiomDecl a => [a.type]
  | _ => []

def declNames : Declaration → List Name
  | .thmDecl t => [t.name]
  | .defnDecl d => [d.name]
  | .opaqueDecl o => [o.name]
  | .axiomDecl a => [a.name]
  | _ => []

/-- Whether every constant `d` names is declared by `before`. -/
def closedOver (before : List Declaration) (d : Declaration) : Bool :=
  let declared := before.foldr (fun b acc => declNames b ++ acc) []
  (declExprs d).all fun e => e.getUsedConstants.all declared.contains

run_cmd do
  let env ← getEnv
  for c in cases do
    match c.subject with
    | .declare base decl =>
      let before := match base with | .main => library | .fresh decls => decls
      if closedOver before decl then
        IO.println s!"CASE {c.id}"
        for d in before do
          IO.println (declLine "before" d)
        IO.println (declLine "check" decl)
      else
        IO.println s!"SKIP {c.id}"
    | .whnf n =>
      let some info := env.find? n | throwError "{c.id}: {n} not found"
      let some d := constDecl info | throwError "{c.id}: {n} is not a declaration"
      IO.println s!"CASE {c.id}"
      IO.println (declLine "before" d)
      IO.println (declLine "check" (probeDecl info))
    | .recheck .. => IO.println s!"SKIP {c.id}"

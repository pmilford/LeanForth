import LeanForthFirstChecker
import LeanForthFirstCheckerTerms

/-!
# Universe scope: ADR 0012 test-matrix row 4, against the pinned Lean kernel

Per-declaration universe scope (ADR 0012, E2): a reference `c.{l₁,…,lₙ}`
must give exactly as many levels as `c` has parameters (rule L1), each level
may use only the *caller's* parameters (L2), and `c`'s stored type is then
instantiated with each of `c`'s own parameters replaced by the level in the
same position, all at once; a declaration lists no parameter twice (L3).
The rows cover zero, exact, too few and too many levels; undeclared and
repeated parameters; caller and callee parameters with the same names in
swapped order (a substitution that is not simultaneous would get it
wrong); and nested `max`/`imax` arguments. Several port the cases of
`constant-environment-oracle.lean` to rows with an expected LeanForth
outcome.

Like `first-checker-expected.lean`, each case is added with
`Kernel.Environment.addDeclCore` to a scratch copy of the kernel environment
after its earlier declarations, and the run fails unless Lean's verdict is the
recorded one. The file prints one `EXPECT <id> <lean> <leanforth> <rule>` line
per case, then every case in the format of `first-checker-terms.lean`
(compiled to `LeanForthFirstCheckerTerms`, whose printer this file uses), for
`tests/core/lean-differential.py` (table `universe-scope`). Reference
observations, not a LeanForth checker or theorem-acceptance path.
-/

open Lean FirstChecker

namespace UniverseScope

def lw : Level := .param `w

/-- `idProp : ∀ (P : Prop), P → P := fun P h => h`: no universe parameter. -/
def idPropType : Expr := foralls [ex `P prop, ex `h (v `P)] (v `P)
def idProp : Declaration := thm `idProp idPropType (funs [ex `P prop, ex `h (v `P)] (v `h))

/-- A use of `idProp` with the given levels. -/
def useIdProp (n : Name) (ls : List Level) : Declaration :=
  thm n idPropType (funs [ex `P prop, ex `h (v `P)] (app (.const `idProp ls) [v `P, v `h]))

/-- `two.{u,v} : (A : Sort u) → (B : Sort v) → A → A := fun A B x => x`. -/
def twoType (a b : Level) : Expr :=
  foralls [ex `A (.sort a), ex `B (.sort b), ex `x (v `A)] (v `A)
def two : Declaration :=
  defn `two (twoType lu lv) (funs [ex `A (.sort lu), ex `B (.sort lv), ex `x (v `A)] (v `x))
    [`u, `v]

/-- `n.{ps} : twoType a b := two.{ls}`. -/
def useTwo (n : Name) (ps : List Name) (a b : Level) (ls : List Level) : Declaration :=
  defn n (twoType a b) (.const `two ls) ps 2

/-- `n.{ps} : {α : Sort l} → α → α := fixtureId.{l}`, written at `claim`. -/
def idAt (n : Name) (ps : List Name) (claim l : Level) : Declaration :=
  defn n (foralls [im `α (.sort claim), ex `x (v `α)] (v `α)) (.const `fixtureId [l]) ps 2

def nested : Level := .max lu (.imax lv (.succ lu))

def cases : List Case := [
  { id := "universe.zero-levels", before := [idProp], decl := useIdProp `useZero [],
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "idProp has no universe parameter and gets none" },
  { id := "universe.zero-given-one", before := [idProp],
    decl := useIdProp `useOne [.zero],
    lean := "levelCount", leanforth := "rejected", rule := "L1",
    what := "idProp gets one universe argument; it takes none" },
  { id := "universe.exact", before := [fixtureId], decl := idAt `exact [`u] lu lu,
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "fixtureId.{u} in a declaration with parameter u" },
  { id := "universe.exact-concrete", before := [fixtureId],
    decl := idAt `exactOne [] (.succ .zero) (.succ .zero),
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "fixtureId.{1} in a declaration without parameters" },
  { id := "universe.too-few", before := [fixtureId],
    decl := defn `tooFew fixtureIdType (.const `fixtureId []) [`u] 2,
    lean := "levelCount", leanforth := "rejected", rule := "L1",
    what := "fixtureId gets no universe argument; it takes one" },
  { id := "universe.too-many", before := [fixtureId],
    decl := defn `tooMany fixtureIdType (.const `fixtureId [lu, lu]) [`u] 2,
    lean := "levelCount", leanforth := "rejected", rule := "L1",
    what := "fixtureId gets two universe arguments; it takes one" },
  { id := "universe.undeclared-argument", before := [fixtureId],
    decl := idAt `undeclared [`u] lv lv,
    lean := "undefinedLevelParam", leanforth := "rejected", rule := "L2",
    what := "fixtureId.{v} where the declaration has only u (Sort v in the claim)" },
  { id := "universe.undeclared-argument-only", before := [fixtureId],
    decl := idAt `undeclaredArgument [`u] lu lv,
    lean := "undefinedLevelParam", leanforth := "rejected", rule := "L2",
    what := "fixtureId.{v} as the value, the claim at Sort u: only the argument fails" },
  { id := "universe.undeclared-in-nested-argument", before := [fixtureId],
    decl := idAt `undeclaredNested [`u, `v] (.max lu lw) (.max lu lw),
    lean := "undefinedLevelParam", leanforth := "rejected", rule := "L2",
    what := "fixtureId.{max u w} where the declaration has u and v" },
  { id := "universe.undeclared-in-sort",
    decl := defn `undeclaredSort (.sort (.succ lv)) (.sort lv) [`u] 1,
    lean := "undefinedLevelParam", leanforth := "rejected", rule := "L2",
    what := "Sort v in the type of a declaration with only u" },
  { id := "universe.repeated", before := [fixtureId], decl := idAt `repeated [`u, `u] lu lu,
    lean := "duplicateLevelParam", leanforth := "rejected", rule := "L3",
    what := "the declaration lists u twice" },
  { id := "universe.callee-parameters-swapped", before := [fixtureId, two],
    decl := useTwo `swapped [`u, `v] lv lu [lv, lu],
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "two.{v,u}: two's u becomes the caller's v and its v the caller's u" },
  { id := "universe.callee-parameters-unswapped", before := [fixtureId, two],
    decl := useTwo `unswapped [`u, `v] lv lu [lu, lv],
    lean := "declTypeMismatch", leanforth := "rejected", rule := "D1",
    what := "two.{u,v} where the claim needs two.{v,u}" },
  { id := "universe.caller-parameters-reordered", before := [fixtureId, two],
    decl := useTwo `reordered [`v, `u] lu lv [lu, lv],
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "the caller lists v before u; the names, not positions, match" },
  { id := "universe.nested-argument", before := [fixtureId],
    decl := idAt `nested [`u, `v] nested nested,
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "fixtureId.{max u (imax v (u+1))}" },
  { id := "universe.nested-argument-wrong", before := [fixtureId],
    decl := idAt `nestedWrong [`u, `v] (.max lu lv) nested,
    lean := "declTypeMismatch", leanforth := "rejected", rule := "D1",
    what := "fixtureId.{max u (imax v (u+1))} where Sort (max u v) is claimed" },
  { id := "universe.nested-argument-other-spelling", before := [fixtureId],
    decl := idAt `nestedSpelling [`u, `v] (.max (.imax lv (.succ lu)) lu) nested,
    lean := "accepted", leanforth := "unknown", rule := "K4",
    what := "the same level with max's arguments swapped: equal, but not identical" }
]

end UniverseScope

open UniverseScope in
run_cmd do
  let base := (← getEnv).toKernelEnv
  for c in UniverseScope.cases do
    let mut scratch := base
    for d in c.before do
      match scratch.addDeclCore 1000000 1000 d none with
      | .ok next => scratch := next
      | .error _ => throwError "{c.id}: Lean rejected a prerequisite"
    let got := verdict (scratch.addDeclCore 1000000 1000 c.decl none)
    unless got == c.lean do
      throwError "{c.id}: Lean's verdict is {got}, expected {c.lean}"
    IO.println s!"EXPECT {c.id} {got} {c.leanforth} {c.rule}"
  for c in UniverseScope.cases do
    IO.println s!"CASE {c.id}"
    for d in c.before do
      IO.println (declLine "before" d)
    IO.println (declLine "check" c.decl)

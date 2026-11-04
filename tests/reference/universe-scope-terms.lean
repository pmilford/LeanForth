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
outcome. The rows after them (ADR 0011, Amendment 1) check that levels are
built and compared as Lean's kernel builds and compares them; four show
that Lean's verdict on the same text depends on whether the universe
argument is the very object the stored type holds (rule K6).

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

/-! ### Levels built and compared as Lean's kernel does (ADR 0011, Amendment 1)

Lean's `infer_pi` builds a Π's sort with `mk_imax`, `instantiate` rebuilds
a specialized `max`/`imax` with `mk_max`/`mk_imax`, and two levels are
equal when `is_equivalent` holds (structurally, or after Lean's incomplete
`normalize`). The rows below are the independent review's (T1–T4, `th`,
`d`), the zero LeanForth used to drop at any depth, and adversarial cases:
nested `max`/`imax`, zeros, offsets, parameters equal and swapped, and
specializations that make an `imax`'s right side never zero, or zero. -/

def one : Level := .succ .zero
def s : Level → Level := .succ
/-- `n.{ps} : Sort claim := value` (height 1). -/
def sortDef (n : Name) (ps : List Name) (claim : Level) (value : Expr) : Declaration :=
  defn n (.sort claim) value ps
/-- `(A : Sort a) → Sort b`. -/
def piSorts (a b : Level) : Expr := foralls [ex `A (.sort a)] (.sort b)
/-- `T.{u,v} : Sort (imax u v + 1) := Sort (imax u v)`, and a use `T.{a,b}`. -/
def tImax : Declaration := sortDef `T [`u, `v] (s (.imax lu lv)) (.sort (.imax lu lv))
def useT (n : Name) (ps : List Name) (claim : Level) (a b : Level) : Declaration :=
  sortDef n ps (s claim) (.const `T [a, b])
/-- `T2.{u,v} : Sort (max u (imax v u) + 1) := Sort (max u (imax v u))`. -/
def nestedLevel : Level := .max lu (.imax lv lu)
def tNested : Declaration := sortDef `T2 [`u, `v] (s nestedLevel) (.sort nestedLevel)
def useT2 (n : Name) (ps : List Name) (claim : Level) (a b : Level) : Declaration :=
  sortDef n ps (s claim) (.const `T2 [a, b])
/-- `th.{u} : ∀ p : Prop, p → p := fun p h => (fun (X : Sort (imax 1 (u+1))) => h)
((A : Prop) → Sort u)`: the Π's sort, `max 1 (u+1)` for Lean, against a
binder written `imax 1 (u+1)`. -/
def thValue : Expr :=
  funs [ex `p prop, ex `h (v `p)]
    (app (.lam `X (.sort (.imax one (s lu))) (v `h) .default) [piSorts .zero lu])
def th : Declaration := thm `th idPropType thValue [`u]
/-- `T5.{u} : Sort (imax 1 (u+1) + 1) := Sort (imax 1 (u+1))`: a stored
`imax` that `mk_imax` would change, for the shared-object rows. -/
def imax1u : Level := .imax one (s lu)
def t5 : Declaration := sortDef `T5 [`u] (s imax1u) (.sort imax1u)
/-- The rows whose value's universe arguments are made fresh objects at run
time (`freshen`); the others share the objects the stored types hold. -/
def freshRows : List String := ["universe.fresh-object", "universe.fresh-object-max"]

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
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "the same level with max's arguments swapped: normalize sorts them" },
  -- The independent review of the declaration check (ADR 0011, Amendment 1).
  { id := "universe.pi-imax-swapped",
    decl := sortDef `T1 [`u, `v] (.imax (s lv) (s lu)) (piSorts lv lu),
    lean := "declTypeMismatch", leanforth := "rejected", rule := "D1",
    what := "T1: (A : Sort v) → Sort u is Sort (max (v+1) (u+1)); imax (v+1) (u+1) normalizes unsorted" },
  { id := "universe.pi-imax-sorted",
    decl := sortDef `T2 [`u, `v] (.imax (s lu) (s lv)) (piSorts lu lv),
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "T2: the same with u and v in Lean's name order" },
  { id := "universe.pi-max",
    decl := sortDef `T3 [`u, `v] (.max (s lv) (s lu)) (piSorts lv lu),
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "T3: Sort (max (v+1) (u+1)) claimed, exactly what mk_imax builds" },
  { id := "universe.pi-imax-prop-domain",
    decl := sortDef `T4 [`u] (.imax one (s lu)) (piSorts .zero lu),
    lean := "declTypeMismatch", leanforth := "rejected", rule := "D1",
    what := "T4: (A : Prop) → Sort u is Sort (max 1 (u+1)), not imax 1 (u+1) for Lean" },
  { id := "universe.app-imax", decl := th,
    lean := "appTypeMismatch", leanforth := "rejected", rule := "D1",
    what := "th: a Π of sort max 1 (u+1) passed where Sort (imax 1 (u+1)) is expected" },
  { id := "universe.instance-imax-nonzero", before := [tImax],
    decl := useT `d [`w] (.imax one (s lw)) one (s lw),
    lean := "declTypeMismatch", leanforth := "rejected", rule := "D1",
    what := "d: T.{1, w+1} has Sort (max 1 (w+1) + 1); imax 1 (w+1) claimed" },
  { id := "universe.zero-rewrite-gone",
    decl := sortDef `X [`u] (s (.max .zero imax1u)) (.sort imax1u),
    lean := "declTypeMismatch", leanforth := "rejected", rule := "D1",
    what := "max 0 (imax 1 (u+1)) against imax 1 (u+1) under a successor: Lean's normalize keeps them apart" },
  { id := "universe.zero-rewrite-gone-reversed",
    decl := sortDef `X2 [`u] (s imax1u) (.sort (.max .zero imax1u)),
    lean := "declTypeMismatch", leanforth := "rejected", rule := "D1",
    what := "the same pair the other way round" },
  -- Offsets, equal parameters, nested max, explicit levels, a Π into Prop.
  { id := "universe.offsets",
    decl := sortDef `O [`u] (s (.max (s lu) lu)) (.sort (s lu)),
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "max (u+1) u is u+1 after normalize" },
  { id := "universe.pi-equal-parameters",
    decl := sortDef `E [`u] (.imax (s lu) (s lu)) (piSorts lu lu),
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "imax (u+1) (u+1): mk_imax of equal levels" },
  { id := "universe.nested-max-explicit",
    decl := sortDef `N [`u, `v] (.max (s lv) (.max (s lu) one)) (piSorts lu lv),
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "max (v+1) (max (u+1) 1): flattened, sorted, 1 covered" },
  { id := "universe.nested-max-swapped",
    decl := sortDef `N2 [`u, `v] (.max (s lv) (.max (s lu) one)) (piSorts lv lu),
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "the same against (A : Sort v) → Sort u" },
  { id := "universe.explicit-max",
    decl := sortDef `Z [] (.max .zero one) prop,
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "max 0 1 against Prop's type" },
  { id := "universe.pi-into-prop",
    decl := sortDef `PP [`u] (.imax (s (s lu)) (.imax one .zero))
      (foralls [ex `A (.sort (s lu)), ex `P prop] (v `P)),
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "(A : Sort (u+1)) → (P : Prop) → P is Prop; imax (u+2) (imax 1 0) claimed" },
  -- Specializations of T.{u,v} (Sort (imax u v + 1)).
  { id := "universe.instance-imax-zero", before := [tImax],
    decl := useT `d0 [`w] (.imax lw .zero) lw .zero,
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "T.{w, 0}: imax w 0 is 0" },
  { id := "universe.instance-imax-zero-wrong", before := [tImax],
    decl := useT `d0c [`w] lw lw .zero,
    lean := "declTypeMismatch", leanforth := "rejected", rule := "D1",
    what := "T.{w, 0} is Sort 1, not Sort (w+1)" },
  { id := "universe.instance-imax-zero-left", before := [tImax],
    decl := useT `d1 [`w] (.imax .zero lw) .zero lw,
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "T.{0, w}: imax 0 w is w" },
  { id := "universe.instance-imax-equal", before := [tImax],
    decl := useT `d2 [`w] (.imax lw lw) lw lw,
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "T.{w, w}: imax w w is w" },
  { id := "universe.instance-imax-stays", before := [tImax],
    decl := useT `d3 [`w] (.max (s lw) lw) (s lw) lw,
    lean := "declTypeMismatch", leanforth := "rejected", rule := "D1",
    what := "T.{w+1, w} stays imax (w+1) w, not max (w+1) w" },
  { id := "universe.instance-imax-max", before := [tImax],
    decl := useT `d5 [`w] (.max one (s lw)) one (s lw),
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "T.{1, w+1} claimed as max 1 (w+1), as mk_imax builds it" },
  { id := "universe.instance-max-order", before := [tImax],
    decl := useT `d6 [`w] (.max one (s lw)) (s lw) one,
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "T.{w+1, 1} is max (w+1) 1; normalize sorts both sides" },
  { id := "universe.instance-imax-order", before := [tImax],
    decl := useT `d6b [`w] (.imax (s lw) one) (s lw) one,
    lean := "declTypeMismatch", leanforth := "rejected", rule := "D1",
    what := "T.{w+1, 1} against imax (w+1) 1, which normalizes to the unsorted max (w+1) 1" },
  { id := "universe.instance-swapped-imax", before := [tImax],
    decl := useT `d7 [`u, `v] (.imax (s lv) (s lu)) (s lv) (s lu),
    lean := "declTypeMismatch", leanforth := "rejected", rule := "D1",
    what := "T.{v+1, u+1} against imax (v+1) (u+1): names out of order" },
  { id := "universe.instance-swapped-max", before := [tImax],
    decl := useT `d8 [`u, `v] (.max (s lv) (s lu)) (s lv) (s lu),
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "T.{v+1, u+1} against max (v+1) (u+1)" },
  { id := "universe.instance-sorted-max", before := [tImax],
    decl := useT `d9 [`u, `v] (.max (s lu) (s lv)) (s lv) (s lu),
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "T.{v+1, u+1} against max (u+1) (v+1)" },
  { id := "universe.instance-nested-zero", before := [tNested],
    decl := useT2 `e1 [`w] lw lw .zero,
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "T2.{w, 0}: max w (imax 0 w) is w" },
  { id := "universe.instance-nested", before := [tNested],
    decl := useT2 `e3 [`u, `w] (.max lw (.imax lu lw)) lw lu,
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "T2.{w, u}: max w (imax u w)" },
  { id := "universe.instance-nested-succ", before := [tNested],
    decl := useT2 `e5 [`w] (s lw) (s lw) (s lw),
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "T2.{w+1, w+1}: max (w+1) (imax (w+1) (w+1)) is w+1" },
  -- Lean keeps a stored imax 1 (u+1) when the universe argument is the very
  -- object its type holds, and rebuilds it as max 1 (u+1) otherwise: the
  -- same text has two Lean verdicts; LeanForth says unknown (K6).
  { id := "universe.shared-object", before := [t5],
    decl := sortDef `S [`u] (s imax1u) (.const `T5 [lu]),
    lean := "accepted", leanforth := "unknown", rule := "K6",
    what := "T5.{u} with the stored u: Lean keeps imax 1 (u+1)" },
  { id := "universe.fresh-object", before := [t5],
    decl := sortDef `S [`u] (s imax1u) (.const `T5 [lu]),
    lean := "declTypeMismatch", leanforth := "unknown", rule := "K6",
    what := "the same with a fresh u: Lean builds max 1 (u+1)" },
  { id := "universe.shared-object-max", before := [t5],
    decl := sortDef `M [`u] (s (.max one (s lu))) (.const `T5 [lu]),
    lean := "declTypeMismatch", leanforth := "unknown", rule := "K6",
    what := "T5.{u} claimed at max 1 (u+1), with the stored u" },
  { id := "universe.fresh-object-max", before := [t5],
    decl := sortDef `M [`u] (s (.max one (s lu))) (.const `T5 [lu]),
    lean := "accepted", leanforth := "unknown", rule := "K6",
    what := "the same with a fresh u" }
]

/-- The value's universe arguments as new objects, allocated at run time
(`t` is a clock reading, so nothing can be computed ahead and shared; the
name is rebuilt from its text too, as the compiler turns `.param n` over a
matched `.param n` back into the same object). -/
partial def freshLevel (t : Nat) : Level → Level
  | .param n => .param (.mkSimple (if t == 0 then "unused" else n.toString))
  | .succ l => .succ (freshLevel t l)
  | .max a b => .max (freshLevel t a) (freshLevel t b)
  | .imax a b => .imax (freshLevel t a) (freshLevel t b)
  | l => l
def freshen (t : Nat) : Declaration → Declaration
  | .defnDecl d => .defnDecl { d with value := d.value.replace fun
      | .const n ls => some (.const n (ls.map (freshLevel t)))
      | _ => none }
  | d => d

end UniverseScope

open UniverseScope in
run_cmd do
  let base := (← getEnv).toKernelEnv
  let clock ← IO.monoNanosNow
  for c in UniverseScope.cases do
    let mut scratch := base
    for d in c.before do
      match scratch.addDeclCore 1000000 1000 d none with
      | .ok next => scratch := next
      | .error _ => throwError "{c.id}: Lean rejected a prerequisite"
    let decl := if UniverseScope.freshRows.contains c.id then freshen clock c.decl else c.decl
    let got := verdict (scratch.addDeclCore 1000000 1000 decl none)
    unless got == c.lean do
      throwError "{c.id}: Lean's verdict is {got}, expected {c.lean}"
    IO.println s!"EXPECT {c.id} {got} {c.leanforth} {c.rule}"
  for c in UniverseScope.cases do
    IO.println s!"CASE {c.id}"
    for d in c.before do
      IO.println (declLine "before" d)
    IO.println (declLine "check" c.decl)

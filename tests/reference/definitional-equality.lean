import Lean

/-!
# Definitional equality as Lean's kernel decides it: pinned Lean 4.35.0 verdicts

Reference observations for plan task 4.1.1, `docs/adr/0014-definitional-equality.md`:
how Lean 4.35.0's kernel unfolds definitions (reducibility hints and lazy delta
reduction), unfolds theorems, never unfolds opaque declarations, and applies eta,
proof irrelevance and `let` (zeta) when it compares two types.

Three kinds of rows:

1. **Declarations.** A hand-built kernel declaration added with
   `Kernel.Environment.addDeclCore` (full checking) to a scratch environment: the
   file's own environment plus this file's small `library` of definitions with
   chosen reducibility hints, or, for the `names.*` rows, an environment with no
   constants at all (`mkEmptyEnvironment`) plus the row's own few declarations.
   Kernel diagnostics are on, so for an accepted declaration the row also records
   how many times the kernel unfolded each constant while checking it (Lean's
   `unfoldCounter`, recorded by `unfold_definition_core` and by recursor
   reduction): this shows *which side* lazy delta reduction unfolded, not only
   the verdict. The counts include Lean's caches (a `whnf` answered from the
   cache unfolds nothing).
2. **Re-checked sources.** A theorem elaborated by Lean in this file (features of
   phase 5: structure eta, unit-like types, `Nat` literals, quotients) is added
   again under a new name; Lean's verdict and counts are recorded.
3. **whnf.** `Kernel.whnf` of a bare constant elaborated in this file: `unfolds`
   when the result differs from the constant, `stays` otherwise.

The run fails unless every verdict and every count is the recorded one. Every
row also names LeanForth's required answer under the rules approved so far
(`adr0011`: ADR 0011 with ADR 0003's amendment) and under ADR 0014 once
implemented (`adr0014`), with the ADR 0014 rule. Lean cannot say which cautious
answer is right, but the run fails if either column contradicts Lean
(*accepted* where Lean rejects, *rejected* where Lean accepts), and if the
`adr0014` column differs from Lean's own verdict on a row whose rule is not one
of the deferrals (`K5`, `K7`, `U1`, `U2`): the owner's rule is that LeanForth
gives exactly Lean's verdict. Nothing is added to this file's own environment by
the checks. The file prints one tab-separated row per case;
`definitional-equality-check.sh` compares them with
`definitional-equality.tsv`. These are reference observations, not a LeanForth
checker or theorem-acceptance path.
-/

open Lean Elab Command

universe u

namespace DefEq

/-! ## Constants elaborated by Lean itself

For the `whnf.*` rows (`Kernel.whnf` needs an elaborated environment) and the
phase-5 rows, which re-check what Lean's elaborator produced. -/

def dqDefW (A : Prop) : Prop := A → A
@[irreducible] def dqIrrW (A : Prop) : Prop := A → A
theorem dqThmW : ∀ A : Prop, A → A := fun _ h => h
opaque dqOpaqueW (A : Prop) : Prop := A → A

/-- A theorem whose proof Lean's kernel must unfold to reduce a recursor on it. -/
theorem dqAnd : True ∧ True := ⟨trivial, trivial⟩

namespace Source
theorem structEta (p : Nat × Nat) (P : Nat × Nat → Prop) (h : P p) : P (p.1, p.2) := h
theorem unitLike (a b : Unit) (P : Unit → Prop) (h : P a) : P b := h
theorem natLiteral (P : Nat → Prop) (h : P (2 + 2)) : P 4 := h
theorem quotLift (r : Nat → Nat → Prop) (f : Nat → Nat) (hf : ∀ a b, r a b → f a = f b)
    (a : Nat) (P : Nat → Prop) (h : P (f a)) : P (Quot.lift f hf (Quot.mk r a)) := h
end Source

/-! ## Building terms (as in `binder-domains.lean`)

Terms are written with named variables (`v`) and closed by `foralls`/`funs`,
which turn each binder's name into a de Bruijn index (`Expr.abstract`). The
kernel rejects any leftover named variable, so a slip in a builder cannot pass
silently. -/

def v (n : Name) : Expr := .fvar ⟨n⟩

abbrev Binder := Name × Expr

def foralls (bs : List Binder) (body : Expr) : Expr :=
  bs.foldr (fun (n, t) b => .forallE n t (b.abstract #[v n]) .default) body

def funs (bs : List Binder) (body : Expr) : Expr :=
  bs.foldr (fun (n, t) b => .lam n t (b.abstract #[v n]) .default) body

def arrow (a b : Expr) : Expr := .forallE `a a b .default

def app (f : Expr) (args : List Expr) : Expr := mkAppN f args.toArray

def c (n : Name) (ls : List Level := []) : Expr := .const n ls

def prop : Expr := .sort .zero
def type : Expr := .sort (.succ .zero)
def propFn : Expr := arrow prop prop

/-- `(fun T : Prop => T) e`: equal to `e` by one beta step. -/
def betaProp (e : Expr) : Expr := app (funs [(`T, prop)] (v `T)) [e]

/-- `f A`, the usual shape below. -/
def at1 (f : Name) (e : Expr) (ls : List Level := []) : Expr := app (c f ls) [e]

def defn (n : Name) (t val : Expr) (hints : ReducibilityHints) (ps : List Name := []) :
    Declaration :=
  .defnDecl { name := n, levelParams := ps, type := t, value := val, hints,
              safety := .safe }

def thm (n : Name) (t val : Expr) (ps : List Name := []) : Declaration :=
  .thmDecl { name := n, levelParams := ps, type := t, value := val }

def opq (n : Name) (t val : Expr) (ps : List Name := []) : Declaration :=
  .opaqueDecl { name := n, levelParams := ps, type := t, value := val, isUnsafe := false }

/-- `fun A : Prop => A → A`. -/
def twiceValue : Expr := funs [(`A, prop)] (arrow (v `A) (v `A))

/-- `fun A : Prop => target A`. -/
def via (target : Name) : Expr := funs [(`A, prop)] (at1 target (v `A))

/-! ## The library: definitions with chosen hints

The kernel takes reducibility hints as given (it does not recompute heights),
so a row can give two definitions honest, equal or inverted heights. Every
library declaration must be accepted. -/

def library : List Declaration := [
  defn `dqTwice propFn twiceValue (.regular 1),
  defn `dqAbbr propFn (via `dqTwice) .abbrev,
  defn `dqHigh propFn (via `dqTwice) (.regular 2),
  defn `dqSame propFn (via `dqTwice) (.regular 1),
  defn `dqLow propFn (via `dqTwice) (.regular 0),
  defn `dqOpq propFn (via `dqTwice) .opaque,
  defn `dqFst (arrow prop propFn) (funs [(`A, prop), (`B, prop)] (v `A)) (.regular 1),
  defn `dqAbbFst (arrow prop propFn) (funs [(`A, prop), (`B, prop)] (v `A)) .abbrev,
  defn `dqLift propFn (funs [(`A, prop)] (v `A)) (.regular 1) [`u],
  opq `dqLiftOpaque propFn (funs [(`A, prop)] (v `A)) [`u],
  opq `dqOpaque propFn twiceValue,
  defn `dqApp
    (foralls [(`A, type), (`B, type)] (arrow (arrow (v `A) (v `B)) (arrow (v `A) (v `B))))
    (funs [(`A, type), (`B, type), (`f, arrow (v `A) (v `B))] (v `f)) (.regular 1),
  defn `dqProp type prop (.regular 1),
  defn `dqPropFn type propFn (.regular 1),
  defn `dqC0 propFn twiceValue (.regular 1),
  defn `dqC1 propFn (via `dqC0) (.regular 2),
  defn `dqC2 propFn (via `dqC1) (.regular 3),
  defn `dqC3 propFn (via `dqC2) (.regular 4),
  defn `dqC4 propFn (via `dqC3) (.regular 5),
  defn `dqC5 propFn (via `dqC4) (.regular 6)
]

/-! ## Lean's verdict -/

def verdict : Except Kernel.Exception Kernel.Environment → String
  | .ok _ => "accepted"
  | .error e => match e with
    | .unknownConstant _ n => s!"unknownConstant {n}"
    | .alreadyDeclared .. => "alreadyDeclared"
    | .declTypeMismatch .. => "declTypeMismatch"
    | .declHasMVars .. => "declHasMVars"
    | .declHasFVars .. => "declHasFVars"
    | .funExpected .. => "funExpected"
    | .typeExpected .. => "typeExpected"
    | .letTypeMismatch .. => "letTypeMismatch"
    | .exprTypeMismatch .. => "exprTypeMismatch"
    | .appTypeMismatch .. => "appTypeMismatch"
    | .invalidProj .. => "invalidProj"
    | .thmTypeIsNotProp .. => "thmTypeIsNotProp"
    | .other msg => "other: " ++ msg
    | .deterministicTimeout => "deterministicTimeout"
    | .excessiveMemory => "excessiveMemory"
    | .deepRecursion => "deepRecursion"
    | .interrupted => "interrupted"

/-- The unfold counts of an accepted declaration, sorted by name: `-` if none. -/
def unfolds (env : Kernel.Environment) : String :=
  let pairs := env.getDiagnostics.unfoldCounter.toList.map (fun (n, k) => s!"{n}:{k}")
  let sorted := pairs.toArray.qsort (· < ·)
  if sorted.isEmpty then "-" else ",".intercalate sorted.toList

/-! ## The rows -/

/-- Where a declaration is added: after the library in this file's
environment, or in an environment with no constants after the given ones. -/
inductive Base where
  | main
  | fresh (decls : List Declaration)

inductive Subject where
  | declare (base : Base) (decl : Declaration)
  /-- Re-add the elaborated theorem `source` under the name `copy`. -/
  | recheck (source copy : Name)
  /-- `Kernel.whnf` of the elaborated constant. -/
  | whnf (constant : Name)

structure Case where
  id : String
  subject : Subject
  /-- Lean's verdict (checked here): `accepted` or the kernel exception; for
  `whnf` rows, `unfolds` or `stays`. -/
  lean : String
  /-- Unfold counts of an accepted declaration (checked here); `n/a` otherwise. -/
  counts : String := "n/a"
  /-- LeanForth's required answer under ADR 0011 as approved. -/
  adr0011 : String
  /-- LeanForth's required answer under ADR 0014. -/
  adr0014 : String
  /-- The ADR 0014 rule (or deferral) that decides the `adr0014` answer. -/
  rule : String
  what : String

/-- The theorem `n : ∀ context, claimed := fun context => proof`. -/
def claim (n : Name) (context : List Binder) (claimed proof : Expr) (ps : List Name := []) :
    Subject :=
  .declare .main (thm n (foralls context claimed) (funs context proof) ps)

/-- `∀ (A : Prop) (h : found), wanted`, proved by `h`: Lean compares `found`
(the proof's type) with `wanted` (the claim), in that order. -/
def retype (n : Name) (found wanted : Expr) : Subject :=
  .declare .main (thm n (foralls [(`A, prop)] (arrow found wanted))
    (funs [(`A, prop), (`h, found)] (v `h)))

def deltaCases : List Case := [
  { id := "delta.abbrev-first", subject := retype `t1 (at1 `dqTwice (v `A)) (at1 `dqAbbr (v `A)),
    lean := "accepted", counts := "dqAbbr:1", adr0011 := "unknown", adr0014 := "accepted",
    rule := "delta",
    what := "dqTwice A against dqAbbr A: the abbreviation is unfolded, the regular definition is not" },
  { id := "delta.higher-first", subject := retype `t2 (at1 `dqTwice (v `A)) (at1 `dqHigh (v `A)),
    lean := "accepted", counts := "dqHigh:1", adr0011 := "unknown", adr0014 := "accepted",
    rule := "delta",
    what := "height 1 against height 2: only the higher one is unfolded" },
  { id := "delta.higher-first-left", subject := retype `t3 (at1 `dqHigh (v `A)) (at1 `dqTwice (v `A)),
    lean := "accepted", counts := "dqHigh:1", adr0011 := "unknown", adr0014 := "accepted",
    rule := "delta",
    what := "the same with the sides swapped: still only the higher one" },
  { id := "delta.equal-heights", subject := retype `t4 (at1 `dqTwice (v `A)) (at1 `dqSame (v `A)),
    lean := "accepted", counts := "dqSame:1,dqTwice:2", adr0011 := "unknown",
    adr0014 := "accepted", rule := "delta",
    what := "equal heights, different constants: both unfolded, then dqTwice again" },
  { id := "delta.inverted-heights", subject := retype `t5 (at1 `dqTwice (v `A)) (at1 `dqLow (v `A)),
    lean := "accepted", counts := "dqLow:1,dqTwice:2", adr0011 := "unknown",
    adr0014 := "accepted", rule := "delta",
    what := "dqLow claims height 0 though it uses dqTwice (height 1): dqTwice goes first, uselessly" },
  { id := "delta.opaque-hint-last", subject := retype `t6 (at1 `dqTwice (v `A)) (at1 `dqOpq (v `A)),
    lean := "accepted", counts := "dqOpq:1,dqTwice:2", adr0011 := "unknown",
    adr0014 := "accepted", rule := "delta",
    what := "a definition with the opaque hint still unfolds, but after the regular side" },
  { id := "delta.same-head-arguments", subject := retype `t7
      (at1 `dqTwice (betaProp (v `A))) (at1 `dqTwice (v `A)),
    lean := "accepted", counts := "-", adr0011 := "unknown", adr0014 := "accepted",
    rule := "delta-args",
    what := "same regular head, arguments equal by beta: decided without unfolding" },
  { id := "delta.same-head-arguments-differ",
    subject := claim `t8 [(`A, prop), (`B, prop), (`h, app (c `dqFst) [v `A, v `B])]
      (app (c `dqFst) [v `A, v `A]) (v `h),
    lean := "accepted", counts := "dqFst:2", adr0011 := "unknown", adr0014 := "accepted",
    rule := "delta-args",
    what := "dqFst A B against dqFst A A: the arguments differ, but both unfold to A" },
  { id := "delta.same-head-abbrev",
    subject := claim `t9 [(`A, prop), (`B, prop), (`h, app (c `dqAbbFst) [v `A, v `B])]
      (app (c `dqAbbFst) [v `A, betaProp (v `B)]) (v `h),
    lean := "accepted", counts := "dqAbbFst:2", adr0011 := "unknown", adr0014 := "accepted",
    rule := "delta",
    what := "abbreviations skip the argument test: both unfolded although the arguments are equal" },
  { id := "delta.same-head-levels-differ", subject := retype `t10
      (at1 `dqLift (v `A) [.zero]) (at1 `dqLift (v `A) [.succ .zero]),
    lean := "accepted", counts := "dqLift:2", adr0011 := "unknown", adr0014 := "accepted",
    rule := "delta-args",
    what := "dqLift.{0} A against dqLift.{1} A: universe arguments differ, both unfold to A" },
  { id := "delta.same-head-levels-differ-opaque", subject := retype `t11
      (at1 `dqLiftOpaque (v `A) [.zero]) (at1 `dqLiftOpaque (v `A) [.succ .zero]),
    lean := "declTypeMismatch", adr0011 := "unsupported", adr0014 := "rejected",
    rule := "opaque",
    what := "the same with an opaque declaration: never unfolded, so the levels decide" },
  { id := "delta.chain", subject := retype `t12 (at1 `dqC0 (v `A)) (at1 `dqC5 (v `A)),
    lean := "accepted", counts := "dqC1:1,dqC2:1,dqC3:1,dqC4:1,dqC5:1", adr0011 := "unknown",
    adr0014 := "accepted", rule := "delta",
    what := "a chain of heights 6 down to 2 is unfolded one step at a time until dqC0 A appears" },
  { id := "delta.wrong-after-unfolding",
    subject := claim `t13 [(`A, prop), (`B, prop)] (at1 `dqTwice (v `A))
      (funs [(`h, v `B)] (v `h)),
    lean := "declTypeMismatch", adr0011 := "unknown", adr0014 := "rejected", rule := "delta",
    what := "B → B against dqTwice A: unfolded to A → A, the domains B and A differ" },
  { id := "delta.argument-after-unfolding",
    subject := claim `t14 [(`A, prop), (`B, prop), (`k, arrow (at1 `dqTwice (v `A)) (v `B))]
      (v `B) (app (v `k) [funs [(`x, v `A)] (v `x)]),
    lean := "accepted", counts := "dqTwice:1", adr0011 := "unknown", adr0014 := "accepted",
    rule := "delta",
    what := "k expects dqTwice A and gets fun x : A => x" },
  { id := "delta.argument-wrong-after-unfolding",
    subject := claim `t15 [(`A, prop), (`B, prop), (`k, arrow (at1 `dqTwice (v `A)) (v `B))]
      (v `B) (app (v `k) [funs [(`x, v `B)] (v `x)]),
    lean := "appTypeMismatch", adr0011 := "unknown", adr0014 := "rejected", rule := "delta",
    what := "k expects dqTwice A and gets fun x : B => x" },
  { id := "sort.after-unfolding",
    subject := claim `t16 [(`A, c `dqProp), (`h, v `A)] (v `A) (v `h),
    lean := "accepted", counts := "dqProp:1", adr0011 := "unknown", adr0014 := "accepted",
    rule := "ensure-sort",
    what := "A : dqProp is a type only after unfolding dqProp to Prop (once: whnf is cached)" },
  { id := "sort.not-after-unfolding",
    subject := claim `t17 [(`A, c `dqPropFn), (`h, v `A)] (v `A) (v `h),
    lean := "typeExpected", adr0011 := "unknown", adr0014 := "rejected", rule := "ensure-sort",
    what := "A : dqPropFn unfolds to Prop → Prop, so A is not a type" },
  { id := "pi.after-unfolding",
    subject := claim `t18 [(`f, c `dqPropFn), (`A, prop), (`h, app (v `f) [v `A])]
      (app (v `f) [v `A]) (v `h),
    lean := "accepted", counts := "dqPropFn:1", adr0011 := "unknown", adr0014 := "accepted",
    rule := "ensure-pi",
    what := "f : dqPropFn is a function only after unfolding dqPropFn" },
  { id := "pi.not-after-unfolding",
    subject := claim `t19 [(`f, c `dqProp), (`A, prop), (`h, app (v `f) [v `A])]
      (app (v `f) [v `A]) (v `h),
    lean := "funExpected", adr0011 := "unknown", adr0014 := "rejected", rule := "ensure-pi",
    what := "f : dqProp unfolds to Prop, which is not a function type" }
]

def opaqueCases : List Case := [
  { id := "opaque.never-unfolds", subject := retype `t20 (arrow (v `A) (v `A)) (at1 `dqOpaque (v `A)),
    lean := "declTypeMismatch", adr0011 := "unsupported", adr0014 := "rejected",
    rule := "opaque",
    what := "A → A against dqOpaque A, whose value is A → A: an opaque declaration never unfolds" },
  { id := "opaque.definition-twin", subject := retype `t21 (arrow (v `A) (v `A)) (at1 `dqTwice (v `A)),
    lean := "accepted", counts := "dqTwice:1", adr0011 := "unknown", adr0014 := "accepted",
    rule := "delta",
    what := "the same with the definition dqTwice: unfolded" },
  { id := "opaque.declaration-accepted",
    subject := .declare .main (opq `dqGoodOpaque propFn (funs [(`A, prop)] (v `A))),
    lean := "accepted", counts := "-", adr0011 := "unsupported", adr0014 := "accepted",
    rule := "opaque",
    what := "an opaque declaration's value is checked against its type" },
  { id := "opaque.declaration-wrong-value",
    subject := .declare .main (opq `dqBadOpaque propFn (funs [(`A, type)] (v `A))),
    lean := "declTypeMismatch", adr0011 := "unsupported", adr0014 := "rejected",
    rule := "opaque",
    what := "an opaque declaration whose value has another type" },
  { id := "whnf.definition", subject := .whnf ``dqDefW, lean := "unfolds",
    adr0011 := "n/a", adr0014 := "unfolds", rule := "delta",
    what := "Lean's whnf unfolds a definition" },
  { id := "whnf.irreducible-definition", subject := .whnf ``dqIrrW, lean := "unfolds",
    adr0011 := "n/a", adr0014 := "unfolds", rule := "delta",
    what := "@[irreducible] is an elaborator attribute: the kernel still unfolds" },
  { id := "whnf.theorem", subject := .whnf ``dqThmW, lean := "unfolds",
    adr0011 := "n/a", adr0014 := "unfolds", rule := "delta",
    what := "Lean's whnf unfolds a theorem (its hint is opaque: last, not never)" },
  { id := "whnf.opaque", subject := .whnf ``dqOpaqueW, lean := "stays",
    adr0011 := "n/a", adr0014 := "stays", rule := "opaque",
    what := "an opaque declaration stays" },
  { id := "theorem.unfolded-by-recursor",
    subject := .declare .main (thm `t22
      (app (c ``And.rec [.succ .zero])
        [c ``True, c ``True, funs [(`x, app (c ``And) [c ``True, c ``True])] prop,
         funs [(`l, c ``True), (`r, c ``True)] (c ``True), c ``dqAnd])
      (c ``True.intro)),
    lean := "accepted", counts := "And.rec:1,DefEq.dqAnd:1", adr0011 := "unsupported",
    adr0014 := "unsupported", rule := "U1",
    what := "And.rec on the theorem dqAnd reduces only after unfolding dqAnd's proof (phase 5)" },
  { id := "theorem.variable-proof-stuck",
    subject := claim `t23 [(`p, app (c ``And) [c ``True, c ``True])]
      (app (c ``And.rec [.succ .zero])
        [c ``True, c ``True, funs [(`x, app (c ``And) [c ``True, c ``True])] prop,
         funs [(`l, c ``True), (`r, c ``True)] (c ``True), v `p])
      (c ``True.intro),
    lean := "declTypeMismatch", adr0011 := "unsupported", adr0014 := "unsupported", rule := "U1",
    what := "the same on a variable proof p: nothing to unfold, the recursor is stuck" }
]

def etaContext : List Binder :=
  [(`A, type), (`B, type), (`f, arrow (v `A) (v `B)), (`g, arrow (v `A) (v `B)),
   (`P, arrow (arrow (v `A) (v `B)) prop)]

def etaOf (fn : Expr) : Expr := funs [(`x, v `A)] (app fn [v `x])

/-- Under `etaContext`: claim `P wanted` from `h : P found`. -/
def etaClaim (n : Name) (found wanted : Expr) : Subject :=
  claim n (etaContext ++ [(`h, app (v `P) [found])]) (app (v `P) [wanted]) (v `h)

def etaCases : List Case := [
  { id := "eta.lambda-in-claim", subject := etaClaim `t24 (v `f) (etaOf (v `f)),
    lean := "accepted", counts := "-", adr0011 := "unknown", adr0014 := "accepted", rule := "eta",
    what := "P f used as P (fun x => f x)" },
  { id := "eta.lambda-in-proof", subject := etaClaim `t25 (etaOf (v `f)) (v `f),
    lean := "accepted", counts := "-", adr0011 := "unknown", adr0014 := "accepted", rule := "eta",
    what := "P (fun x => f x) used as P f: eta in the other order" },
  { id := "eta.wrong-function", subject := etaClaim `t26 (v `f) (etaOf (v `g)),
    lean := "declTypeMismatch", adr0011 := "unknown", adr0014 := "rejected", rule := "eta",
    what := "P f used as P (fun x => g x)" },
  { id := "eta.after-unfolding",
    subject := etaClaim `t27 (app (c `dqApp) [v `A, v `B, v `f]) (etaOf (v `f)),
    lean := "accepted", counts := "dqApp:1", adr0011 := "unknown", adr0014 := "accepted",
    rule := "eta",
    what := "dqApp A B f unfolds to f, then eta against fun x => f x" },
  { id := "eta.two-binders",
    subject := claim `t28
      [(`A, type), (`B, type), (`k, arrow (v `A) (arrow (v `A) (v `B))),
       (`Q, arrow (arrow (v `A) (arrow (v `A) (v `B))) prop), (`h, app (v `Q) [v `k])]
      (app (v `Q) [funs [(`x, v `A), (`y, v `A)] (app (v `k) [v `x, v `y])]) (v `h),
    lean := "accepted", counts := "-", adr0011 := "unknown", adr0014 := "accepted", rule := "eta",
    what := "Q k used as Q (fun x y => k x y): eta twice" }
]

def irrelevanceCases : List Case := [
  { id := "proof-irrelevance.same-statement",
    subject := claim `t29
      [(`A, prop), (`Q, arrow (v `A) prop), (`h, v `A), (`k, v `A), (`q, app (v `Q) [v `h])]
      (app (v `Q) [v `k]) (v `q),
    lean := "accepted", counts := "-", adr0011 := "unknown", adr0014 := "accepted",
    rule := "proof-irrelevance",
    what := "Q h used as Q k, where h and k prove the same A" },
  { id := "proof-irrelevance.statement-after-unfolding",
    subject := claim `t30
      [(`A, prop), (`Q, arrow (arrow (v `A) (v `A)) prop), (`h, at1 `dqTwice (v `A)),
       (`k, arrow (v `A) (v `A)), (`q, app (v `Q) [v `h])]
      (app (v `Q) [v `k]) (v `q),
    lean := "accepted", counts := "dqTwice:3", adr0011 := "unknown", adr0014 := "accepted",
    rule := "proof-irrelevance",
    what := "h : dqTwice A and k : A → A: their statements are equal after unfolding" },
  { id := "proof-irrelevance.not-proofs",
    subject := claim `t31
      [(`A, type), (`Q, arrow (arrow (v `A) (v `A)) prop), (`f, arrow (v `A) (v `A)),
       (`g, arrow (v `A) (v `A)), (`q, app (v `Q) [v `f])]
      (app (v `Q) [v `g]) (v `q),
    lean := "declTypeMismatch", adr0011 := "rejected", adr0014 := "rejected",
    rule := "proof-irrelevance",
    what := "the same shape over a Type: f and g are functions, not proofs" },
  { id := "proof-irrelevance.any-sort",
    subject := claim `t32
      [(`A, .sort (.param `u)), (`Q, arrow (v `A) prop), (`h, v `A), (`k, v `A),
       (`q, app (v `Q) [v `h])]
      (app (v `Q) [v `k]) (v `q) [`u],
    lean := "declTypeMismatch", adr0011 := "rejected", adr0014 := "rejected",
    rule := "proof-irrelevance",
    what := "A : Sort u is a proposition only when u = 0, so h and k are not known to be proofs" }
]

def letCases : List Case := [
  { id := "let.in-proof",
    subject := claim `t33 [(`A, prop), (`h, v `A)] (v `A)
      (.letE `y (v `A) (v `h) (.bvar 0) false),
    lean := "accepted", counts := "-", adr0011 := "unsupported", adr0014 := "accepted",
    rule := "zeta",
    what := "let y : A := h; y" },
  { id := "let.in-claim",
    subject := claim `t34 [(`A, prop)]
      (.letE `T prop (v `A) (arrow (.bvar 0) (v `A)) false)
      (funs [(`h, v `A)] (v `h)),
    lean := "accepted", counts := "-", adr0011 := "unsupported", adr0014 := "accepted",
    rule := "zeta",
    what := "claims let T := A; T → A, proved by fun h : A => h" },
  { id := "let.variable-unfolds",
    subject := claim `t35 [(`A, prop), (`h, v `A)] (v `A)
      (.letE `T prop (v `A) (app (.lam `x (.bvar 0) (.bvar 0) .default) [v `h]) false),
    lean := "accepted", counts := "-", adr0011 := "unsupported", adr0014 := "accepted",
    rule := "zeta",
    what := "let T := A; (fun x : T => x) h: T is replaced by its value A" },
  { id := "let.wrong-value",
    subject := claim `t36 [(`A, prop), (`B, prop), (`h, v `A)] (v `A)
      (.letE `y (v `B) (v `h) (v `h) false),
    lean := "letTypeMismatch", adr0011 := "unsupported", adr0014 := "rejected", rule := "zeta",
    what := "let y : B := h where h : A" }
]

/-! ## Constants matched by name

In an environment with no constants, user definitions named like Lean's
natural numbers. Lean's kernel recognises `Nat.zero`, `Nat.succ` and the `Nat`
operations by name, whatever they are (`type_checker.cpp` 1025–1066). -/

def natSuccLike (n : Name) : Declaration :=
  defn n propFn (funs [(`A, prop)] (foralls [(`X, prop)] (arrow (v `X) (v `X)))) (.regular 1)

def succClaim (n : Name) (s : Name) : Declaration :=
  thm n (foralls [(`A, prop), (`B, prop), (`P, propFn), (`h, app (v `P) [at1 s (v `A)])]
      (app (v `P) [at1 s (v `B)]))
    (funs [(`A, prop), (`B, prop), (`P, propFn), (`h, app (v `P) [at1 s (v `A)])] (v `h))

def zeroLike (z : Name) : Declaration := opq z prop (foralls [(`X, prop)] (arrow (v `X) (v `X)))
def idLike (s : Name) : Declaration := defn s propFn (funs [(`A, prop)] (v `A)) (.regular 1)

def zeroClaim (n z s : Name) : Declaration :=
  thm n (foralls [(`P, propFn), (`h, app (v `P) [at1 s (c z)])] (app (v `P) [c z]))
    (funs [(`P, propFn), (`h, app (v `P) [at1 s (c z)])] (v `h))

def nameCases : List Case := [
  { id := "names.nat-succ-matched-by-name",
    subject := .declare (.fresh [natSuccLike `Nat.succ]) (succClaim `t37 `Nat.succ),
    lean := "declTypeMismatch", adr0011 := "unknown", adr0014 := "rejected", rule := "offset",
    what := "Nat.succ A against Nat.succ B for a user Nat.succ ignoring its argument: Lean compares A with B" },
  { id := "names.ordinary-name-twin",
    subject := .declare (.fresh [natSuccLike `dqSucc]) (succClaim `t38 `dqSucc),
    lean := "accepted", counts := "dqSucc:2", adr0011 := "unknown", adr0014 := "accepted",
    rule := "delta-args",
    what := "the same definition under another name: unfolded, accepted" },
  { id := "names.nat-zero-becomes-a-literal",
    subject := .declare (.fresh [zeroLike `Nat.zero, idLike `Nat.succ])
      (zeroClaim `t39 `Nat.zero `Nat.succ),
    lean := "unknownConstant Nat", adr0011 := "unsupported", adr0014 := "unknown", rule := "K7",
    what := "Nat.succ Nat.zero is turned into the literal 1, whose type Nat does not exist" },
  { id := "names.ordinary-zero-twin",
    subject := .declare (.fresh [zeroLike `dqZero, idLike `dqSucc])
      (zeroClaim `t40 `dqZero `dqSucc),
    lean := "accepted", counts := "dqSucc:1", adr0011 := "unsupported", adr0014 := "accepted",
    rule := "delta",
    what := "the same under other names: dqSucc unfolds" }
]

def laterCases : List Case := [
  { id := "later.structure-eta", subject := .recheck ``Source.structEta `t41,
    lean := "accepted", counts := "Prod.fst:1,Prod.snd:1", adr0011 := "unsupported", adr0014 := "unsupported",
    rule := "U1",
    what := "P p used as P (p.1, p.2): structure eta (phase 5)" },
  { id := "later.unit-like", subject := .recheck ``Source.unitLike `t42,
    lean := "accepted", counts := "Unit:2", adr0011 := "unsupported", adr0014 := "unsupported",
    rule := "U1",
    what := "any two values of Unit are equal (phase 5)" },
  { id := "later.nat-literal", subject := .recheck ``Source.natLiteral `t43,
    lean := "accepted",
    counts := "Add.add:1,HAdd.hAdd:1,OfNat.ofNat:2,instAddNat:1,instHAdd:1,instOfNatNat:2,outParam:1", adr0011 := "unsupported", adr0014 := "unsupported",
    rule := "U2",
    what := "2 + 2 against 4: instances unfold to Nat.add, computed on literals (phase 5)" },
  { id := "later.quotient", subject := .recheck ``Source.quotLift `t44,
    lean := "accepted", counts := "Quot.lift:1", adr0011 := "unsupported", adr0014 := "unsupported",
    rule := "U1",
    what := "Quot.lift f h (Quot.mk r a) reduces to f a (phase 5)" }
]

def cases : List Case :=
  deltaCases ++ opaqueCases ++ etaCases ++ irrelevanceCases ++ letCases ++ nameCases ++ laterCases

/-- Rules under which ADR 0014 defers to a later phase: the `adr0014` answer
must then be unknown or unsupported; under every other rule it must be Lean's. -/
def deferrals : List String := ["K5", "K7", "U1", "U2"]

/-- Add `decls` in order; Lean must accept each. -/
def addAll (env : Kernel.Environment) (decls : List Declaration) :
    CommandElabM Kernel.Environment := do
  let mut env := env
  for d in decls do
    match env.addDeclCore 1000000 1000 d none with
    | .ok e => env := e
    | .error _ => throwError "a library declaration was rejected: {repr (d.getNames)}"
  pure env

/-- Lean's verdict on `decl` added to `env`, with unfold counts if accepted. -/
def judge (env : Kernel.Environment) (decl : Declaration) : String × String :=
  let env := (env.enableDiag true).resetDiag
  match env.addDeclCore 1000000 1000 decl none with
  | .ok e => ("accepted", unfolds e)
  | r => (verdict r, "n/a")

end DefEq

open DefEq in
run_cmd do
  let env ← getEnv
  let main ← addAll env.toKernelEnv library
  let empty ← liftM (m := IO) mkEmptyEnvironment
  IO.println "id\tlean\tunfolds\tadr0011\tadr0014\trule"
  for c in cases do
    let (got, counts) ← match c.subject with
      | .declare .main decl => pure (judge main decl)
      | .declare (.fresh decls) decl => do
        let base ← addAll empty.toKernelEnv decls
        pure (judge base decl)
      | .recheck source copy => do
        let some info := env.find? source | throwError "{c.id}: {source} not found"
        let some value := info.value? (allowOpaque := true) | throwError "{c.id}: {source} has no value"
        pure (judge env.toKernelEnv (thm copy info.type value info.levelParams))
      | .whnf n => do
        match Kernel.whnf env {} (.const n []) with
        | .ok r => pure (if r == .const n [] then "stays" else "unfolds", "n/a")
        | .error _ => throwError "{c.id}: Lean's whnf raised an exception"
    unless got == c.lean do
      throwError "{c.id}: Lean's answer is {got}, expected {c.lean}"
    unless counts == c.counts do
      throwError "{c.id}: Lean's unfold counts are {counts}, expected {c.counts}"
    -- LeanForth's answers may be cautious but never contradict Lean; ADR 0014's
    -- answer is Lean's own unless the row's rule defers the feature.
    let isWhnf := match c.subject with | .whnf _ => true | _ => false
    let leanYes := got == "accepted"
    for answer in [c.adr0011, c.adr0014] do
      let ok := if isWhnf then ["n/a", "unfolds", "stays"].contains answer
        else ["accepted", "rejected", "unknown", "unsupported"].contains answer
      unless ok do throwError "{c.id}: {answer} is not a LeanForth answer for this row"
      if !isWhnf && ((answer == "accepted" && !leanYes) || (answer == "rejected" && leanYes)) then
        throwError "{c.id}: LeanForth's answer {answer} contradicts Lean's {got}"
    if deferrals.contains c.rule then
      unless ["unknown", "unsupported"].contains c.adr0014 do
        throwError "{c.id}: rule {c.rule} defers the feature, so ADR 0014 answers unknown or unsupported"
    else
      let lean := if isWhnf then got else if leanYes then "accepted" else "rejected"
      unless c.adr0014 == lean do
        throwError "{c.id}: ADR 0014 must give Lean's verdict {lean}, not {c.adr0014}"
    IO.println s!"{c.id}\t{got}\t{counts}\t{c.adr0011}\t{c.adr0014}\t{c.rule}"

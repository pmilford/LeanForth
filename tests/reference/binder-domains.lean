import Lean

/-!
# Comparing under binders whose domains differ: the pinned Lean 4.35.0 kernel

Reference observations for plan task 2.1.2, the question the 2026-10-30 human
review left open: may LeanForth compare the bodies of two `fun`s (or two `∀`s)
whose binder domains are written differently but are equal, and if so, which
domain does the bound variable get? The answer and its Lean source citations
are in `docs/adr/0003-conversion.md`, "Amendment 1".

Two groups of rows:

1. **Comparisons.** A pair of closed terms, both `∀` or both `fun`, whose
   binder domains differ. Lean's kernel first checks that both terms are well
   typed (`Kernel.check`), then compares them with `Kernel.isDefEq` in *both*
   orders. The run fails unless both orders give the recorded answer (`equal`
   or `different`) and the two terms are not already structurally equal.
2. **Declarations.** A theorem whose value's type differs from its declared
   type, or whose argument's type differs from the expected domain, only in
   binder domains. Each row also names that inner comparison; the run checks
   that its two types are structurally different binders and that Lean's
   answer on them, in both orders, explains the verdict. Each declaration is
   added with `Kernel.Environment.addDeclCore` to a scratch copy of the kernel
   environment; the run fails unless Lean's verdict (accepted, or the exact
   kind of kernel exception) is the recorded one. Nothing is added to this
   file's own environment.

Every row also names LeanForth's required answer under ADR 0003 and ADR 0011
as approved (`now`) and under the proposed amendment (`amended`), with the
rule. Lean cannot say which cautious answer is right, but the run fails if
either column contradicts Lean: *equal* or *accepted* where Lean says no,
*apart* or *rejected* where Lean says yes. The columns are the specification
for the LeanForth differential (plan task 2.2.1). The file prints one tab-separated
row per case; `binder-domains-check.sh` compares the rows with
`binder-domains.tsv`. These are reference observations, not a LeanForth
checker or theorem-acceptance path.
-/

open Lean Elab Command

universe u

namespace BinderDomains

/-- The polymorphic identity. One pair of rows uses `bdId.{1} Prop A`, which is
`A` only after unfolding `bdId`: Lean's kernel unfolds definitions, LeanForth's
first checker does not. -/
def bdId {α : Sort u} (x : α) : α := x

/-! ## Building terms (as in `first-checker-expected.lean`)

Terms are written with named variables (`v`) and closed by `foralls`/`funs`,
which turn each binder's name into a de Bruijn index (`Expr.abstract`). The
kernel rejects any leftover named variable, so a slip in a builder cannot pass
silently. -/

/-- A variable by name, bound later by `foralls` or `funs`. -/
def v (n : Name) : Expr := .fvar ⟨n⟩

abbrev Binder := Name × Expr

/-- `∀ bs, body`, every binder explicit (the kernel ignores annotations). -/
def foralls (bs : List Binder) (body : Expr) : Expr :=
  bs.foldr (fun (n, t) b => .forallE n t (b.abstract #[v n]) .default) body

/-- `fun bs => body`. -/
def funs (bs : List Binder) (body : Expr) : Expr :=
  bs.foldr (fun (n, t) b => .lam n t (b.abstract #[v n]) .default) body

/-- The non-dependent function type `a → b`. -/
def arrow (a b : Expr) : Expr := .forallE `a a b .default

/-- `f a₁ … aₙ`. -/
def app (f : Expr) (args : List Expr) : Expr := mkAppN f args.toArray

def prop : Expr := .sort .zero
def type : Expr := .sort (.succ .zero)

/-- `(fun T : Prop => T) e`: equal to `e` by one beta step. -/
def betaProp (e : Expr) : Expr := app (funs [(`T, prop)] (v `T)) [e]

/-- `(fun T : Type => T) e`: equal to `e` by one beta step. -/
def betaType (e : Expr) : Expr := app (funs [(`T, type)] (v `T)) [e]

/-- `bdId.{1} Prop e`: equal to `e`, but only by unfolding `bdId`. -/
def hidden (e : Expr) : Expr := app (.const ``bdId [.succ .zero]) [prop, e]

def thm (n : Name) (t val : Expr) : Declaration :=
  .thmDecl { name := n, levelParams := [], type := t, value := val }

/-! ## Lean's verdict -/

/-- A short, stable name for the kernel's answer on a declaration; any other
exception is printed in full and so fails the comparison with the table. -/
def verdict : Except Kernel.Exception Kernel.Environment → String
  | .ok _ => "accepted"
  | .error e => match e with
    | .unknownConstant .. => "unknownConstant"
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

/-- One row: a comparison of two closed terms, or a declaration together with
the comparison inside it that decides Lean's verdict: the type Lean infers for
`term` (in `context`, whose names are the free variables `v` of `term`)
against `expected`. For a whole declaration `term` is its value and
`expected` its declared type (`add_theorem`); for an argument they are the
argument and the function's domain (`infer_app`). -/
inductive Subject where
  | compare (left right : Expr)
  | declare (decl : Declaration) (context : List Binder) (term expected : Expr)

structure Case where
  id : String
  subject : Subject
  /-- Lean's expected answer (checked here). -/
  lean : String
  /-- LeanForth's required answer under ADR 0003 and ADR 0011 as approved. -/
  now : String
  /-- LeanForth's required answer under ADR 0003 Amendment 1. -/
  amended : String
  /-- The rule that decides LeanForth's amended answer. -/
  rule : String
  /-- What differs, in a few words. -/
  what : String

/-! ## Comparisons: two `∀`s or two `fun`s whose domains differ -/

def compareCases : List Case := [
  { id := "compare.beta-domain",
    subject := .compare
      (foralls [(`A, prop)] (arrow (betaProp (v `A)) (v `A)))
      (foralls [(`A, prop)] (arrow (v `A) (v `A))),
    lean := "equal", now := "unknown", amended := "equal", rule := "B1",
    what := "domain (fun T => T) A against A; the body does not use the variable" },
  { id := "compare.beta-domain-used-by-body",
    subject := .compare
      (funs [(`A, type), (`x, betaType (v `A))] (v `x))
      (funs [(`A, type), (`x, v `A)] (v `x)),
    lean := "equal", now := "unknown", amended := "equal", rule := "B1",
    what := "fun x : (fun T => T) A => x against fun x : A => x; the body is the variable" },
  { id := "compare.beta-domain-in-telescope",
    subject := .compare
      (foralls [(`A, type), (`P, arrow (v `A) prop), (`x, betaType (v `A))] (app (v `P) [v `x]))
      (foralls [(`A, type), (`P, arrow (v `A) prop), (`x, v `A)] (app (v `P) [v `x])),
    lean := "equal", now := "unknown", amended := "equal", rule := "B1",
    what := "the third domain differs by beta and the body P x uses its variable" },
  { id := "compare.beta-domain-different-body",
    subject := .compare
      (foralls [(`A, prop), (`B, prop)] (arrow (betaProp (v `A)) (v `B)))
      (foralls [(`A, prop), (`B, prop)] (arrow (v `A) (v `A))),
    lean := "different", now := "unknown", amended := "apart", rule := "D4+B1",
    what := "domains equal by beta, bodies B and A differ" },
  { id := "compare.lambda-beta-domain-different-body",
    subject := .compare
      (funs [(`A, type), (`x, betaType (v `A)), (`y, v `A)] (v `x))
      (funs [(`A, type), (`x, v `A), (`y, v `A)] (v `y)),
    lean := "different", now := "unknown", amended := "apart", rule := "D4+B1",
    what := "fun x y => x against fun x y => y, first domains equal by beta" },
  { id := "compare.domain-apart",
    subject := .compare
      (foralls [(`A, prop), (`B, prop)] (arrow (v `B) (v `A)))
      (foralls [(`A, prop), (`B, prop)] (arrow (v `A) (v `A))),
    lean := "different", now := "apart", amended := "apart", rule := "D4",
    what := "domains B and A differ" },
  { id := "compare.domain-needs-unfolding",
    subject := .compare
      (foralls [(`A, prop)] (arrow (hidden (v `A)) (v `A)))
      (foralls [(`A, prop)] (arrow (v `A) (v `A))),
    lean := "equal", now := "unknown", amended := "equal", rule := "A1",
    what := "domain bdId Prop A against A: equal only by unfolding bdId" },
  { id := "compare.domain-needs-unfolding-different-body",
    subject := .compare
      (foralls [(`A, prop), (`B, prop)] (arrow (hidden (v `A)) (v `B)))
      (foralls [(`A, prop), (`B, prop)] (arrow (v `A) (v `A))),
    lean := "different", now := "unknown", amended := "apart", rule := "defeq",
    what := "LeanForth stops at the undecided domain, though the bodies differ" },
  { id := "compare.domain-proof-irrelevance",
    subject := .compare
      (foralls [(`A, prop), (`P, arrow (v `A) prop), (`h, v `A), (`k, v `A)]
        (arrow (app (v `P) [v `h]) (v `A)))
      (foralls [(`A, prop), (`P, arrow (v `A) prop), (`h, v `A), (`k, v `A)]
        (arrow (app (v `P) [v `k]) (v `A))),
    lean := "equal", now := "unknown", amended := "unknown", rule := "K2",
    what := "domain P h against P k, where h and k are proofs of A" },
  { id := "compare.eta-under-beta-domain",
    subject := .compare
      (funs [(`A, type), (`f, betaType (arrow (v `A) (v `A)))] (v `f))
      (funs [(`A, type), (`f, arrow (v `A) (v `A))]
        (funs [(`x, v `A)] (app (v `f) [v `x]))),
    lean := "equal", now := "unknown", amended := "unknown", rule := "K3",
    what := "domains equal by beta, then f against fun x => f x (eta)" }
]

/-! ## Declarations whose types differ only in binder domains -/

/-- The theorem `n : t := val`: Lean compares the type of `val` with `t`. -/
def whole (n : Name) (t val : Expr) : Subject := .declare (thm n t val) [] val t

/-- The theorem `n : ∀ context, result := fun context => k arg`, where `k` is
the last binder of `context` and has domain `expected`: Lean compares the type
of `arg` with `expected` when it checks the application. -/
def argument (n : Name) (context : List Binder) (result arg expected : Expr) : Subject :=
  .declare (thm n (foralls context result) (funs context (app (v `k) [arg])))
    context arg expected

def declareCases : List Case := [
  { id := "decl.beta-domain-in-statement",
    subject := whole `bdStatement
      (foralls [(`A, prop)] (arrow (betaProp (v `A)) (v `A)))
      (funs [(`A, prop), (`h, v `A)] (v `h)),
    lean := "accepted", now := "unknown", amended := "accepted", rule := "A1+B1",
    what := "claims (fun T => T) A → A; the proof takes h : A" },
  { id := "decl.beta-domain-in-proof",
    subject := whole `bdProof
      (foralls [(`A, prop)] (arrow (v `A) (v `A)))
      (funs [(`A, prop), (`h, betaProp (v `A))] (v `h)),
    lean := "accepted", now := "unknown", amended := "accepted", rule := "A1+B1",
    what := "claims A → A; the proof takes h : (fun T => T) A" },
  { id := "decl.beta-domain-used-by-body",
    subject := whole `bdDependent
      (foralls [(`A, type), (`P, arrow (v `A) prop), (`x, betaType (v `A))]
        (arrow (app (v `P) [v `x]) (app (v `P) [v `x])))
      (funs [(`A, type), (`P, arrow (v `A) prop), (`x, v `A), (`h, app (v `P) [v `x])] (v `h)),
    lean := "accepted", now := "unknown", amended := "accepted", rule := "A1+B1",
    what := "x : (fun T => T) A in the claim, x : A in the proof; P x uses x" },
  { id := "decl.beta-domain-wrong-claim",
    subject := whole `bdWrongClaim
      (foralls [(`A, prop), (`B, prop)] (arrow (betaProp (v `A)) (arrow (v `B) (v `A))))
      (funs [(`A, prop), (`B, prop), (`h, v `A), (`k, v `B)] (v `k)),
    lean := "declTypeMismatch", now := "unknown", amended := "rejected", rule := "D4+B1",
    what := "domains equal by beta; the proof gives B where A is claimed" },
  { id := "decl.domain-apart",
    subject := whole `bdApart
      (foralls [(`A, prop), (`B, prop)] (arrow (v `A) (v `A)))
      (funs [(`A, prop), (`B, prop), (`h, v `B)] (v `h)),
    lean := "declTypeMismatch", now := "rejected", amended := "rejected", rule := "D4",
    what := "claims A → A; the proof is a function from B" },
  { id := "decl.domain-needs-unfolding",
    subject := whole `bdUnfold
      (foralls [(`A, prop)] (arrow (hidden (v `A)) (v `A)))
      (funs [(`A, prop), (`h, v `A)] (v `h)),
    lean := "accepted", now := "unknown", amended := "accepted", rule := "A1",
    what := "claims bdId Prop A → A; equal to A → A only by unfolding bdId" },
  { id := "decl.domain-needs-unfolding-wrong-claim",
    subject := whole `bdUnfoldWrong
      (foralls [(`A, prop), (`B, prop)] (arrow (hidden (v `A)) (arrow (v `B) (v `A))))
      (funs [(`A, prop), (`B, prop), (`h, v `A), (`k, v `B)] (v `k)),
    lean := "declTypeMismatch", now := "unknown", amended := "rejected", rule := "defeq",
    what := "wrong claim behind a domain that needs unfolding" },
  { id := "decl.argument-beta-domain",
    subject := argument `bdArgument
      [(`A, prop), (`k, arrow (arrow (v `A) (v `A)) (v `A))] (v `A)
      (funs [(`h, betaProp (v `A))] (v `h)) (arrow (v `A) (v `A)),
    lean := "accepted", now := "unknown", amended := "accepted", rule := "A1+B1",
    what := "k expects A → A and gets fun h : (fun T => T) A => h" },
  { id := "decl.argument-beta-domain-wrong-body",
    subject := argument `bdArgumentWrong
      [(`A, prop), (`B, prop), (`k, arrow (arrow (v `A) (v `B)) (v `A))] (v `A)
      (funs [(`h, betaProp (v `A))] (v `h)) (arrow (v `A) (v `B)),
    lean := "appTypeMismatch", now := "unknown", amended := "rejected", rule := "D4+B1",
    what := "k expects A → B and gets a function from (fun T => T) A to A" },
  { id := "decl.argument-domain-apart",
    subject := argument `bdArgumentApart
      [(`A, prop), (`B, prop), (`k, arrow (arrow (v `B) (v `A)) (v `A))] (v `A)
      (funs [(`h, betaProp (v `A))] (v `h)) (arrow (v `B) (v `A)),
    lean := "appTypeMismatch", now := "rejected", amended := "rejected", rule := "D4",
    what := "k expects a function from B and gets one from (fun T => T) A" },
  { id := "decl.lambda-in-argument",
    subject := whole `bdLambda
      (foralls [(`A, type), (`P, arrow (arrow (v `A) (v `A)) prop),
                (`q, app (v `P) [funs [(`x, v `A)] (v `x)])]
        (app (v `P) [funs [(`x, betaType (v `A))] (v `x)]))
      (funs [(`A, type), (`P, arrow (arrow (v `A) (v `A)) prop),
             (`q, app (v `P) [funs [(`x, v `A)] (v `x)])] (v `q)),
    lean := "accepted", now := "unknown", amended := "accepted", rule := "A1+B1",
    what := "P (fun x : A => x) used as P (fun x : (fun T => T) A => x)" },
  { id := "decl.lambda-in-argument-wrong-body",
    subject := whole `bdLambdaWrong
      (foralls [(`A, type), (`P, arrow (arrow (v `A) (arrow (v `A) (v `A))) prop),
                (`q, app (v `P) [funs [(`x, v `A), (`y, v `A)] (v `x)])]
        (app (v `P) [funs [(`x, betaType (v `A)), (`y, v `A)] (v `y)]))
      (funs [(`A, type), (`P, arrow (arrow (v `A) (arrow (v `A) (v `A))) prop),
             (`q, app (v `P) [funs [(`x, v `A), (`y, v `A)] (v `x)])] (v `q)),
    lean := "declTypeMismatch", now := "unknown", amended := "rejected", rule := "D5+B1",
    what := "P (fun x y => x) used as P (fun x y => y), first domains equal by beta" }
]

def cases : List Case := compareCases ++ declareCases

/-- The local context of `context`: each name is the free variable `v name`. -/
def localContext (context : List Binder) : LocalContext :=
  context.foldl (fun lctx (n, t) => lctx.mkLocalDecl ⟨n⟩ n t) {}

/-- The type Lean's kernel infers for `term` in `lctx`. -/
def inferIn (env : Environment) (lctx : LocalContext) (id : String) (term : Expr) :
    CommandElabM Expr :=
  match Kernel.check env lctx term with
  | .ok type => pure type
  | .error _ => throwError "{id}: Lean's kernel rejected a term"

/-- Lean's comparison of two well-typed, structurally different binders, in
both orders; fails unless both orders agree. -/
def compareIn (env : Environment) (lctx : LocalContext) (id : String) (left right : Expr) :
    CommandElabM Bool := do
  if left == right then throwError "{id}: the two terms are structurally equal"
  unless left.isBinding && right.isBinding do throwError "{id}: a term is not a binder"
  discard <| inferIn env lctx id left
  discard <| inferIn env lctx id right
  let forward ← match Kernel.isDefEq env lctx left right with
    | .ok answer => pure answer
    | .error _ => throwError "{id}: Lean's comparison raised an exception"
  let backward ← match Kernel.isDefEq env lctx right left with
    | .ok answer => pure answer
    | .error _ => throwError "{id}: Lean's reversed comparison raised an exception"
  unless forward == backward do
    throwError "{id}: Lean's answer depends on the order of the operands"
  pure forward

end BinderDomains

open BinderDomains in
run_cmd do
  let env ← getEnv
  let base := env.toKernelEnv
  IO.println "id\tlean\tnow\tamended\trule"
  for c in cases do
    let got ← match c.subject with
      | .compare left right => do
        pure (if (← compareIn env {} c.id left right) then "equal" else "different")
      | .declare decl context term expected => do
        -- The comparison inside the declaration must explain Lean's verdict.
        let lctx := localContext context
        let found ← inferIn env lctx c.id term
        let equal ← compareIn env lctx c.id found expected
        unless equal == (c.lean == "accepted") do
          throwError "{c.id}: the comparison does not explain Lean's verdict {c.lean}"
        pure (verdict (base.addDeclCore 1000000 1000 decl none))
    unless got == c.lean do
      throwError "{c.id}: Lean's answer is {got}, expected {c.lean}"
    -- LeanForth's answers may be cautious (unknown) but never contradict Lean.
    let vocabulary := match c.subject with
      | .compare .. => ["equal", "apart", "unknown"]
      | .declare .. => ["accepted", "rejected", "unknown"]
    let leanSaysYes := got == "equal" || got == "accepted"
    for answer in [c.now, c.amended] do
      unless vocabulary.contains answer do
        throwError "{c.id}: {answer} is not a LeanForth answer for this row"
      let yes := answer == "equal" || answer == "accepted"
      let no := answer == "apart" || answer == "rejected"
      if (yes && !leanSaysYes) || (no && leanSaysYes) then
        throwError "{c.id}: LeanForth's answer {answer} contradicts Lean's {got}"
    IO.println s!"{c.id}\t{got}\t{c.now}\t{c.amended}\t{c.rule}"

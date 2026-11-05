import Lean

/-!
# First checker: expected results against the pinned Lean 4.35.0 kernel

Reference observations for LeanForth's first checker: plan task 2.1.4, rules
in `docs/adr/0011-definite-rejection.md`, readable table in
`docs/reviews/FIRST_CHECKER_EXPECTED.md`.

For each of the five pinned fixtures (`composition`, `identity`,
`type-identity`, `poly-identity` and the constant fixture) this file builds
the original kernel declaration and deliberately broken copies, plus a group
of declarations outside the first checker's scope. Each case is added to a
scratch copy of Lean's kernel environment with `Kernel.Environment.addDeclCore`
(full checking); the run fails unless Lean's verdict -- accepted, or the exact
kind of kernel exception -- is the one recorded here. Nothing is added to this
file's own environment, so no case can make another case, or any other
reference check, pass.

Every case also names the outcome LeanForth's first checker must give and the
ADR 0011 rule behind it. Lean does not check that column: it is the
specification for the later LeanForth differential (plan task 2.2.1).

The file prints one tab-separated row per case; `first-checker-check.sh`
compares the rows with `first-checker-expected.tsv`. These are reference
observations, not a LeanForth checker, importer or theorem-acceptance path.
-/

open Lean Elab Command

universe u

/-! The five fixtures exactly as in `tests/reference/*.lean`, elaborated in a
namespace so that the hand-built originals below can be compared with what
Lean itself produces (and exports, see `export-check.sh`). -/
namespace FirstCheckerSource

theorem composition {A B C : Prop} (f : A → B) (g : B → C) : A → C :=
  fun value => g (f value)

theorem identity {P : Prop} (proof : P) : P := proof

theorem type_identity {A : Type} {P : A → Prop} {x : A} (proof : P x) : P x := proof

theorem poly_identity {A : Sort u} {P : A → Prop} {x : A} (proof : P x) : P x := proof

def fixtureId {α : Sort u} (x : α) : α := x

def fixturePoly {α : Sort u} (x : α) : α := fixtureId x

theorem fixtureUse {P : Prop} (h : P) : P := fixtureId h

end FirstCheckerSource

namespace FirstChecker

/-! ## Building terms

Terms are written with named variables (`v`) and closed by `foralls`/`funs`,
which turn each binder's name into a de Bruijn index (`Expr.abstract`). The
kernel rejects any leftover named variable (`declHasFVars`), so a slip in a
builder cannot pass silently. -/

/-- A variable by name, bound later by `foralls` or `funs`. -/
def v (n : Name) : Expr := .fvar ⟨n⟩

abbrev Binder := Name × Expr × BinderInfo

/-- An explicit binder `(n : t)`. -/
def ex (n : Name) (t : Expr) : Binder := (n, t, .default)

/-- An implicit binder `{n : t}`. -/
def im (n : Name) (t : Expr) : Binder := (n, t, .implicit)

/-- `∀ bs, body`. -/
def foralls (bs : List Binder) (body : Expr) : Expr :=
  bs.foldr (fun (n, t, bi) b => .forallE n t (b.abstract #[v n]) bi) body

/-- `fun bs => body`. -/
def funs (bs : List Binder) (body : Expr) : Expr :=
  bs.foldr (fun (n, t, bi) b => .lam n t (b.abstract #[v n]) bi) body

/-- The non-dependent function type `a → b`. -/
def arrow (a b : Expr) : Expr := .forallE `a a b .default

/-- `f a₁ … aₙ`. -/
def app (f : Expr) (args : List Expr) : Expr := mkAppN f args.toArray

def prop : Expr := .sort .zero
def type : Expr := .sort (.succ .zero)
def lu : Level := .param `u
def lv : Level := .param `v

def thm (n : Name) (t val : Expr) (ps : List Name := []) : Declaration :=
  .thmDecl { name := n, levelParams := ps, type := t, value := val }

def defn (n : Name) (t val : Expr) (ps : List Name := []) (height : UInt32 := 1)
    (safety := DefinitionSafety.safe) : Declaration :=
  .defnDecl { name := n, levelParams := ps, type := t, value := val,
              hints := .regular height, safety }

/-! ## Lean's verdict -/

/-- A short, stable name for the kernel's answer. Messages of `other` are
matched by their fixed prefixes in Lean 4.35.0's `src/kernel/*.cpp`; any other
message is printed in full and so fails the comparison. -/
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
    | .other msg =>
      if msg.startsWith "incorrect number of universe levels parameters" then
        "levelCount"
      else if msg.startsWith "invalid reference to undefined universe level parameter" then
        "undefinedLevelParam"
      else if msg.startsWith "failed to add declaration to environment, duplicate universe level parameter" then
        "duplicateLevelParam"
      else if msg.startsWith "type checker does not support loose bound variables" then
        "looseBVar"
      else
        "other: " ++ msg
    | .deterministicTimeout => "deterministicTimeout"
    | .excessiveMemory => "excessiveMemory"
    | .deepRecursion => "deepRecursion"
    | .interrupted => "interrupted"

/-- One row of the expected-results table. -/
structure Case where
  id : String
  /-- Earlier declarations, added in order; Lean must accept each. -/
  before : List Declaration := []
  decl : Declaration
  /-- Lean's expected verdict (checked here). -/
  lean : String
  /-- LeanForth's required outcome (not checked by Lean). -/
  leanforth : String
  /-- The ADR 0011 rule that decides LeanForth's outcome. -/
  rule : String
  /-- What was changed, in a few words. -/
  what : String

/-! ## composition: `∀ {A B C : Prop}, (A → B) → (B → C) → A → C` -/

def compositionType (s gDom result : Expr) : Expr :=
  foralls [im `A s, im `B s, im `C s, ex `f (arrow (v `A) (v `B)), ex `g gDom]
    (arrow (v `A) result)

def compositionValue (s gDom body : Expr) : Expr :=
  funs [im `A s, im `B s, im `C s, ex `f (arrow (v `A) (v `B)), ex `g gDom,
        ex `value (v `A)] body

def gBC : Expr := arrow (v `B) (v `C)
def gOfF : Expr := app (v `g) [app (v `f) [v `value]]

def composition : Declaration :=
  thm `composition (compositionType prop gBC (v `C)) (compositionValue prop gBC gOfF)

def compositionCases : List Case := [
  { id := "composition.original", decl := composition,
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "the pinned fixture" },
  { id := "composition.wrong-intermediate",
    decl := thm `composition_invalid (compositionType prop (arrow (v `C) (v `C)) (v `C))
      (compositionValue prop (arrow (v `C) (v `C)) gOfF),
    lean := "appTypeMismatch", leanforth := "rejected", rule := "D3",
    what := "g : C → C, so g receives a B where it needs a C" },
  { id := "composition.wrong-argument",
    decl := thm `composition_wrong_argument (compositionType prop gBC (v `C))
      (compositionValue prop gBC (app (v `g) [v `value])),
    lean := "appTypeMismatch", leanforth := "rejected", rule := "D3",
    what := "g value: g receives an A where it needs a B" },
  { id := "composition.wrong-declared-type",
    decl := thm `composition_wrong_type (compositionType prop gBC (v `B))
      (compositionValue prop gBC gOfF),
    lean := "declTypeMismatch", leanforth := "rejected", rule := "D4",
    what := "claims A → B; the proof gives A → C" },
  { id := "composition.theorem-over-types",
    decl := thm `composition_types (compositionType type gBC (v `C))
      (compositionValue type gBC gOfF),
    lean := "thmTypeIsNotProp", leanforth := "rejected", rule := "S3",
    what := "A B C : Type, so the statement is a type, not a proposition" },
  { id := "composition.definition-over-types",
    decl := defn `composition_types_def (compositionType type gBC (v `C))
      (compositionValue type gBC gOfF),
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "the same term as a definition is fine" },
  { id := "composition.applies-a-non-function",
    decl := thm `composition_non_function (compositionType prop gBC (v `C))
      (compositionValue prop gBC (app (v `g) [app (v `value) [v `value]])),
    lean := "funExpected", leanforth := "rejected", rule := "F1",
    what := "value value: value : A is not a function" },
  { id := "composition.proof-irrelevance",
    decl := thm `composition_irrelevant
      (foralls [im `A prop, im `B prop, ex `f (arrow (v `A) (v `B)), ex `f' (arrow (v `A) (v `B)),
                ex `Q (arrow (v `B) prop), ex `a (v `A), ex `h (app (v `Q) [app (v `f) [v `a]])]
        (app (v `Q) [app (v `f') [v `a]]))
      (funs [im `A prop, im `B prop, ex `f (arrow (v `A) (v `B)), ex `f' (arrow (v `A) (v `B)),
             ex `Q (arrow (v `B) prop), ex `a (v `A), ex `h (app (v `Q) [app (v `f) [v `a]])]
        (v `h)),
    lean := "accepted", leanforth := "unknown", rule := "K2",
    what := "Q (f a) used as Q (f' a): f a and f' a are both proofs of B, so Lean equates them" }
]

/-! ## identity: `∀ {P : Prop}, P → P` -/

def identityType (s : Expr) : Expr := foralls [im `P s, ex `proof (v `P)] (v `P)
def identityValue (s : Expr) : Expr := funs [im `P s, ex `proof (v `P)] (v `proof)

def identityCases : List Case := [
  { id := "identity.original", decl := thm `identity (identityType prop) (identityValue prop),
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "the pinned fixture" },
  { id := "identity.wrong-binder",
    decl := thm `identity_wrong_binder
      (foralls [im `P prop, im `Q prop, ex `first (v `P), ex `second (v `Q)] (v `Q))
      (funs [im `P prop, im `Q prop, ex `first (v `P), ex `second (v `Q)] (v `first)),
    lean := "declTypeMismatch", leanforth := "rejected", rule := "D4",
    what := "returns the proof of P where Q is claimed" },
  { id := "identity.returns-the-proposition",
    decl := thm `identity_returns_prop (identityType prop)
      (funs [im `P prop, ex `proof (v `P)] (v `P)),
    lean := "declTypeMismatch", leanforth := "rejected", rule := "D2",
    what := "returns P itself, whose type is Prop, not P" },
  { id := "identity.type-is-not-a-type",
    decl := thm `identity_non_type (identityValue prop) (identityValue prop),
    lean := "typeExpected", leanforth := "rejected", rule := "S1",
    what := "the declared type is a function, not a type" },
  { id := "identity.theorem-over-types",
    decl := thm `identity_types (identityType type) (identityValue type),
    lean := "thmTypeIsNotProp", leanforth := "rejected", rule := "S3",
    what := "P : Type, so the statement is a type, not a proposition" },
  { id := "identity.definition-over-types",
    decl := defn `identity_types_def (identityType type) (identityValue type),
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "the same term as a definition is fine" },
  { id := "identity.loose-bound-variable",
    decl := thm `identity_loose (identityType prop)
      (.lam `P prop (.lam `proof (.bvar 0) (.bvar 2) .default) .implicit),
    lean := "looseBVar", leanforth := "invalid", rule := "V1",
    what := "the body refers to a binder that does not exist" },
  { id := "identity.unknown-constant",
    decl := thm `identity_unknown (identityType prop)
      (funs [im `P prop, ex `proof (v `P)] (app (.const `LeanForthMissing []) [v `P, v `proof])),
    lean := "unknownConstant", leanforth := "rejected", rule := "N1",
    what := "uses a name that was never declared" },
  { id := "identity.let",
    decl := thm `identity_let (identityType prop)
      (funs [im `P prop, ex `proof (v `P)] (.letE `copy (v `P) (v `proof) (.bvar 0) false)),
    lean := "accepted", leanforth := "unsupported", rule := "U2",
    what := "the proof is let copy := proof; copy (a let expression)" },
  { id := "identity.binder-annotation-differs",
    decl := thm `identity_explicit (identityType prop)
      (funs [ex `P prop, ex `proof (v `P)] (v `proof)),
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "explicit binder in the proof, implicit in the statement" }
]

/-! ## type-identity: `∀ {A : Type} {P : A → Prop} {x : A}, P x → P x` -/

def typeIdentityBinders (sA pCod : Expr) : List Binder :=
  [im `A sA, im `P (arrow (v `A) pCod), im `x (v `A), ex `proof (app (v `P) [v `x])]

def typeIdentityType (sA pCod : Expr) : Expr :=
  foralls (typeIdentityBinders sA pCod) (app (v `P) [v `x])

def typeIdentityValue (sA pCod : Expr) : Expr :=
  funs (typeIdentityBinders sA pCod) (v `proof)

/-- Binders with a second point `y`, for the wrong-argument pair. -/
def twoPointBinders (sA : Expr) : List Binder :=
  [im `A sA, im `P (arrow (v `A) prop), im `x (v `A), im `y (v `A),
   ex `proof (app (v `P) [v `x])]

/-- Binders for the eta case: `k` receives `P` or `fun y => P y`. -/
def etaBinders : List Binder :=
  [im `A type, im `P (arrow (v `A) prop), ex `k (arrow (arrow (v `A) prop) prop),
   ex `h (app (v `k) [v `P])]

def typeIdentityCases : List Case := [
  { id := "type-identity.original",
    decl := thm `type_identity (typeIdentityType type prop) (typeIdentityValue type prop),
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "the pinned fixture" },
  { id := "type-identity.wrong-universe",
    decl := thm `type_identity_wrong_universe (typeIdentityType type prop)
      (typeIdentityValue prop prop),
    lean := "declTypeMismatch", leanforth := "rejected", rule := "D1",
    what := "the proof takes A : Prop where the statement says A : Type" },
  { id := "type-identity.wrong-argument",
    decl := thm `type_identity_wrong_argument
      (foralls (twoPointBinders type) (app (v `P) [v `y]))
      (funs (twoPointBinders type) (v `proof)),
    lean := "declTypeMismatch", leanforth := "rejected", rule := "D5",
    what := "claims P y from a proof of P x, with x y : A and A : Type" },
  { id := "type-identity.proof-irrelevance-twin",
    decl := thm `type_identity_proof_irrelevant
      (foralls (twoPointBinders prop) (app (v `P) [v `y]))
      (funs (twoPointBinders prop) (v `proof)),
    lean := "accepted", leanforth := "unknown", rule := "K2",
    what := "the same with A : Prop: x and y are proofs, so Lean equates them" },
  { id := "type-identity.eta-twin",
    decl := thm `type_identity_eta
      (foralls etaBinders (app (v `k) [funs [ex `y (v `A)] (app (v `P) [v `y])]))
      (funs etaBinders (v `h)),
    lean := "accepted", leanforth := "unknown", rule := "K3",
    what := "k P versus k (fun y => P y): equal only by eta" },
  { id := "type-identity.beta",
    decl := thm `type_identity_beta
      (foralls (typeIdentityBinders type prop)
        (app (funs [ex `y (v `A)] (app (v `P) [v `y])) [v `x]))
      (typeIdentityValue type prop),
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "claims (fun y => P y) x, which beta-reduces to P x" },
  { id := "type-identity.binder-is-not-a-type",
    decl := thm `type_identity_non_type
      (foralls [im `A type, im `P (arrow (v `A) prop), im `x (v `A), ex `proof (v `x)]
        (app (v `P) [v `x]))
      (funs [im `A type, im `P (arrow (v `A) prop), im `x (v `A), ex `proof (v `x)]
        (v `proof)),
    lean := "typeExpected", leanforth := "rejected", rule := "S2",
    what := "proof : x, but x : A is a value, not a type" },
  { id := "type-identity.applies-a-non-function",
    decl := thm `type_identity_non_function
      (foralls [im `A type, im `P (v `A), im `x (v `A), ex `proof (app (v `P) [v `x])]
        (app (v `P) [v `x]))
      (funs [im `A type, im `P (v `A), im `x (v `A), ex `proof (app (v `P) [v `x])]
        (v `proof)),
    lean := "funExpected", leanforth := "rejected", rule := "F1",
    what := "P : A is not a function, so P x is meaningless" },
  { id := "type-identity.theorem-over-types",
    decl := thm `type_identity_types (typeIdentityType type type)
      (typeIdentityValue type type),
    lean := "thmTypeIsNotProp", leanforth := "rejected", rule := "S3",
    what := "P : A → Type, so the statement is a type, not a proposition" },
  { id := "type-identity.definition-over-types",
    decl := defn `type_identity_types_def (typeIdentityType type type)
      (typeIdentityValue type type),
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "the same term as a definition is fine" }
]

/-! ## poly-identity: `∀ {A : Sort u} {P : A → Prop} {x : A}, P x → P x` -/

def sortU : Expr := .sort lu

/-- Two spellings of `Prop` that only Lean's level normalisation sees. -/
def sortImaxU0 : Expr := .sort (.imax lu .zero)
def sortMaxZero : Expr := .sort (.max .zero .zero)

/-- `P y` from a proof of `P x`, with `A : sA` (the `proof-irrelevance-twin` pair). -/
def twinType (sA : Expr) : Expr := foralls (twoPointBinders sA) (app (v `P) [v `y])
def twinValue (sA : Expr) : Expr := funs (twoPointBinders sA) (v `proof)

def polyIdentityCases : List Case := [
  { id := "poly-identity.original",
    decl := thm `poly_identity (typeIdentityType sortU prop) (typeIdentityValue sortU prop)
      [`u],
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "the pinned fixture" },
  { id := "poly-identity.undeclared-universe",
    decl := thm `poly_identity_undeclared (typeIdentityType sortU prop)
      (typeIdentityValue sortU prop) [],
    lean := "undefinedLevelParam", leanforth := "rejected", rule := "L2",
    what := "uses universe u without declaring it" },
  { id := "poly-identity.repeated-universe",
    decl := thm `poly_identity_repeated (typeIdentityType sortU prop)
      (typeIdentityValue sortU prop) [`u, `u],
    lean := "duplicateLevelParam", leanforth := "rejected", rule := "L3",
    what := "declares universe u twice" },
  { id := "poly-identity.wrong-universe",
    decl := thm `poly_identity_wrong_universe (typeIdentityType sortU prop)
      (typeIdentityValue (.sort (.succ lu)) prop) [`u],
    lean := "declTypeMismatch", leanforth := "rejected", rule := "D1",
    what := "the proof takes A : Sort (u+1) where the statement says Sort u" },
  { id := "poly-identity.swapped-universe",
    decl := thm `poly_identity_swapped (typeIdentityType sortU prop)
      (typeIdentityValue (.sort lv) prop) [`u, `v],
    lean := "declTypeMismatch", leanforth := "rejected", rule := "D1",
    what := "the proof takes A : Sort v where the statement says Sort u" },
  { id := "poly-identity.theorem-over-sort-u",
    decl := thm `poly_identity_sort_u (typeIdentityType sortU sortU)
      (typeIdentityValue sortU sortU) [`u],
    lean := "thmTypeIsNotProp", leanforth := "rejected", rule := "S3",
    what := "P : A → Sort u: a proposition only when u = 0, so not for every u" },
  { id := "poly-identity.definition-over-sort-u",
    decl := defn `poly_identity_sort_u_def (typeIdentityType sortU sortU)
      (typeIdentityValue sortU sortU) [`u],
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "the same term as a definition is fine" },
  { id := "poly-identity.equal-universe-other-spelling",
    decl := thm `poly_identity_max (typeIdentityType sortU prop)
      (typeIdentityValue (.sort (.max lu lu)) prop) [`u],
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "the proof writes Sort (max u u); Lean's level normalisation equates it with Sort u (ADR 0011 Amendment 1)" },
  { id := "poly-identity.proof-irrelevance-imax",
    decl := thm `poly_identity_imax (twinType sortImaxU0) (twinValue sortImaxU0) [`u],
    lean := "accepted", leanforth := "unknown", rule := "K2",
    what := "P y from a proof of P x, A : Sort (imax u 0), which is Prop for every u: x and y are proofs" },
  { id := "poly-identity.proof-irrelevance-max-zero",
    decl := thm `poly_identity_max_zero (twinType sortMaxZero) (twinValue sortMaxZero),
    lean := "accepted", leanforth := "unknown", rule := "K2",
    what := "the same with A : Sort (max 0 0), which is Prop" }
]

/-! ## The constant fixture: `fixtureId`, `fixturePoly`, `fixtureUse` -/

def fixtureIdType : Expr := foralls [im `α sortU, ex `x (v `α)] (v `α)
def fixtureIdValue : Expr := funs [im `α sortU, ex `x (v `α)] (v `x)
def fixtureId : Declaration := defn `fixtureId fixtureIdType fixtureIdValue [`u] 1

def fixturePolyWith (n : Name) (head : Expr) : Declaration :=
  defn n fixtureIdType (funs [im `α sortU, ex `x (v `α)] (app head [v `α, v `x])) [`u] 2

def fixturePoly : Declaration := fixturePolyWith `fixturePoly (.const `fixtureId [lu])

def implication : Expr := foralls [im `P prop, ex `h (v `P)] (v `P)
def implicationProof (body : Expr) : Expr := funs [im `P prop, ex `h (v `P)] body

def fixtureUseWith (n : Name) (body : Expr) : Declaration :=
  thm n implication (implicationProof body)

def fixtureUse : Declaration :=
  fixtureUseWith `fixtureUse (app (.const `fixtureId [.zero]) [v `P, v `h])

/-- `@fixtureId.{1} Prop q`: equal to `q`, but only by unfolding `fixtureId`. -/
def hidden (q : Expr) : Expr := app (.const `fixtureId [.succ .zero]) [prop, q]

def fixtureUnfold : Declaration :=
  thm `fixtureUnfold (foralls [im `P prop, ex `h (v `P)] (hidden (v `P)))
    (implicationProof (v `h))

def constantCases : List Case := [
  { id := "constant.fixtureId", decl := fixtureId,
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "the pinned polymorphic identity definition" },
  { id := "constant.fixturePoly", before := [fixtureId], decl := fixturePoly,
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "the pinned definition that uses fixtureId.{u}" },
  { id := "constant.fixtureUse", before := [fixtureId], decl := fixtureUse,
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "the pinned theorem that uses fixtureId.{0}" },
  { id := "constant.forward-reference", decl := fixturePoly,
    lean := "unknownConstant", leanforth := "rejected", rule := "N1",
    what := "fixturePoly checked before fixtureId exists" },
  { id := "constant.self-reference", before := [fixtureId],
    decl := fixturePolyWith `fixturePoly (.const `fixturePoly [lu]),
    lean := "unknownConstant", leanforth := "rejected", rule := "N1",
    what := "fixturePoly uses itself, which a non-recursive definition cannot" },
  { id := "constant.duplicate-name", before := [fixtureId], decl := fixtureId,
    lean := "alreadyDeclared", leanforth := "rejected", rule := "N2",
    what := "fixtureId declared a second time" },
  { id := "constant.too-few-universes", before := [fixtureId],
    decl := fixturePolyWith `fixturePoly (.const `fixtureId []),
    lean := "levelCount", leanforth := "rejected", rule := "L1",
    what := "fixtureId used with no universe argument; it takes one" },
  { id := "constant.too-many-universes", before := [fixtureId],
    decl := fixturePolyWith `fixturePoly (.const `fixtureId [lu, lu]),
    lean := "levelCount", leanforth := "rejected", rule := "L1",
    what := "fixtureId used with two universe arguments; it takes one" },
  { id := "constant.wrong-universe-argument", before := [fixtureId],
    decl := fixtureUseWith `fixtureUse (app (.const `fixtureId [.succ .zero]) [v `P, v `h]),
    lean := "appTypeMismatch", leanforth := "rejected", rule := "D1",
    what := "fixtureId.{1} expects a Type; P is a Prop" },
  { id := "constant.wrong-argument", before := [fixtureId],
    decl := fixtureUseWith `fixtureUse (app (.const `fixtureId [.zero]) [v `P, v `P]),
    lean := "appTypeMismatch", leanforth := "rejected", rule := "D2",
    what := "passes P (a proposition) where a proof of P is needed" },
  { id := "constant.needs-unfolding", before := [fixtureId], decl := fixtureUnfold,
    lean := "accepted", leanforth := "unknown", rule := "K1",
    what := "claims fixtureId Prop P from a proof of P: true by unfolding fixtureId" },
  { id := "constant.needs-unfolding-wrong", before := [fixtureId],
    decl := thm `fixtureUnfoldWrong
      (foralls [im `P prop, im `Q prop, ex `h (v `P)] (hidden (v `Q)))
      (funs [im `P prop, im `Q prop, ex `h (v `P)] (v `h)),
    lean := "declTypeMismatch", leanforth := "unknown", rule := "K1",
    what := "claims fixtureId Prop Q from a proof of P: false, but only unfolding shows it" },
  { id := "constant.uses-an-undecided-declaration", before := [fixtureId, fixtureUnfold],
    decl := thm `fixtureUnfoldUse (foralls [im `P prop, ex `h (v `P)] (hidden (v `P)))
      (implicationProof (app (.const `fixtureUnfold []) [v `P, v `h])),
    lean := "accepted", leanforth := "unknown", rule := "K5",
    what := "cites fixtureUnfold, which LeanForth could not decide" },
  { id := "constant.theorem-cites-theorem", before := [fixtureId, fixtureUse],
    decl := fixtureUseWith `fixtureUseAgain (app (.const `fixtureUse []) [v `P, v `h]),
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "a theorem whose proof cites the earlier theorem fixtureUse" },
  { id := "constant.over-application", before := [fixtureId, fixtureUse],
    decl := fixtureUseWith `fixtureOverApplied
      (app (.const `fixtureUse []) [v `P, v `h, v `h]),
    lean := "funExpected", leanforth := "rejected", rule := "F1",
    what := "fixtureUse h is a proof of P, not a function, but is applied to h" },
  { id := "constant.function-type-behind-definition", before := [fixtureId],
    decl := thm `fixtureHiddenArrow
      (foralls [im `P prop, ex `f (hidden (arrow (v `P) (v `P))), ex `h (v `P)] (v `P))
      (funs [im `P prop, ex `f (hidden (arrow (v `P) (v `P))), ex `h (v `P)]
        (app (v `f) [v `h])),
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "f's type is fixtureId Prop (P → P); it is a function type only after unfolding (Lean's whnf in ensure_pi, since plan task 4.2.2c; K1 unknown before)" },
  { id := "constant.sort-behind-definition", before := [fixtureId],
    decl := thm `fixtureHiddenSort
      (foralls [im `Q (app (.const `fixtureId [.succ (.succ .zero)]) [type, prop]),
                ex `h (v `Q)] (v `Q))
      (funs [im `Q (app (.const `fixtureId [.succ (.succ .zero)]) [type, prop]),
             ex `h (v `Q)] (v `h)),
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "Q : fixtureId Type Prop; Q is a proposition only after unfolding (Lean's whnf in ensure_sort, since plan task 4.2.2c; K1 unknown before)" }
]

/-! ## Outside the first checker's scope (Lean accepts; LeanForth must not) -/

def assumed : Declaration :=
  .axiomDecl { name := `scopeAssumed, levelParams := [], type := implication, isUnsafe := false }

def scopeCases : List Case := [
  { id := "scope.metadata",
    decl := thm `scopeMetadata implication (implicationProof (.mdata {} (v `h))),
    lean := "accepted", leanforth := "unsupported", rule := "U2",
    what := "a metadata node in the proof" },
  { id := "scope.number-literal",
    decl := defn `scopeNumber (.const ``Nat []) (.lit (.natVal 3)),
    lean := "accepted", leanforth := "unsupported", rule := "U2",
    what := "the number 3, a literal of the data type Nat" },
  { id := "scope.postulate", decl := assumed,
    lean := "accepted", leanforth := "unsupported", rule := "U1",
    what := "a statement assumed without proof; the allowlist is empty" },
  { id := "scope.uses-postulate", before := [assumed],
    decl := thm `scopeUsesAssumed implication
      (implicationProof (app (.const `scopeAssumed []) [v `P, v `h])),
    lean := "accepted", leanforth := "unsupported", rule := "K5",
    what := "a proof that cites the assumed statement" },
  { id := "scope.opaque",
    decl := .opaqueDecl { name := `scopeOpaque, levelParams := [`u], type := fixtureIdType,
                          value := fixtureIdValue, isUnsafe := false },
    lean := "accepted", leanforth := "unsupported", rule := "U1",
    what := "an opaque declaration (never unfolds)" },
  { id := "scope.unsafe-definition",
    decl := defn `scopeUnsafe fixtureIdType fixtureIdValue [`u] (safety := .unsafe),
    lean := "accepted", leanforth := "unsupported", rule := "U1",
    what := "a definition marked unsafe" },
  { id := "scope.partial-definition",
    decl := defn `scopePartial fixtureIdType fixtureIdValue [`u] (safety := .partial),
    lean := "accepted", leanforth := "unsupported", rule := "U1",
    what := "a definition marked partial" }
]

/-! ## A Π whose body is not a type (rule S4, ADR 0011 Amendment 2)

Lean's `infer_pi` requires the body's type to be a `Sort` too
(`ensure_sort_core`, `type_checker.cpp` 158): `typeExpected` otherwise.
LeanForth rejects only when the body's type, after weak-head beta
reduction, is rigid and not a `Sort`; behind a constant it stays unknown
(K1), as Lean may unfold it either way. -/

def sort2 : Expr := .sort (.succ (.succ .zero))
/-- `S1 : Sort 2 := Type` and `F1 : Type := Prop → Prop`, to unfold. -/
def s1 : Declaration := defn `S1 sort2 type
def f1 : Declaration := defn `F1 type (foralls [ex `p prop] prop)

def piBodyCases : List Case := [
  { id := "pi-body.variable",
    decl := defn `piBodyVariable sort2 (foralls [ex `A type, ex `a (v `A)] (v `a)),
    lean := "typeExpected", leanforth := "rejected", rule := "S4",
    what := "(A : Type) → (a : A) → a: the body a is a value of type A, not a type" },
  { id := "pi-body.lambda",
    decl := defn `piBodyLambda type (foralls [ex `x prop] (funs [ex `y prop] (v `y))),
    lean := "typeExpected", leanforth := "rejected", rule := "S4",
    what := "(x : Prop) → fun (y : Prop) => y: the body is a function" },
  { id := "pi-body.in-claim",
    decl := thm `piBodyClaim (foralls [ex `A prop, ex `a (v `A)] (v `a))
      (funs [ex `A prop, ex `a (v `A)] (v `a)),
    lean := "typeExpected", leanforth := "rejected", rule := "S4",
    what := "the claimed statement (A : Prop) → (a : A) → a has a proof as its body" },
  { id := "pi-body.type",
    decl := defn `piBodyType sort2 (foralls [ex `A type, ex `a (v `A)] (v `A)),
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "the neighbour (A : Type) → (a : A) → A: the body A is a type" },
  { id := "pi-body.proposition",
    decl := defn `piBodyProp prop (foralls [ex `x prop] (v `x)),
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "(x : Prop) → x: the body x is a proposition, a type" },
  { id := "pi-body.needs-unfolding", before := [s1],
    decl := defn `piBodyUnfold sort2 (foralls [ex `y (.const `S1 [])] (v `y)),
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "(y : S1) → y: y's type S1 unfolds to Type, a Sort (Lean's whnf in ensure_sort, since plan task 4.2.2c; K1 unknown before)" },
  { id := "pi-body.needs-unfolding-wrong", before := [f1],
    decl := defn `piBodyUnfoldWrong sort2 (foralls [ex `y (.const `F1 [])] (v `y)),
    lean := "typeExpected", leanforth := "rejected", rule := "S4",
    what := "(y : F1) → y: y's type F1 unfolds to Prop → Prop, not a Sort (Lean's whnf in ensure_sort, since plan task 4.2.2c; K1 unknown before)" }
]

def cases : List Case :=
  compositionCases ++ identityCases ++ typeIdentityCases ++ polyIdentityCases ++
    constantCases ++ scopeCases ++ piBodyCases

/-- Rename `FirstCheckerSource.n` to `n` in constant references. -/
def unqualify (e : Expr) : Expr :=
  e.replace fun
    | .const n ls => some (.const (n.replacePrefix `FirstCheckerSource .anonymous) ls)
    | _ => none

/-- The hand-built originals and the source fixtures elaborated above. -/
def originals : List (Name × Declaration) := [
  (`FirstCheckerSource.composition, composition),
  (`FirstCheckerSource.identity, thm `identity (identityType prop) (identityValue prop)),
  (`FirstCheckerSource.type_identity,
    thm `type_identity (typeIdentityType type prop) (typeIdentityValue type prop)),
  (`FirstCheckerSource.poly_identity,
    thm `poly_identity (typeIdentityType sortU prop) (typeIdentityValue sortU prop) [`u]),
  (`FirstCheckerSource.fixtureId, fixtureId),
  (`FirstCheckerSource.fixturePoly, fixturePoly),
  (`FirstCheckerSource.fixtureUse, fixtureUse)
]

/-- Type, value and universe parameters of a theorem or definition. -/
def parts : Declaration → Option (Expr × Expr × List Name)
  | .thmDecl d => some (d.type, d.value, d.levelParams)
  | .defnDecl d => some (d.type, d.value, d.levelParams)
  | _ => none

end FirstChecker

open FirstChecker in
run_cmd do
  let env ← getEnv
  -- 1. Each hand-built original is the term Lean elaborates from the fixture
  --    source (up to binder names and annotations, which the kernel ignores).
  for (source, decl) in originals do
    let some info := env.find? source | throwError "missing source fixture {source}"
    let some (type, value, params) := parts decl | throwError "unexpected original {source}"
    let some sourceValue := info.value? (allowOpaque := true) | throwError "{source} has no value"
    unless unqualify info.type == type && unqualify sourceValue == value &&
        info.levelParams == params do
      throwError "hand-built original differs from the elaborated fixture {source}"
  -- 2. Lean's kernel verdict on every case, each in its own scratch environment.
  let base := env.toKernelEnv
  IO.println "id\tlean\tleanforth\trule"
  for c in cases do
    let mut scratch := base
    for d in c.before do
      match scratch.addDeclCore 1000000 1000 d none with
      | .ok next => scratch := next
      | .error _ => throwError "{c.id}: Lean rejected a prerequisite"
    let got := verdict (scratch.addDeclCore 1000000 1000 c.decl none)
    unless got == c.lean do
      throwError "{c.id}: Lean's verdict is {got}, expected {c.lean}"
    IO.println s!"{c.id}\t{got}\t{c.leanforth}\t{c.rule}"

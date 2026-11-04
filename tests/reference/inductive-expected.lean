import Lean
import LeanExport.Basic

/-!
# Inductive types, recursors, reductions: Lean 4.35.0's kernel verdicts

Reference observations for ADR 0015 (`docs/adr/0015-inductive-types.md`, plan
task 5.1.1). Nothing here is LeanForth code: this file asks the pinned Lean
4.35.0 kernel for its verdict on small hand-written cases and fails unless
the verdict is the one recorded below. `inductive-check.sh` compares the
printed rows with `inductive-expected.tsv` byte for byte.

Five groups of cases, each added to a scratch copy of a kernel environment
with `Kernel.Environment.addDeclCore` (full checking), so no case can make
another pass:

* `ind.*`, `pos.*`, `uniform.*`, `universe.*`, `result.*`, `params.*`,
  `mutual.*`, `nested.*`, `names.*`: inductive declarations
  (`Declaration.inductDecl`) written in Lean syntax. Each type's short name is
  a local variable while its constructors are elaborated, then replaced by the
  constant `IE.<name>`; so the kernel, not the elaborator, decides. For an
  accepted block the row also prints what the kernel generated: indices,
  `isRec`, `isReflexive`, `numNested`, the recursor's elimination universe
  (`any` when the recursor has its own universe parameter for the motive,
  `Prop` when it eliminates only into `Prop`), `k`, motives, minor premises,
  the fields of each rule, and the auxiliary recursors of a nested block.
* `iota.*`, `k.*`, `eta.*`, `unit.*`, `proj.*`, `quot.*`, `lit.*`: theorems
  and definitions whose checking needs one reduction rule. Type and value are
  elaborated separately, without comparing them, and the kernel compares.
* `replay.*`: Lean's own checker for exported libraries,
  `Kernel.Environment.replay` (`src/Lean/Replay.lean`, used by
  `leanchecker`), given the constants of a small inductive block, unchanged
  and mutated. Replay rebuilds the block from the exported types and
  constructor types, lets the kernel generate the rest, and compares only the
  constructors and recursors with the exported ones.
* `primitive.*`: an empty environment in which `Nat` and `Nat.add` are
  declared by hand. The kernel computes on `Nat` literals by the names
  `Nat.add` and so on, whatever their definitions say.
* `quotinit.*`: initialising quotients (`Declaration.quotDecl`) needs `Eq`
  with exactly Lean's shape.

Columns: `id`, Lean's verdict (checked here), the outcome LeanForth must give
once its plan task is done, the ADR 0015 rule, the plan task, and the facts
of an accepted block (empty otherwise). Until its task is done LeanForth
answers *unsupported* for the row, never *accepted*.
-/

open Lean Elab Command Term Meta

universe u v

namespace InductiveExpected

/-! ## Lean's verdict -/

def has (msg pat : String) : Bool := (msg.splitOn pat).length > 1

/-- Short names for the kernel's `other` messages, matched by fixed text in
Lean 4.35.0's `src/kernel/inductive.cpp`, `type_checker.cpp` and
`environment.cpp`. Any other message is printed in full and so fails the
comparison. -/
def otherCodes : List (String × String) := [
  ("has a non positive occurrence of the datatypes being declared", "nonPositive"),
  ("contains a non valid occurrence of the datatypes being declared", "nonValidOccurrence"),
  ("is too big for the corresponding inductive datatype", "universeTooBig"),
  ("invalid return type for", "invalidReturnType"),
  ("number of parameters mismatch in inductive datatype declaration", "paramCountMismatch"),
  ("invalid inductive datatype declaration, incorrect number of parameters", "tooFewParamBinders"),
  ("does not match inductive datatypes parameters", "ctorParamMismatch"),
  ("parameters of all inductive datatypes must match", "mutualParamMismatch"),
  ("mutually inductive types must live in the same universe", "mutualUniverseMismatch"),
  ("must be applied to the parameters and universe levels of the mutual declaration",
    "nonUniformOccurrence"),
  ("nested inductive datatypes parameters cannot contain local variables", "nestedLocalVariable"),
  ("duplicate constructor name", "duplicateConstructor"),
  ("invalid empty (mutual) inductive datatype declaration", "emptyBlock"),
  ("duplicate universe level parameter", "duplicateLevelParam"),
  ("it uses the reserved prefix", "reservedNestedPrefix"),
  ("failed to initialize quot module", "quotEqShape"),
  ("incorrect number of universe levels", "universeArity")]

def otherCode (msg : String) : String :=
  match otherCodes.find? (fun (p, _) => has msg p) with
  | some (_, c) => c
  | none => "other: " ++ msg

def exceptionCode : Kernel.Exception → String
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
  | .other msg => otherCode msg
  | .deterministicTimeout => "deterministicTimeout"
  | .excessiveMemory => "excessiveMemory"
  | .deepRecursion => "deepRecursion"
  | .interrupted => "interrupted"

def verdict : Except Kernel.Exception Kernel.Environment → String
  | .ok _ => "accepted"
  | .error e => exceptionCode e

/-! ## Inductive declarations -/

/-- One type of a block: its short name, its type and its constructors (short
name and type), in Lean syntax. -/
structure Ty where
  name : String
  type : String
  ctors : List (String × String) := []

structure Block where
  id : String
  lparams : List Name := []
  nparams : Nat := 0
  types : List Ty
  /-- Namespace of the declared names; `anonymous` declares `name` itself. -/
  ns : Name := `IE
  lean : String
  leanforth : String
  rule : String
  task : String

def Block.full (b : Block) (short : String) : Name := b.ns ++ short.toName

def parseTerm (s : String) : TermElabM Syntax := do
  match Parser.runParserCategory (← getEnv) `term s with
  | .ok stx => pure stx
  | .error e => throwError "cannot parse {s}: {e}"

/-- Elaborate `s` with each `(short, full, type)` of `locals` as a variable,
then replace those variables by the constants `full.{lps}`. -/
def elabWith (locals : List (String × Name × Expr)) (lps : List Name) (s : String) :
    TermElabM Expr := do
  let stx ← parseTerm s
  let rec go (rest : List (String × Name × Expr)) (fvars : Array (Expr × Name)) :
      TermElabM Expr := do
    match rest with
    | [] =>
      let e ← elabTerm stx none
      synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      if e.hasMVar then throwError "unassigned metavariable in {s}"
      pure <| fvars.foldl (fun e (fv, n) => e.replaceFVar fv (mkConst n (lps.map .param))) e
    | (short, full, ty) :: more =>
      withLocalDeclD short.toName ty fun fv => go more (fvars.push (fv, full))
  go locals #[]

def Block.decl (b : Block) : TermElabM Declaration := do
  let tys ← b.types.mapM fun t => do
    pure (t.name, b.full t.name, ← elabWith [] b.lparams t.type)
  let types ← b.types.mapM fun t => do
    let ty ← elabWith [] b.lparams t.type
    let ctors ← t.ctors.mapM fun (c, cty) => do
      pure ({ name := b.full t.name ++ c.toName, type := ← elabWith tys b.lparams cty } :
        Constructor)
    pure ({ name := b.full t.name, type := ty, ctors } : InductiveType)
  pure (.inductDecl b.lparams b.nparams types false)

def bit (b : Bool) : String := if b then "1" else "0"

/-- What the kernel generated for an accepted block. -/
def facts (env : Kernel.Environment) (b : Block) : String :=
  let one (t : Ty) : String :=
    match env.find? (b.full t.name), env.find? (b.full t.name ++ `rec) with
    | some (.inductInfo i), some (.recInfo r) =>
      let elim := if r.levelParams.length > i.levelParams.length then "any" else "Prop"
      let aux := (List.range i.numNested).filterMap fun k =>
        match env.find? (b.full t.name ++ Name.mkSimple s!"rec_{k + 1}") with
        | some (.recInfo _) => some s!"rec_{k + 1}"
        | _ => none
      s!"{t.name}: idx={i.numIndices} rec={bit i.isRec} refl={bit i.isReflexive} " ++
      s!"nested={i.numNested} elim={elim} k={bit r.k} motives={r.numMotives} " ++
      s!"minors={r.numMinors} fields={r.rules.map (·.nfields)}" ++
      (if aux.isEmpty then "" else s!" aux={aux}")
    | _, _ => s!"{t.name}: not generated"
  "; ".intercalate (b.types.map one)

/-- Three-form examples of ADR 0015 and the elimination-level cases. -/
def accepted : List Block := [
  { id := "ind.nat", types := [⟨"N", "Type", [("zero", "N"), ("succ", "N → N")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1", task := "5.2.1b" },
  { id := "ind.and", nparams := 2,
    types := [⟨"And", "Prop → Prop → Prop",
      [("intro", "(a b : Prop) → a → b → And a b")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 E3", task := "5.2.1a" },
  { id := "ind.eq", lparams := [`u], nparams := 2,
    types := [⟨"Eq", "(α : Sort u) → α → α → Prop",
      [("refl", "(α : Sort u) → (a : α) → Eq α a a")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 E3 K1", task := "5.2.1c" },
  { id := "ind.bool", types := [⟨"B", "Type", [("false", "B"), ("true", "B")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1", task := "5.2.1a" },
  { id := "ind.list", lparams := [`u], nparams := 1,
    types := [⟨"L", "Type u → Type u",
      [("nil", "(α : Type u) → L α"), ("cons", "(α : Type u) → α → L α → L α")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1", task := "5.2.1b" },
  { id := "ind.vector", nparams := 1,
    types := [⟨"V", "Type → Nat → Type",
      [("nil", "(α : Type) → V α 0"),
       ("cons", "(α : Type) → (n : Nat) → α → V α n → V α (n + 1)")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1", task := "5.2.1c" },
  { id := "ind.unit", types := [⟨"U", "Type", [("unit", "U")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 R5", task := "5.2.1a" },
  { id := "ind.empty-type", types := [⟨"E", "Type", []⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1", task := "5.2.1a" },
  { id := "ind.empty-prop", types := [⟨"F", "Prop", []⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 E2", task := "5.2.1a" },
  { id := "ind.true", types := [⟨"T", "Prop", [("intro", "T")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 E3 K1", task := "5.2.1a" },
  { id := "ind.or", nparams := 2,
    types := [⟨"Or", "Prop → Prop → Prop",
      [("inl", "(a b : Prop) → a → Or a b"), ("inr", "(a b : Prop) → b → Or a b")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 E1", task := "5.2.1a" },
  { id := "ind.prop-two-empty-ctors", types := [⟨"P", "Prop", [("a", "P"), ("b", "P")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 E1", task := "5.2.1a" },
  { id := "ind.exists", lparams := [`u], nparams := 2,
    types := [⟨"Ex", "(α : Sort u) → (α → Prop) → Prop",
      [("intro", "(α : Sort u) → (p : α → Prop) → (w : α) → p w → Ex α p")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 E4", task := "5.2.1a" },
  { id := "ind.exists-prop-witness", nparams := 2,
    types := [⟨"ExP", "(α : Prop) → (α → Prop) → Prop",
      [("intro", "(α : Prop) → (p : α → Prop) → (w : α) → p w → ExP α p")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 E3", task := "5.2.1a" },
  { id := "ind.field-in-index", types := [⟨"IsZ", "Nat → Prop",
      [("mk", "(n : Nat) → n = 0 → IsZ n")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 E3", task := "5.2.1c" },
  { id := "ind.reflexive", types := [⟨"O", "Type",
      [("zero", "O"), ("lim", "(Nat → O) → O")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 P1", task := "5.2.1b" },
  { id := "ind.universe-max", lparams := [`u, `v], nparams := 2,
    types := [⟨"Pr", "Type u → Type v → Type (max u v)",
      [("mk", "(α : Type u) → (β : Type v) → α → β → Pr α β")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 U1", task := "5.2.1a" },
  { id := "ind.sort-max", lparams := [`u, `v], nparams := 2,
    types := [⟨"S", "Sort u → Sort v → Sort (max 1 u v)",
      [("inl", "(α : Sort u) → (β : Sort v) → α → S α β"),
       ("inr", "(α : Sort u) → (β : Sort v) → β → S α β")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 U1", task := "5.2.1a" },
  -- Fields typed `optParam` and `outParam`: the recursor's minor premise has them
  -- removed (`consume_type_annotations`; review rvI21 M1).
  { id := "ind.annotated-fields",
    types := [⟨"An", "Type", [("mk", "(p : optParam Prop True) → (q : outParam Prop) → An")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 G1", task := "5.2.1a" },
  -- Recursive blocks (plan task 5.2.1b): two recursive fields, a function field of two
  -- arguments, a reflexive field under a parameter, recursive propositions (Prop only,
  -- and any universe with one constructor), a list in `Sort (max 1 u)`, and fields whose
  -- type is a β-redex: one Lean's `whnf` turns into a function into the type (recursive,
  -- not reflexive: `is_reflexive` reads the raw type), one it turns into `Nat`
  -- (`is_rec` is syntactic, the field is no recursive argument).
  { id := "ind.binary-tree", types := [⟨"BT", "Type",
      [("leaf", "BT"), ("node", "BT → BT → BT")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 G1", task := "5.2.1b" },
  { id := "ind.reflexive-two-arguments", types := [⟨"R2", "Type",
      [("z", "R2"), ("f", "(Nat → Bool → R2) → R2")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 P1 G1", task := "5.2.1b" },
  { id := "ind.reflexive-parameter", nparams := 1, types := [⟨"RP", "Type → Type",
      [("leaf", "(α : Type) → α → RP α"), ("sup", "(α : Type) → (α → RP α) → RP α")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 P1 G1", task := "5.2.1b" },
  { id := "ind.recursive-predicate", types := [⟨"Ev", "Prop",
      [("base", "Ev"), ("step", "Ev → Ev")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 E1 G1", task := "5.2.1b" },
  { id := "ind.recursive-predicate-one-constructor", types := [⟨"Inf", "Prop",
      [("mk", "Inf → Inf")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 E3 G1", task := "5.2.1b" },
  { id := "ind.list-sort-max", lparams := [`u], nparams := 1,
    types := [⟨"LS", "Sort u → Sort (max 1 u)",
      [("nil", "(α : Sort u) → LS α"), ("cons", "(α : Sort u) → α → LS α → LS α")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 U1 G1", task := "5.2.1b" },
  { id := "ind.recursive-through-beta", types := [⟨"Bt", "Type",
      [("z", "Bt"), ("mk", "(fun (X : Type) => Nat → X) Bt → Bt")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 P1 G1", task := "5.2.1b" },
  { id := "ind.erased-by-beta", types := [⟨"Eb", "Type",
      [("mk", "(fun (X : Type) => Nat) Eb → Eb")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 P1 G1", task := "5.2.1b" }
]

/-- Declarations Lean rejects, each next to an accepted neighbour. -/
def checks : List Block := [
  -- Strict positivity (check_positivity).
  { id := "pos.negative", types := [⟨"Bad", "Type", [("mk", "(Bad → Nat) → Bad")]⟩],
    lean := "nonPositive", leanforth := "rejected", rule := "P1", task := "5.2.1b" },
  { id := "pos.double-negative", types := [⟨"Bad", "Type", [("mk", "((Bad → Nat) → Nat) → Bad")]⟩],
    lean := "nonPositive", leanforth := "rejected", rule := "P1", task := "5.2.1b" },
  { id := "pos.through-definition", types := [⟨"Bad", "Type", [("mk", "id (Bad → Nat) → Bad")]⟩],
    lean := "nonPositive", leanforth := "rejected", rule := "P1", task := "5.2.1b" },
  { id := "pos.erased-by-definition",
    types := [⟨"Ok", "Type", [("mk", "Function.const Type Nat Ok → Ok")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 P1", task := "5.2.1b" },
  { id := "pos.non-valid-occurrence", nparams := 1,
    types := [⟨"Bad", "(Type → Type) → Type",
      [("mk", "(f : Type → Type) → f (Bad f) → Bad f")]⟩],
    lean := "nonValidOccurrence", leanforth := "rejected", rule := "P2", task := "5.2.1b" },
  { id := "pos.universe-checked-first",
    types := [⟨"Bad", "Type", [("mk", "(f : Type → Type) → f Bad → Bad")]⟩],
    lean := "universeTooBig", leanforth := "rejected", rule := "U1", task := "5.2.1b" },
  -- The same rules where whnf only β-reduces, in a later binder, and after a Pi.
  { id := "pos.negative-through-beta",
    types := [⟨"Bad", "Type", [("mk", "(fun (X : Type) => X → Nat) Bad → Bad")]⟩],
    lean := "nonPositive", leanforth := "rejected", rule := "P1", task := "5.2.1b" },
  { id := "pos.negative-second-binder",
    types := [⟨"Bad", "Type", [("mk", "(Nat → Bad → Nat) → Bad")]⟩],
    lean := "nonPositive", leanforth := "rejected", rule := "P1", task := "5.2.1b" },
  { id := "pos.negative-later-field",
    types := [⟨"Bad", "Type", [("z", "Bad"), ("mk", "Bad → (Bad → Bad) → Bad")]⟩],
    lean := "nonPositive", leanforth := "rejected", rule := "P1", task := "5.2.1b" },
  { id := "pos.non-valid-after-pi", nparams := 1,
    types := [⟨"Bad", "(Type → Type) → Type",
      [("mk", "(f : Type → Type) → (Nat → f (Bad f)) → Bad f")]⟩],
    lean := "nonValidOccurrence", leanforth := "rejected", rule := "P2", task := "5.2.1b" },
  -- Occurrences applied to the parameters (check_uniform_ind_occs).
  { id := "uniform.other-argument", nparams := 1,
    types := [⟨"T", "Type → Type", [("mk", "(α : Type) → T Nat → T α")]⟩],
    lean := "nonUniformOccurrence", leanforth := "rejected", rule := "C1", task := "5.2.1b" },
  { id := "uniform.definitionally-equal-argument", nparams := 1,
    types := [⟨"T", "Type → Type", [("mk", "(α : Type) → T (id α) → T α")]⟩],
    lean := "nonUniformOccurrence", leanforth := "rejected", rule := "C1", task := "5.2.1b" },
  { id := "uniform.result-other-argument", nparams := 1,
    types := [⟨"T", "Type → Type", [("mk", "(α : Type) → T Nat")]⟩],
    lean := "nonUniformOccurrence", leanforth := "rejected", rule := "C1", task := "5.2.1a" },
  -- Universe constraints on constructor fields.
  { id := "universe.field-too-big", types := [⟨"Big", "Type", [("mk", "Type → Big")]⟩],
    lean := "universeTooBig", leanforth := "rejected", rule := "U1", task := "5.2.1a" },
  { id := "universe.field-too-big-param", lparams := [`u],
    types := [⟨"Big", "Type u", [("mk", "Type u → Big")]⟩],
    lean := "universeTooBig", leanforth := "rejected", rule := "U1", task := "5.2.1a" },
  { id := "universe.field-fits", lparams := [`u],
    types := [⟨"Fits", "Type (u + 1)", [("mk", "Type u → Fits")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 U1", task := "5.2.1a" },
  { id := "universe.predicate-any-field", types := [⟨"BigP", "Prop", [("mk", "Type → BigP")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 U1 E4", task := "5.2.1a" },
  { id := "universe.type-not-a-sort", types := [⟨"T", "Nat", []⟩],
    lean := "typeExpected", leanforth := "rejected", rule := "T2", task := "5.2.1a" },
  -- The same rule without `Nat` (a recursive type, task 5.2.1b), so that task 5.2.1a
  -- reaches it: the telescope ends in a variable.
  { id := "universe.type-not-a-sort-param", nparams := 1,
    types := [⟨"T", "(P : Prop) → P", []⟩],
    lean := "typeExpected", leanforth := "rejected", rule := "T2", task := "5.2.1a" },
  -- Constructor result types (is_valid_ind_app).
  { id := "result.other-type", types := [⟨"T", "Type", [("mk", "Nat")]⟩],
    lean := "invalidReturnType", leanforth := "rejected", rule := "C3", task := "5.2.1a" },
  { id := "result.other-type-sort", types := [⟨"T", "Type", [("mk", "Prop")]⟩],
    lean := "invalidReturnType", leanforth := "rejected", rule := "C3", task := "5.2.1a" },
  { id := "result.index-mentions-type", types := [⟨"T", "Type → Type", [("mk", "T (T Nat)")]⟩],
    lean := "invalidReturnType", leanforth := "rejected", rule := "C3", task := "5.2.1c" },
  -- Parameters.
  { id := "params.too-few-binders", nparams := 2, types := [⟨"T", "Type → Type", []⟩],
    lean := "tooFewParamBinders", leanforth := "rejected", rule := "T1", task := "5.2.1a" },
  -- A constructor with fewer binders than parameters and no occurrence of the type
  -- (so check_uniform_ind_occs passes): get_params refuses it (review rvI21 L1).
  { id := "params.constructor-too-few-binders", nparams := 1,
    types := [⟨"T", "Prop → Prop", [("mk", "Prop")]⟩],
    lean := "tooFewParamBinders", leanforth := "rejected", rule := "T1", task := "5.2.1a" },
  { id := "params.constructor-mismatch", nparams := 1,
    types := [⟨"T", "Type → Type", [("mk", "(β : Prop) → Nat")]⟩],
    lean := "ctorParamMismatch", leanforth := "rejected", rule := "C2", task := "5.2.1a" },
  { id := "params.constructor-mismatch-sort", nparams := 1,
    types := [⟨"T", "Type → Type", [("mk", "(β : Prop) → Prop")]⟩],
    lean := "ctorParamMismatch", leanforth := "rejected", rule := "C2", task := "5.2.1a" },
  { id := "params.constructor-binder-defeq", nparams := 1,
    types := [⟨"T", "Type → Type", [("mk", "(β : id Type) → T β")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 C2", task := "5.2.1a" },
  { id := "params.constructor-binder-beta", nparams := 1,
    types := [⟨"T", "Type → Type", [("mk", "(β : (fun (x : Type 1) => x) Type) → T β")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 C2", task := "5.2.1a" },
  { id := "params.index-instead-of-parameter", types := [⟨"T", "Type → Type",
      [("mk", "(α : Type) → α → T α")]⟩],
    lean := "universeTooBig", leanforth := "rejected", rule := "U1", task := "5.2.1c" },
  { id := "params.index-one-universe-up", types := [⟨"T", "Type → Type 1",
      [("mk", "(α : Type) → α → T α")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 U1", task := "5.2.1c" },
  -- Mutual blocks.
  { id := "mutual.even-odd",
    types := [⟨"Even", "Nat → Prop", [("zero", "Even 0"), ("succ", "(n : Nat) → Odd n → Even (n + 1)")]⟩,
              ⟨"Odd", "Nat → Prop", [("succ", "(n : Nat) → Even n → Odd (n + 1)")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 E1", task := "5.2.5" },
  { id := "mutual.tree-forest",
    types := [⟨"Tree", "Type", [("node", "Nat → Forest → Tree")]⟩,
              ⟨"Forest", "Type", [("nil", "Forest"), ("cons", "Tree → Forest → Forest")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1", task := "5.2.5" },
  { id := "mutual.single-ctor-props",
    types := [⟨"A", "Prop", [("a", "A")]⟩, ⟨"B", "Prop", [("b", "B")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 E1", task := "5.2.5" },
  { id := "mutual.universe-mismatch",
    types := [⟨"A", "Type", [("a", "B → A")]⟩, ⟨"B", "Prop", [("b", "B")]⟩],
    lean := "mutualUniverseMismatch", leanforth := "rejected", rule := "T4", task := "5.2.5" },
  { id := "mutual.parameter-mismatch", nparams := 1,
    types := [⟨"A", "Type → Type", []⟩, ⟨"B", "Prop → Type", []⟩],
    lean := "mutualParamMismatch", leanforth := "rejected", rule := "T3", task := "5.2.5" },
  { id := "mutual.parameter-count", nparams := 1,
    types := [⟨"A", "Type → Type", []⟩, ⟨"B", "Type", []⟩],
    lean := "paramCountMismatch", leanforth := "rejected", rule := "T3", task := "5.2.5" },
  -- Nested blocks.
  { id := "nested.tree", types := [⟨"Tree", "Type", [("node", "List Tree → Tree")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 N1", task := "5.2.5" },
  { id := "nested.non-positive",
    types := [⟨"Bad", "Type", [("mk", "List (Bad → Nat) → Bad")]⟩],
    lean := "nonPositive", leanforth := "rejected", rule := "N1 P1", task := "5.2.5" },
  { id := "nested.local-variable",
    types := [⟨"Bad", "Type", [("mk", "(α : Type) → List (Prod α Bad) → Bad")]⟩],
    lean := "nestedLocalVariable", leanforth := "rejected", rule := "N2", task := "5.2.5" },
  -- Names and the block itself.
  { id := "names.already-declared", ns := .anonymous,
    types := [⟨"Nat", "Type", [("zero", "Nat")]⟩],
    lean := "alreadyDeclared", leanforth := "rejected", rule := "T5", task := "5.2.1a" },
  { id := "names.duplicate-constructor",
    types := [⟨"T", "Type", [("a", "T"), ("a", "T")]⟩],
    lean := "duplicateConstructor", leanforth := "rejected", rule := "C4", task := "5.2.1a" },
  { id := "names.duplicate-universe", lparams := [`u, `u],
    types := [⟨"T", "Sort u", []⟩],
    lean := "duplicateLevelParam", leanforth := "rejected", rule := "T5", task := "5.2.1a" },
  -- A constructor named `rec`: the recursor's name is then taken (declare_recursors).
  { id := "names.constructor-named-rec", types := [⟨"R", "Type", [("rec", "R")]⟩],
    lean := "alreadyDeclared", leanforth := "rejected", rule := "N2", task := "5.2.1a" },
  { id := "names.empty-block", types := [],
    lean := "emptyBlock", leanforth := "rejected", rule := "T1", task := "5.2.1a" }
]

/-! ## Reductions -/

structure Red where
  id : String
  thm : Bool := true
  type : String
  value : String
  /-- Replace the body of the value `fun … x => x` by `x.i` of structure `S`. -/
  proj : Option (Name × Nat) := none
  lean : String
  leanforth : String
  rule : String
  task : String

/-- `fun … x => x.i`, the projection written as Lean's `Expr.proj`. -/
def projInnermost (s : Name) (i : Nat) : Expr → Expr
  | .lam x t b bi => match b with
    | .lam .. => .lam x t (projInnermost s i b) bi
    | _ => .lam x t (.proj s i (.bvar 0)) bi
  | e => e

def Red.decl (r : Red) (n : Name) : TermElabM Declaration := do
  let type ← elabWith [] [] r.type
  let value ← elabWith [] [] r.value
  let value := match r.proj with
    | some (s, i) => projInnermost s i value
    | none => value
  if r.thm then
    pure (.thmDecl { name := n, levelParams := [], type, value })
  else
    pure (.defnDecl { name := n, levelParams := [], type, value, hints := .regular 1,
                      safety := .safe })

def reductions : List Red := [
  { id := "iota.nat-literal-major",
    type := "@Nat.rec (fun _ => Nat) 7 (fun _ ih => Nat.succ ih) 3 = 10", value := "Eq.refl 10",
    lean := "accepted", leanforth := "accepted", rule := "R1 L2", task := "5.2.1b" },
  { id := "iota.nat-literal-major-wrong",
    type := "@Nat.rec (fun _ => Nat) 7 (fun _ ih => Nat.succ ih) 3 = 11", value := "Eq.refl 11",
    lean := "declTypeMismatch", leanforth := "rejected", rule := "R1 L2", task := "5.2.1b" },
  { id := "iota.stuck-on-variable",
    type := "∀ n : Nat, @Nat.rec (fun _ => Nat) 7 (fun _ ih => ih) n = 7",
    value := "fun (n : Nat) => Eq.refl 7",
    lean := "declTypeMismatch", leanforth := "rejected", rule := "R1", task := "5.2.1b" },
  { id := "iota.structure-eta",
    type := "∀ p : Nat × Nat, @Prod.rec Nat Nat (fun _ => Nat) (fun a _ => a) p = p.1",
    value := "fun (p : Nat × Nat) => Eq.refl p.1",
    lean := "accepted", leanforth := "accepted", rule := "R1 R3", task := "5.2.2" },
  { id := "iota.prop-structure-stuck",
    type := "∀ (a b : Prop) (h : a ∧ b), @And.rec a b (fun _ => Nat) (fun _ _ => 5) h = 5",
    value := "fun (a b : Prop) (h : a ∧ b) => Eq.refl 5",
    lean := "declTypeMismatch", leanforth := "rejected", rule := "R1 R3", task := "5.2.2" },
  { id := "k.eq-variable-proof",
    type := "∀ (a : Nat) (h : a = a), @Eq.rec Nat a (fun _ _ => Nat) 5 a h = 5",
    value := "fun (a : Nat) (h : a = a) => Eq.refl 5",
    lean := "accepted", leanforth := "accepted", rule := "R2", task := "5.2.1c" },
  { id := "k.eq-different-ends",
    type := "∀ (a b : Nat) (h : a = b), @Eq.rec Nat a (fun _ _ => Nat) 5 b h = 5",
    value := "fun (a b : Nat) (h : a = b) => Eq.refl 5",
    lean := "declTypeMismatch", leanforth := "rejected", rule := "R2", task := "5.2.1c" },
  { id := "eta.structure",
    type := "∀ p : Nat × Nat, p = (p.1, p.2)", value := "fun (p : Nat × Nat) => Eq.refl p",
    lean := "accepted", leanforth := "accepted", rule := "R4", task := "5.2.2" },
  { id := "unit.punit",
    type := "∀ x y : PUnit.{1}, x = y", value := "fun (x y : PUnit.{1}) => Eq.refl x",
    lean := "accepted", leanforth := "accepted", rule := "R5", task := "5.2.2" },
  { id := "unit.bool-not-unit-like",
    type := "∀ x y : Bool, x = y", value := "fun (x y : Bool) => Eq.refl x",
    lean := "declTypeMismatch", leanforth := "rejected", rule := "R5", task := "5.2.2" },
  -- Unit-like on two variables of a predicate's argument, without `Eq`: once PUnit is
  -- accepted (task 5.2.1a), rules D3/D5 must not call `P x` and `P y` apart.
  { id := "unit.punit-variables",
    type := "∀ (x y : PUnit.{1}) (P : PUnit.{1} → Prop), P x → P y",
    value := "fun (x y : PUnit.{1}) (P : PUnit.{1} → Prop) (h : P x) => h",
    lean := "accepted", leanforth := "accepted", rule := "R5", task := "5.2.2" },
  { id := "unit.bool-variables",
    type := "∀ (x y : Bool) (P : Bool → Prop), P x → P y",
    value := "fun (x y : Bool) (P : Bool → Prop) (h : P x) => h",
    lean := "declTypeMismatch", leanforth := "rejected", rule := "R5", task := "5.2.2" },
  { id := "unit.pair-of-units",
    type := "∀ x y : PUnit.{1} × PUnit.{1}, x = y",
    value := "fun (x y : PUnit.{1} × PUnit.{1}) => Eq.refl x",
    lean := "declTypeMismatch", leanforth := "rejected", rule := "R4 R5", task := "5.2.2" },
  { id := "proj.data", thm := false, type := "Nat × Nat → Nat",
    value := "fun (p : Nat × Nat) => p", proj := some (``Prod, 0),
    lean := "accepted", leanforth := "accepted", rule := "J1", task := "5.2.2" },
  { id := "proj.proof-of-proof", type := "∀ (a b : Prop), a ∧ b → a",
    value := "fun (a b : Prop) (h : a ∧ b) => h", proj := some (``And, 0),
    lean := "accepted", leanforth := "accepted", rule := "J1", task := "5.2.2" },
  { id := "proj.data-from-proof", thm := false, type := "(∃ n : Nat, n = n) → Nat",
    value := "fun (h : ∃ n : Nat, n = n) => h", proj := some (``Exists, 0),
    lean := "invalidProj", leanforth := "rejected", rule := "J2", task := "5.2.2" },
  { id := "proj.wrong-structure", thm := false, type := "Nat × Nat → Nat",
    value := "fun (p : Nat × Nat) => p", proj := some (``And, 0),
    lean := "invalidProj", leanforth := "rejected", rule := "J2", task := "5.2.2" },
  { id := "proj.index-out-of-range", thm := false, type := "Nat × Nat → Nat",
    value := "fun (p : Nat × Nat) => p", proj := some (``Prod, 2),
    lean := "invalidProj", leanforth := "rejected", rule := "J2", task := "5.2.2" },
  { id := "quot.lift-on-mk",
    type := "∀ (r : Nat → Nat → Prop) (f : Nat → Nat) (h : ∀ a b, r a b → f a = f b) (a : Nat), " ++
      "Quot.lift f h (Quot.mk r a) = f a",
    value := "fun (r : Nat → Nat → Prop) (f : Nat → Nat) (h : ∀ a b, r a b → f a = f b) " ++
      "(a : Nat) => Eq.refl (f a)",
    lean := "accepted", leanforth := "accepted", rule := "Q2", task := "5.2.4" },
  { id := "quot.lift-on-mk-wrong",
    type := "∀ (r : Nat → Nat → Prop) (f : Nat → Nat) (h : ∀ a b, r a b → f a = f b) " ++
      "(a b : Nat), Quot.lift f h (Quot.mk r a) = f b",
    value := "fun (r : Nat → Nat → Prop) (f : Nat → Nat) (h : ∀ a b, r a b → f a = f b) " ++
      "(a b : Nat) => Eq.refl (f b)",
    lean := "declTypeMismatch", leanforth := "rejected", rule := "Q2", task := "5.2.4" },
  { id := "quot.lift-stuck-on-variable",
    type := "∀ (r : Nat → Nat → Prop) (h : ∀ a b, r a b → (0 : Nat) = 0) (q : Quot r), " ++
      "Quot.lift (fun _ => (0 : Nat)) h q = 0",
    value := "fun (r : Nat → Nat → Prop) (h : ∀ a b, r a b → (0 : Nat) = 0) (q : Quot r) => " ++
      "Eq.refl (0 : Nat)",
    lean := "declTypeMismatch", leanforth := "rejected", rule := "Q2", task := "5.2.4" },
  { id := "lit.succ-of-literal", type := "Nat.succ 41 = 42", value := "Eq.refl 42",
    lean := "accepted", leanforth := "accepted", rule := "L1", task := "5.2.3" },
  { id := "lit.offset-with-variable", type := "∀ n : Nat, n + 1 = Nat.succ n",
    value := "fun (n : Nat) => Eq.refl (n + 1)",
    lean := "accepted", leanforth := "accepted", rule := "L3", task := "5.2.3" },
  { id := "lit.literal-against-constructors", type := "(5 : Nat) = Nat.succ (Nat.succ 3)",
    value := "Eq.refl 5",
    lean := "accepted", leanforth := "accepted", rule := "L3", task := "5.2.3" },
  { id := "lit.pow", type := "2 ^ 64 = 18446744073709551616", value := "Eq.refl 18446744073709551616",
    lean := "accepted", leanforth := "accepted", rule := "L1", task := "5.2.3" },
  { id := "lit.pow-wrong", type := "2 ^ 64 = 18446744073709551615",
    value := "Eq.refl 18446744073709551615",
    lean := "declTypeMismatch", leanforth := "rejected", rule := "L1", task := "5.2.3" },
  { id := "lit.mul", type := "123456789 * 987654321 = 121932631112635269",
    value := "Eq.refl 121932631112635269",
    lean := "accepted", leanforth := "accepted", rule := "L1", task := "5.2.3" },
  { id := "lit.sub-truncated", type := "(3 : Nat) - 5 = 0", value := "Eq.refl 0",
    lean := "accepted", leanforth := "accepted", rule := "L1", task := "5.2.3" },
  { id := "lit.div-by-zero", type := "(7 : Nat) / 0 = 0", value := "Eq.refl 0",
    lean := "accepted", leanforth := "accepted", rule := "L1", task := "5.2.3" },
  { id := "lit.gcd", type := "Nat.gcd 12 18 = 6", value := "Eq.refl 6",
    lean := "accepted", leanforth := "accepted", rule := "L1", task := "5.2.3" },
  { id := "lit.ble", type := "Nat.ble 3 5 = true", value := "Eq.refl true",
    lean := "accepted", leanforth := "accepted", rule := "L1", task := "5.2.3" },
  { id := "lit.string-expansion", type := "\"ab\" = String.ofList ['a', 'b']",
    value := "Eq.refl \"ab\"",
    lean := "accepted", leanforth := "accepted", rule := "L4", task := "5.2.3" },
  { id := "lit.string-expansion-wrong", type := "\"ab\" = String.ofList ['a', 'c']",
    value := "Eq.refl \"ab\"",
    lean := "declTypeMismatch", leanforth := "rejected", rule := "L4", task := "5.2.3" }
]

/-! ## Lean's replay of an exported block -/

def replayCode (msg : String) : String :=
  if has msg "Invalid recursor" then "invalidRecursor"
  else if has msg "Invalid constructor" then "invalidConstructor"
  else if has msg "No such recursor" then "noSuchRecursor"
  else match otherCodes.find? (fun (p, _) => has msg p) with
    | some (_, c) => "kernel " ++ c
    | none => "other: " ++ msg

def replayVerdict (base : Kernel.Environment) (cs : List ConstantInfo) : IO String := do
  let map := cs.foldl (fun (m : Std.HashMap Name ConstantInfo) c => m.insert c.name c) {}
  match ← (base.replay map).toBaseIO with
  | .ok _ => pure "accepted"
  | .error e => pure (replayCode (toString e))

structure Mutation where
  id : String
  change : ConstantInfo → Option ConstantInfo
  lean : String
  leanforth : String
  rule : String

def onRec (f : RecursorVal → RecursorVal) : ConstantInfo → Option ConstantInfo
  | .recInfo r => some (.recInfo (f r))
  | c => some c

def onCtor (n : Name) (f : ConstructorVal → ConstructorVal) : ConstantInfo → Option ConstantInfo
  | .ctorInfo c => some (if c.name == n then .ctorInfo (f c) else .ctorInfo c)
  | c => some c

def onType (f : InductiveVal → InductiveVal) : ConstantInfo → Option ConstantInfo
  | .inductInfo i => some (.inductInfo (f i))
  | c => some c

def swapRules (r : RecursorVal) : RecursorVal :=
  match r.rules with
  | [a, b] => { r with rules := [{ a with rhs := b.rhs }, { b with rhs := a.rhs }] }
  | _ => r

def nToN : Expr := .forallE `a (mkConst `IE.N) (mkConst `IE.N) .default
def nToNToN : Expr := .forallE `a (mkConst `IE.N) nToN .default

def mutations : List Mutation := [
  { id := "replay.original", change := some,
    lean := "accepted", leanforth := "accepted", rule := "A1 B3" },
  { id := "replay.rule-right-sides-swapped", change := onRec swapRules,
    lean := "invalidRecursor", leanforth := "rejected", rule := "B3" },
  { id := "replay.recursor-k-set", change := onRec fun r => { r with k := true },
    lean := "invalidRecursor", leanforth := "rejected", rule := "B3" },
  { id := "replay.recursor-motives-changed", change := onRec fun r => { r with numMotives := 2 },
    lean := "invalidRecursor", leanforth := "rejected", rule := "B3" },
  { id := "replay.constructor-fields-changed",
    change := onCtor `IE.N.succ fun c => { c with numFields := 2 },
    lean := "invalidConstructor", leanforth := "rejected", rule := "B3" },
  { id := "replay.constructor-type-changed",
    change := onCtor `IE.N.succ fun c => { c with type := nToNToN, numFields := 2 },
    lean := "invalidRecursor", leanforth := "rejected", rule := "B1 B3" },
  { id := "replay.parameters-changed", change := onType fun i => { i with numParams := 1 },
    lean := "kernel nonUniformOccurrence", leanforth := "rejected", rule := "B1 C1" },
  { id := "replay.isRec-changed", change := onType fun i => { i with isRec := false },
    lean := "accepted", leanforth := "accepted", rule := "B4" },
  { id := "replay.indices-changed", change := onType fun i => { i with numIndices := 1 },
    lean := "accepted", leanforth := "accepted", rule := "B4" },
  { id := "replay.recursor-left-out",
    change := fun c => match c with | .recInfo _ => none | c => some c,
    lean := "accepted", leanforth := "accepted", rule := "B4" }
]

/-- `{motive} → motive false → motive true → …` with its two minor premises swapped:
`{motive} → motive true → motive false → …` (the motive one binder further out in
the second). -/
def swapMinors : Expr → Expr
  | .forallE m mt (.forallE a (.app f x) (.forallE b (.app g y) rest bi2) bi1) bi0 =>
    .forallE m mt (.forallE b (.app f y) (.forallE a (.app g x) rest bi2) bi1) bi0
  | e => e

/-- The same checks on the non-recursive block `ind.bool` (`B`: `false`, `true`), which
plan task 5.2.1a covers, and more mutations: the recursor's universe parameter
dropped, renamed or doubled, the recursor renamed, its `all` doubled, its minor
premises swapped, a constructor's index or universe parameters changed (the last
five are review rvI21's probes). -/
def bTrue : Name := `IE.B.true
def boolMutations : List Mutation := [
  { id := "replay-bool.original", change := some,
    lean := "accepted", leanforth := "accepted", rule := "A1 B3" },
  { id := "replay-bool.rule-right-sides-swapped", change := onRec swapRules,
    lean := "invalidRecursor", leanforth := "rejected", rule := "B3" },
  { id := "replay-bool.recursor-k-set", change := onRec fun r => { r with k := true },
    lean := "invalidRecursor", leanforth := "rejected", rule := "B3" },
  { id := "replay-bool.recursor-motives-changed",
    change := onRec fun r => { r with numMotives := 2 },
    lean := "invalidRecursor", leanforth := "rejected", rule := "B3" },
  { id := "replay-bool.recursor-universe-dropped",
    change := onRec fun r => { r with levelParams := [] },
    lean := "invalidRecursor", leanforth := "rejected", rule := "B3" },
  { id := "replay-bool.recursor-renamed",
    change := onRec fun r => { r with name := `IE.B.recursor },
    lean := "noSuchRecursor", leanforth := "rejected", rule := "B3" },
  { id := "replay-bool.constructor-index-changed",
    change := onCtor bTrue fun c => { c with cidx := 0 },
    lean := "invalidConstructor", leanforth := "rejected", rule := "B3" },
  { id := "replay-bool.constructor-fields-changed",
    change := onCtor bTrue fun c => { c with numFields := 1 },
    lean := "invalidConstructor", leanforth := "rejected", rule := "B3" },
  { id := "replay-bool.constructor-type-changed",
    change := onCtor bTrue fun c =>
      { c with type := .forallE `p (.sort 0) (mkConst `IE.B) .default, numFields := 1 },
    lean := "invalidRecursor", leanforth := "rejected", rule := "B1 B3" },
  { id := "replay-bool.parameters-changed", change := onType fun i => { i with numParams := 1 },
    lean := "kernel nonUniformOccurrence", leanforth := "rejected", rule := "B1 C1" },
  { id := "replay-bool.isRec-changed", change := onType fun i => { i with isRec := true },
    lean := "accepted", leanforth := "accepted", rule := "B4" },
  { id := "replay-bool.indices-changed", change := onType fun i => { i with numIndices := 1 },
    lean := "accepted", leanforth := "accepted", rule := "B4" },
  { id := "replay-bool.recursor-left-out",
    change := fun c => match c with | .recInfo _ => none | c => some c,
    lean := "accepted", leanforth := "accepted", rule := "B4" },
  { id := "replay-bool.recursor-universe-renamed",
    change := onRec fun r =>
      { r with levelParams := [`v], type := r.type.instantiateLevelParams [`u] [.param `v] },
    lean := "invalidRecursor", leanforth := "rejected", rule := "B3" },
  { id := "replay-bool.recursor-universe-doubled",
    change := onRec fun r => { r with levelParams := [`u, `u] },
    lean := "invalidRecursor", leanforth := "rejected", rule := "B3" },
  { id := "replay-bool.recursor-all-doubled",
    change := onRec fun r => { r with all := [`IE.B, `IE.B] },
    lean := "invalidRecursor", leanforth := "rejected", rule := "B3" },
  { id := "replay-bool.minor-premises-swapped",
    change := onRec fun r => { r with type := swapMinors r.type },
    lean := "invalidRecursor", leanforth := "rejected", rule := "B3" },
  { id := "replay-bool.minor-premises-and-rules-swapped",
    change := onRec fun r => swapRules { r with type := swapMinors r.type },
    lean := "invalidRecursor", leanforth := "rejected", rule := "B3" },
  { id := "replay-bool.constructor-universe-added",
    change := onCtor bTrue fun c => { c with levelParams := [`u] },
    lean := "invalidConstructor", leanforth := "rejected", rule := "B3" }
]

/-- The motive's sort in a recursor's type made `Sort u`. -/
def sortInto (u : Level) : Expr → Expr
  | .forallE n t b bi => .forallE n t (sortInto u b) bi
  | .sort _ => .sort u
  | e => e

def motiveInto (u : Level) : Expr → Expr
  | .forallE n t b bi =>
    if n == `motive then .forallE n (sortInto u t) b bi else .forallE n t (motiveInto u b) bi
  | e => e

/-- Replays of three more accepted blocks of task 5.2.1a, each mutated once (review
rvI21's probes): `k` set where Lean's `init_K_target` clears it (`And` has a field,
`U` lives in `Type`), and `Or`'s recursor made to eliminate into every universe
(Lean's eliminates only into `Prop`, E1). -/
def blockReplays : List (String × List Mutation) := [
  ("ind.and", [
    { id := "replay-and.recursor-k-set", change := onRec fun r => { r with k := true },
      lean := "invalidRecursor", leanforth := "rejected", rule := "B3 K1" }]),
  ("ind.unit", [
    { id := "replay-unit.recursor-k-set", change := onRec fun r => { r with k := true },
      lean := "invalidRecursor", leanforth := "rejected", rule := "B3 K1" }]),
  ("ind.or", [
    { id := "replay-or.recursor-large-elimination",
      change := onRec fun r =>
        { r with levelParams := [`u], type := motiveInto (.param `u) r.type },
      lean := "invalidRecursor", leanforth := "rejected", rule := "B3 E1" }])
]

/-! ## Primitive names and quotient initialisation, in an empty environment -/

def v (n : Name) : Expr := .fvar ⟨n⟩
def foralls (bs : List (Name × Expr)) (body : Expr) : Expr :=
  bs.foldr (fun (n, t) b => .forallE n t (b.abstract #[v n]) .default) body
def funs (bs : List (Name × Expr)) (body : Expr) : Expr :=
  bs.foldr (fun (n, t) b => .lam n t (b.abstract #[v n]) .default) body
def lit (n : Nat) : Expr := .lit (.natVal n)
def nat : Expr := mkConst `Nat
def lu : Level := .param `u
def eqC (l : Level) (α a b : Expr) : Expr := mkAppN (mkConst `Eq [l]) #[α, a, b]
def reflC (l : Level) (α a : Expr) : Expr := mkAppN (mkConst `Eq.refl [l]) #[α, a]

def natDecl : Declaration :=
  let zero : Constructor := ⟨`Nat.zero, nat⟩
  let succ : Constructor := ⟨`Nat.succ, .forallE `n nat nat .default⟩
  .inductDecl [] 0 [⟨`Nat, .sort 1, [zero, succ]⟩] false

/-- `Eq` exactly as in Lean's prelude (up to binder names), or of type
`α → α → Type` when `wrong`. -/
def eqDecl (wrong : Bool := false) : Declaration :=
  let result : Expr := if wrong then .sort 1 else .sort 0
  let type := Expr.forallE `α (.sort lu)
    (.forallE `a (.bvar 0) (.forallE `b (.bvar 1) result .default) .default) .implicit
  let refl := Expr.forallE `α (.sort lu)
    (.forallE `a (.bvar 0) (mkAppN (mkConst `Eq [lu]) #[.bvar 1, .bvar 0, .bvar 0]) .default)
    .implicit
  .inductDecl [`u] 2 [⟨`Eq, type, [⟨`Eq.refl, refl⟩]⟩] false

/-- A `Nat.add` that ignores its second argument. -/
def forgedAdd : Declaration :=
  .defnDecl { name := `Nat.add, levelParams := [], type := .forallE `a nat (.forallE `b nat nat .default) .default,
              value := funs [(`a, nat), (`b, nat)] (v `a), hints := .regular 1, safety := .safe }

def add (a b : Expr) : Expr := mkAppN (mkConst `Nat.add) #[a, b]

/-- `Nat.add 2 3 = 5`, by computation on literals. -/
def five : Declaration :=
  .thmDecl { name := `five, levelParams := [], type := eqC 1 nat (add (lit 2) (lit 3)) (lit 5),
             value := reflC 1 nat (lit 5) }

/-- `∀ b, Nat.add 2 b = 2`, by unfolding `Nat.add`. -/
def twoAny : Declaration :=
  .thmDecl { name := `twoAny, levelParams := [],
             type := foralls [(`b, nat)] (eqC 1 nat (add (lit 2) (v `b)) (lit 2)),
             value := funs [(`b, nat)] (reflC 1 nat (lit 2)) }

/-- `5 = 2`, from the two by `Eq.rec`. -/
def fiveIsTwo : Declaration :=
  let motive := funs [(`x, nat), (`h, eqC 1 nat (add (lit 2) (lit 3)) (v `x))] (eqC 1 nat (v `x) (lit 2))
  .thmDecl { name := `fiveIsTwo, levelParams := [], type := eqC 1 nat (lit 5) (lit 2),
             value := mkAppN (mkConst `Eq.rec [0, 1])
               #[nat, add (lit 2) (lit 3), motive, .app (mkConst `twoAny) (lit 3), lit 5, mkConst `five] }

structure Chain where
  id : String
  decls : List Declaration
  lean : String
  leanforth : String
  rule : String
  task : String

def chains : List Chain := [
  { id := "primitive.forged-add-computes", decls := [natDecl, eqDecl, forgedAdd, five],
    lean := "accepted", leanforth := "unsupported", rule := "L5", task := "5.2.3" },
  { id := "primitive.forged-add-unfolds", decls := [natDecl, eqDecl, forgedAdd, five, twoAny],
    lean := "accepted", leanforth := "unsupported", rule := "L5", task := "5.2.3" },
  { id := "primitive.five-is-two", decls := [natDecl, eqDecl, forgedAdd, five, twoAny, fiveIsTwo],
    lean := "accepted", leanforth := "unsupported", rule := "L5", task := "5.2.3" },
  { id := "quotinit.with-eq", decls := [eqDecl, .quotDecl],
    lean := "accepted", leanforth := "accepted", rule := "Q1", task := "5.2.4" },
  { id := "quotinit.without-eq", decls := [.quotDecl],
    lean := "unknownConstant", leanforth := "rejected", rule := "Q1", task := "5.2.4" },
  { id := "quotinit.eq-wrong-shape", decls := [eqDecl (wrong := true), .quotDecl],
    lean := "quotEqShape", leanforth := "rejected", rule := "Q1", task := "5.2.4" }
]

/-- A constructor that names `_nested.T`, a name only the kernel's nested
elimination may use; the constant need not exist, since the name is checked
before any typing. Added to the `import Lean` environment. -/
def reservedPrefix : Declaration :=
  let t : Expr := mkConst `IE.T
  .inductDecl [] 0 [⟨`IE.T, .sort 1, [⟨`IE.T.mk, .forallE `x (mkConst `_nested.T) t .default⟩]⟩] false

/-- A definition named under `_nested`, then a block whose constructor uses it: T0
rejects the block, the constant being declared (a closed file; review rvI21 M1). -/
def nestedAux : Declaration :=
  .defnDecl { name := `_nested.X, levelParams := [], type := .sort 1, value := .sort 0,
              hints := .regular 0, safety := .safe }
def usesNestedAux : Declaration :=
  let t : Expr := mkConst `IE.T0
  .inductDecl [] 0 [⟨`IE.T0, .sort 1, [⟨`IE.T0.mk, .forallE `x (mkConst `_nested.X) t .default⟩]⟩] false

/-- A definition `IE.C.mk`, then a block `IE.C` whose constructor has that name (N2 on
the constructors, check_constructors; review rvI21 M1). -/
def takenName : Declaration :=
  .defnDecl { name := `IE.C.mk, levelParams := [], type := .sort 1, value := .sort 0,
              hints := .regular 0, safety := .safe }
def takenBlock : Declaration :=
  .inductDecl [] 0 [⟨`IE.C, .sort 1, [⟨`IE.C.mk, mkConst `IE.C⟩]⟩] false

def onBase : List Chain := [
  { id := "names.reserved-nested-prefix", decls := [reservedPrefix],
    lean := "reservedNestedPrefix", leanforth := "rejected", rule := "T0", task := "5.2.5" },
  { id := "names.reserved-nested-prefix-declared", decls := [nestedAux, usesNestedAux],
    lean := "reservedNestedPrefix", leanforth := "rejected", rule := "T0", task := "5.2.1a" },
  { id := "names.constructor-already-declared", decls := [takenName, takenBlock],
    lean := "alreadyDeclared", leanforth := "rejected", rule := "N2", task := "5.2.1a" }
]

/-! ## A declaration after a block

Each case adds declarations after a block, in order, each where the kernel
accepts it (as a file's declarations are checked one after another); the row's
verdict is the last one's. The block is `ind.bool` replayed from its constants with
or without its recursor (Lean's replay generates `IE.B.rec` either way), or a
declaration of `decls`. Review rvI21 B2 and M1. -/

structure Sequel where
  id : String
  /-- `some keep`: start from `ind.bool` replayed, with its recursor when `keep`. -/
  bool : Option Bool := none
  /-- A mutation of the Bool block's constants, before they are replayed. -/
  change : ConstantInfo → Option ConstantInfo := some
  decls : List Declaration
  lean : String
  leanforth : String
  rule : String
  task : String := "5.2.1a"

/-- `def IE.B.rec : Type := IE.B`. -/
def defBRec : Declaration :=
  .defnDecl { name := `IE.B.rec, levelParams := [], type := .sort 1, value := mkConst `IE.B,
              hints := .regular 1, safety := .safe }

/-- `def IE.B.useRec.{u} : <the type of IE.B.rec.{u}> := @IE.B.rec.{u}`. -/
def useBRec (recType : Expr) : Declaration :=
  .defnDecl { name := `IE.B.useRec, levelParams := [`u], type := recType,
              value := mkConst `IE.B.rec [.param `u], hints := .regular 1, safety := .safe }

/-- `Big : Type` with a field `Type` (rejected, U1), then `def IE.useBig : Type := IE.Big`. -/
def bigDecl : Declaration :=
  .inductDecl [] 0 [⟨`IE.Big, .sort 1, [⟨`IE.Big.mk, .forallE `a (.sort 1) (mkConst `IE.Big) .default⟩]⟩] false
def useBig : Declaration :=
  .defnDecl { name := `IE.useBig, levelParams := [], type := .sort 1, value := mkConst `IE.Big,
              hints := .regular 1, safety := .safe }

/-- `def n : Type := Prop`. -/
def defNamed (n : Name) : Declaration :=
  .defnDecl { name := n, levelParams := [], type := .sort 1, value := .sort 0,
              hints := .regular 1, safety := .safe }

/-- `def IE.useB : Type := IE.B`. -/
def useB : Declaration :=
  .defnDecl { name := `IE.useB, levelParams := [], type := .sort 1, value := mkConst `IE.B,
              hints := .regular 1, safety := .safe }

/-- The Bool block with its recursor renamed, and without its recursor but with
`true`'s index changed: replay's comparison (B3) refuses each, after its kernel added
the block (review rvI21 R2-1). -/
def renamedRec : ConstantInfo → Option ConstantInfo :=
  onRec fun r => { r with name := `IE.B.recursor }
def trueIndexZero : ConstantInfo → Option ConstantInfo :=
  onCtor `IE.B.true fun c => { c with cidx := 0 }

/-- Uses after a block: `IE.B.false`, `IE.B.rec` without its universe argument, and
the renamed recursor `IE.B.recursor`, which Lean's kernel never added. -/
def useFalse : Declaration :=
  .defnDecl { name := `IE.useFalse, levelParams := [], type := mkConst `IE.B,
              value := mkConst `IE.B.false, hints := .regular 1, safety := .safe }
def useRecNoLevel : Declaration :=
  .defnDecl { name := `IE.useRec0, levelParams := [], type := .sort 1,
              value := mkConst `IE.B.rec, hints := .regular 1, safety := .safe }
def useRenamed : Declaration :=
  .defnDecl { name := `IE.useRenamed, levelParams := [], type := .sort 1,
              value := mkConst `IE.B.recursor, hints := .regular 1, safety := .safe }

def sequels (recType : Expr) : List Sequel := [
  { id := "after.recursor-left-out-then-def-rec", bool := some false, decls := [defBRec],
    lean := "alreadyDeclared", leanforth := "rejected", rule := "B4 N2" },
  { id := "after.recursor-then-def-rec", bool := some true, decls := [defBRec],
    lean := "alreadyDeclared", leanforth := "rejected", rule := "N2" },
  { id := "after.recursor-left-out-then-use-rec", bool := some false, decls := [useBRec recType],
    lean := "accepted", leanforth := "accepted", rule := "B4" },
  { id := "after.recursor-left-out-then-use-and-def-rec", bool := some false,
    decls := [useBRec recType, defBRec],
    lean := "alreadyDeclared", leanforth := "rejected", rule := "B4 N2" },
  { id := "after.rejected-block-then-use", decls := [bigDecl, useBig],
    lean := "unknownConstant", leanforth := "rejected", rule := "U1 N1" },
  { id := "after.rejected-block-then-def-rec", decls := [bigDecl, defNamed `IE.Big.rec],
    lean := "accepted", leanforth := "accepted", rule := "U1 N2" },
  { id := "after.b3-renamed-then-def-rec", bool := some true, change := renamedRec,
    decls := [defBRec], lean := "alreadyDeclared", leanforth := "rejected", rule := "B3 N2" },
  { id := "after.b3-renamed-then-def-renamed", bool := some true, change := renamedRec,
    decls := [defNamed `IE.B.recursor],
    lean := "accepted", leanforth := "accepted", rule := "B3 N2" },
  { id := "after.b3-ctor-then-def-rec", bool := some false, change := trueIndexZero,
    decls := [defBRec], lean := "alreadyDeclared", leanforth := "rejected", rule := "B3 N2" },
  { id := "after.b3-ctor-then-def-type", bool := some false, change := trueIndexZero,
    decls := [defNamed `IE.B], lean := "alreadyDeclared", leanforth := "rejected",
    rule := "B3 N2" },
  { id := "after.b3-ctor-then-def-constructor", bool := some false, change := trueIndexZero,
    decls := [defNamed `IE.B.false], lean := "alreadyDeclared", leanforth := "rejected",
    rule := "B3 N2" },
  { id := "after.b3-ctor-then-use", bool := some false, change := trueIndexZero,
    decls := [useB], lean := "accepted", leanforth := "accepted", rule := "B3 N1" },
  { id := "after.b3-ctor-then-use-constructor", bool := some false, change := trueIndexZero,
    decls := [useFalse], lean := "accepted", leanforth := "accepted", rule := "B3 N1" },
  { id := "after.b3-ctor-then-use-rec", bool := some false, change := trueIndexZero,
    decls := [useBRec recType], lean := "accepted", leanforth := "accepted", rule := "B3 G1" },
  { id := "after.b3-renamed-then-use-rec", bool := some true, change := renamedRec,
    decls := [useBRec recType], lean := "accepted", leanforth := "accepted", rule := "B3 G1" },
  { id := "after.b3-renamed-then-use-renamed", bool := some true, change := renamedRec,
    decls := [useRenamed], lean := "unknownConstant", leanforth := "rejected",
    rule := "B3 N1" },
  { id := "after.recursor-left-out-then-use-rec-no-level", bool := some false,
    decls := [useRecNoLevel], lean := "universeArity", leanforth := "rejected",
    rule := "B4 L1" }
]

/-- What replay's `addDecl` adds for a block: the declaration rebuilt from the
exported type and constructor types (`Lean/Replay.lean`, the inductive case). -/
def rebuilt (cs : List ConstantInfo) : Option Declaration := do
  let some (.inductInfo i) := cs.find? (fun c => c matches .inductInfo _) | none
  let ctors := i.ctors.filterMap fun n => match cs.find? (·.name == n) with
    | some (.ctorInfo c) => some ({ name := c.name, type := c.type } : Constructor)
    | _ => none
  some (.inductDecl i.levelParams i.numParams [⟨i.name, i.type, ctors⟩] false)

/-- The last declaration's verdict, the others added where the kernel accepts them. -/
def lastVerdict (env : Kernel.Environment) : List Declaration → String
  | [] => "no declaration"
  | [d] => verdict (env.addDeclCore 0 0 d none)
  | d :: ds => lastVerdict (match env.addDeclCore 0 0 d none with
      | .ok e => e
      | .error _ => env) ds

/-- The environment a sequel's declarations are added to: `base`, or `base` after
replay of the (mutated) Bool block. When replay's comparison refuses the block, its
kernel has already added the block rebuilt from the file (`addDecl` comes first, the
comparison last), so that is the environment Lean's later declarations meet. -/
def sequelStart (base : Kernel.Environment) (bcs : List ConstantInfo) (s : Sequel) :
    IO Kernel.Environment := do
  match s.bool with
  | none => pure base
  | some keep =>
    let cs := (if keep then bcs else bcs.filter fun c => !(c matches .recInfo _)).filterMap s.change
    let map := cs.foldl (fun (m : Std.HashMap Name ConstantInfo) c => m.insert c.name c) {}
    match ← (base.replay map).toBaseIO with
    | .ok env => pure env
    | .error e =>
      let code := replayCode (toString e)
      unless ["invalidConstructor", "invalidRecursor", "noSuchRecursor"].contains code do
        throw (IO.userError s!"{s.id}: the Bool block not replayed: {e}")
      let some d := rebuilt cs | throw (IO.userError s!"{s.id}: no block to rebuild")
      match base.addDeclCore 0 0 d none with
      | .ok env => pure env
      | .error _ => throw (IO.userError s!"{s.id}: the rebuilt block refused")

/-- A block declared twice in one input: `names.already-declared` without `Nat` (a
recursive type, task 5.2.1b), so that task 5.2.1a reaches rule T5. -/
def twice : Block :=
  { id := "names.already-declared-earlier",
    types := [⟨"Twice", "Prop", [("mk", "Twice")]⟩],
    lean := "alreadyDeclared", leanforth := "rejected", rule := "T5", task := "5.2.1a" }

/-- Add `ds` in order; the verdict is that of the first failure, or of the last. -/
def addAll (env : Kernel.Environment) : List Declaration → Except Kernel.Exception Kernel.Environment
  | [] => .ok env
  | d :: ds => match env.addDeclCore 0 0 d none with
    | .ok env' => addAll env' ds
    | .error e => .error e

/-! ## Every case as a lean4export file, for LeanForth's differential

After the rows, each case is printed as the NDJSON file the toolchain's exporter
(`LeanExport`) writes for it, between a line `ndjson-begin <id> <names>` (the case's own
constants, comma-separated) and a line `ndjson-end`: the case's dependencies from the
environment it was checked in, then the case's own constants. A declaration Lean's kernel
accepted is written from the environment the kernel made (with the recursors it
generated); one it refused, from its constants added without any check, as a file that
holds it would (no recursor; the fields Lean's replay ignores set plainly). The verdicts
above never come from these files; `inductive-check.sh` compares only the rows, and
`tests/core/inductive-table.py` runs LeanForth on the files (plan task 5.2.1a). -/

/-- Lean's own `Kernel.Environment.add` (private to `Lean.Environment`): a constant added
without any check, used only to write a refused case as a file. -/
def kernelAddName : Name := Name.mkNum `_private.Lean.Environment 0 ++ `Lean.Kernel.Environment.add

unsafe def kernelAddImpl (env : Environment) :
    Except String (Kernel.Environment → ConstantInfo → Kernel.Environment) :=
  env.evalConst _ {} kernelAddName

@[implemented_by kernelAddImpl]
opaque kernelAddFn (env : Environment) :
    Except String (Kernel.Environment → ConstantInfo → Kernel.Environment)

def piCount : Expr → Nat
  | .forallE _ _ b _ => piCount b + 1
  | _ => 0

def ctorConstants (lps : List Name) (np : Nat) (t : InductiveType) : List ConstantInfo :=
  t.ctors.zipIdx.map fun (c, i) => .ctorInfo {
    name := c.name
    levelParams := lps
    type := c.type
    induct := t.name
    cidx := i
    numParams := np
    numFields := piCount c.type - np
    isUnsafe := false }

/-- The constants a file holds for a declaration Lean's kernel refused. -/
def asConstants : Declaration → List ConstantInfo
  | .inductDecl lps np types _ =>
    types.flatMap fun t =>
      let ty : ConstantInfo := .inductInfo {
        name := t.name
        levelParams := lps
        type := t.type
        numParams := np
        numIndices := piCount t.type - np
        all := types.map (·.name)
        ctors := t.ctors.map (·.name)
        numNested := 0
        isRec := false
        isUnsafe := false
        isReflexive := false }
      ty :: ctorConstants lps np t
  | .thmDecl v => [.thmInfo v]
  | .defnDecl v => [.defnInfo v]
  | _ => []

def typeNames : Declaration → List Name
  | .inductDecl _ _ types _ => types.map (·.name)
  | .quotDecl => [`Quot]
  | d => d.getNames

/-- A block's own constants in an environment that holds it: its types, their
constructors, and the recursors Lean generated (`T.rec`, `T.rec_1`, …). -/
def blockNames (env : Kernel.Environment) (types : List Name) : List Name := Id.run do
  let mut out := types
  for t in types do
    if let some (.inductInfo i) := env.find? t then out := out ++ i.ctors
  for t in types do
    let mut k := 0
    let mut r := t ++ `rec
    while (env.find? r).isSome do
      out := out ++ [r]
      k := k + 1
      r := t ++ Name.mkSimple s!"rec_{k}"
  return out

def quotNames : List Name := [`Quot, `Quot.mk, `Quot.lift, `Quot.ind]

/-- The own constants of a declaration in the environment that holds it. -/
def ownNames (env : Kernel.Environment) : Declaration → List Name
  | d@(.inductDecl ..) => blockNames env (typeNames d)
  | .quotDecl => quotNames
  | d => d.getNames

/-- The recursor names `LeanExport` writes with each root (its `recursorMap`). -/
def recsOf (env : Kernel.Environment) (own : List Name) : NameSet :=
  NameSet.ofList <| own.filter fun n => match env.find? n with
    | some (.recInfo _) => true
    | _ => false

def emptyBlockLine : String := "{\"inductive\":{\"ctors\":[],\"recs\":[],\"types\":[]}}"

/-- Part of a case: its own constants in the environment that holds them, and the
names `LeanExport` dumps them from. -/
structure Segment where
  env : Kernel.Environment
  own : List Name
  roots : List Name

/-- Print one case as an export between marker lines: the meta record, what the
segments use from `base`, then each segment from its own environment. The marker
names the case's own constants, or only `judged` when given (a sequel's last
declaration). -/
def writeSegments (base : Kernel.Environment) (baseRecs : NameMap NameSet) (id : String)
    (segs : List Segment) (judged : Option (List Name) := none) : IO Unit := do
  let own := segs.flatMap (·.own)
  let named := judged.getD own
  IO.println s!"ndjson-begin\t{id}\t{",".intercalate (named.map (·.toString false))}"
  LeanExport.M.run (Environment.ofKernelEnv base) do
    modify fun st => { st with recursorMap := baseRecs, ignoreMissing := true }
    LeanExport.dumpMetadata
    if own.isEmpty then IO.println emptyBlockLine
    for s in segs do
      for n in s.own do
        if let some c := s.env.find? n then
          for d in c.getUsedConstantsAsSet do
            if (base.find? d).isSome then LeanExport.dumpConstant d
    for s in segs do
      let recs := recsOf s.env s.own
      modify fun st => { st with
        visitedConstants := s.own.foldl (fun v n => v.erase n) st.visitedConstants
        recursorMap := s.roots.foldl (fun m r => m.insert r recs) st.recursorMap }
      withReader (fun _ => { env := Environment.ofKernelEnv s.env }) do
        for r in s.roots do LeanExport.dumpConstant r
  IO.println "ndjson-end"

def writeCase (base : Kernel.Environment) (baseRecs : NameMap NameSet) (id : String)
    (caseEnv : Kernel.Environment) (own roots : List Name) : IO Unit :=
  writeSegments base baseRecs id [⟨caseEnv, own, roots⟩]

/-- The recursor map of an environment, as `LeanExport.initState` makes it. -/
def recursorsOf (env : Kernel.Environment) : IO (NameMap NameSet) :=
  LeanExport.M.run (Environment.ofKernelEnv env) do
    LeanExport.initState (Environment.ofKernelEnv env)
    return (← get).recursorMap

abbrev KernelAdd := Kernel.Environment → ConstantInfo → Kernel.Environment

/-- A declaration added to `env`: by the kernel when it accepts it, else as a file
holds it (for a quotient, the four constants of `lean`, the environment `quot`). -/
def addOrHold (add : KernelAdd) (quot : Kernel.Environment) (env : Kernel.Environment)
    (d : Declaration) : Kernel.Environment :=
  match env.addDeclCore 0 0 d none, d with
  | .ok e, _ => e
  | .error _, .quotDecl => quotNames.foldl (fun e n => match quot.find? n with
      | some c => add e c
      | none => e) env
  | .error _, _ => (asConstants d).foldl add env

/-- The own constants of `d` added to `env`, giving `e`: what the kernel made, or the
constants held for a declaration it refused. -/
def ownOf (env e : Kernel.Environment) (d : Declaration) : List Name :=
  match env.addDeclCore 0 0 d none, d with
  | .ok _, _ => ownNames e d
  | .error _, .quotDecl => quotNames
  | .error _, _ => (asConstants d).map (·.name)

/-- Declarations added in order, each written from the environment just after it. -/
def chainSegments (add : KernelAdd) (quot env : Kernel.Environment) :
    List Declaration → List Segment
  | [] => []
  | d :: ds =>
    let e := addOrHold add quot env d
    ⟨e, ownOf env e d, (typeNames d).take 1⟩ :: chainSegments add quot e ds

/-- A sequel as a file holds it: the Bool block's constants (without its recursor
when left out), then each declaration as `chainSegments` writes it; the marker names
the last declaration's constants. -/
def writeSequel (add : KernelAdd) (base : Kernel.Environment) (baseRecs : NameMap NameSet)
    (bcs : List ConstantInfo) (s : Sequel) : IO Unit :=
  let (start, head) : Kernel.Environment × List Segment := match s.bool with
    | none => (base, [])
    | some keep =>
      let cs := (if keep then bcs else bcs.filter fun c => !(c matches .recInfo _)).filterMap
        s.change
      let e := cs.foldl add base
      (e, [⟨e, cs.map (·.name), [`IE.B]⟩])
  let segs := head ++ chainSegments add base start s.decls
  writeSegments base baseRecs s.id segs (some ((segs.getLast?.map (·.own)).getD []))

/-- A block of `accepted` or `checks` that the kernel accepts, as a declaration. -/
def blockDecl (id : String) : CommandElabM Declaration := do
  let some b := (accepted ++ checks).find? (·.id == id) | throwError "no {id}"
  liftTermElabM b.decl

/-- A declaration's own constants in `base` after the kernel adds it. -/
def ownConstants (base : Kernel.Environment) (d : Declaration) :
    CommandElabM (List ConstantInfo) := do
  let .ok env := base.addDeclCore 0 0 d none | throwError "block not accepted"
  (ownNames env d).mapM fun n => match env.find? n with
    | some c => pure c
    | none => throwError "missing {n}"

/-- An accepted block of `accepted`, added to `base`, and its own constants. -/
def blockConstants (base : Kernel.Environment) (id : String) :
    CommandElabM (List ConstantInfo) := do
  ownConstants base (← blockDecl id)

/-! ### A block without its recursors, then a use of the generated one

Review rvI21 round 4 (R4-1, R4-2): the recursor a block generates is the one
a later declaration meets when the file leaves the recursors out. Each case
replays a block without its recursors (Lean's replay generates them) and adds
declarations after it: by default `def T.useRec.{us} : <the type of T.rec> :=
@T.rec.{us}`, `T` the block's first type; the row's verdict is the last
declaration's. The block is one of the table's, or written here. -/

structure Stripped where
  id : String
  block : CommandElabM Declaration
  /-- The declarations after the block, from Lean's recursor of its first type. -/
  uses : RecursorVal → List Declaration
  lean : String
  leanforth : String
  rule : String
  task : String := "5.2.1a"

/-- `def T.useRec.{us} : <type of T.rec> := @T.rec.{us}`. -/
def useRecOf (r : RecursorVal) : Declaration :=
  .defnDecl { name := r.name.getPrefix ++ `useRec, levelParams := r.levelParams, type := r.type,
              value := mkConst r.name (r.levelParams.map .param), hints := .regular 1,
              safety := .safe }

/-- `def T.useRec<suffix>.{names} : <type of T.rec at levels> := @T.rec.{levels}`, with
the value eta-expanded over the type's first `eta` binders (`fun α p => @T.rec.{…} α p`):
the generated recursor at universes other than its own names (review rvI21 R5-1). -/
def etaOf (f : Expr) : Nat → Expr → Nat → Expr
  | k+1, .forallE n t b bi, depth => .lam n t (etaOf f k b (depth + 1)) bi
  | _, _, depth => mkAppN f ((List.range depth).reverse.map Expr.bvar).toArray

def useRecAt (suffix : String) (names : List Name) (levels : List Level) (eta : Nat := 0)
    (r : RecursorVal) : Declaration :=
  let ty := r.type.instantiateLevelParams r.levelParams levels
  .defnDecl { name := r.name.getPrefix ++ Name.mkSimple ("useRec" ++ suffix),
              levelParams := names, type := ty, value := etaOf (mkConst r.name levels) eta ty 0,
              hints := .regular 1, safety := .safe }

def lp (n : Name) : Level := .param n
def lv (k : Nat) : Level := Level.ofNat k

/-- `Q := ∀ p : Prop, p` and `@IE.B.rec.{1} (fun _ : IE.B => Prop) Q Q IE.B.true`, a
proposition: the motive's universe `u` named by no level of the file (R4-1). -/
def qProp : Expr := .forallE `p (.sort 0) (.bvar 0) .default
def recAtOne : Expr :=
  mkAppN (mkConst `IE.B.rec [1])
    #[.lam `x (mkConst `IE.B) (.sort 0) .default, qProp, qProp, mkConst `IE.B.true]
/-- `def IE.d : Prop := (fun x : Prop => x) recAtOne`. -/
def lookupInDef : Declaration :=
  .defnDecl { name := `IE.d, levelParams := [], type := .sort 0,
              value := .app (.lam `x (.sort 0) (.bvar 0) .default) recAtOne,
              hints := .regular 1, safety := .safe }
/-- A block `IE.C : Prop` whose constructor's field is that proposition, as
`(fun x : Prop => x) recAtOne`: the recursor is built again during another block's
check. -/
def lookupDuringBlock : Declaration :=
  let field : Expr := .app (.lam `x (.sort 0) (.bvar 0) .default) recAtOne
  .inductDecl [] 0 [⟨`IE.C, .sort 0, [⟨`IE.C.mk, .forallE `h field (mkConst `IE.C) .default⟩]⟩]
    false
/-- `IE.U2 : (fun x : Type 1 => x) Type`, a type that is a Sort only after whnf, with
one constructor; then `def IE.U2.bad : Prop := @IE.U2.rec.{1}`, which Lean rejects. -/
def redexBlock : Declaration :=
  .inductDecl [] 0 [⟨`IE.U2, .app (.lam `x (.sort 2) (.bvar 0) .default) (.sort 1),
    [⟨`IE.U2.unit, mkConst `IE.U2⟩]⟩] false
def redexUse : Declaration :=
  .defnDecl { name := `IE.U2.bad, levelParams := [], type := .sort 0,
              value := mkConst `IE.U2.rec [1], hints := .regular 1, safety := .safe }

/-- `@IE.L.rec.{1, 1} Type (fun _ => Prop) Q (fun _ _ _ => Q) (@IE.L.nil.{1} Type)`, a
proposition, and a block `IE.W (α : Type) : Prop` whose constructor's field is that
proposition behind a β-redex: the recursor of the list `IE.L` is built again while W's
constructors are checked, after W's parameter domains were recorded (plan task 5.2.1b). -/
def lType : Expr := mkApp (mkConst `IE.L [1]) (.sort 1)
def recListAtOne : Expr :=
  let motive : Expr := .lam `x lType (.sort 0) .default
  let consCase : Expr :=
    .lam `h (.sort 1) (.lam `t lType (.lam `ih (.sort 0) qProp .default) .default) .default
  mkAppN (mkConst `IE.L.rec [1, 1])
    #[.sort 1, motive, qProp, consCase, mkApp (mkConst `IE.L.nil [1]) (.sort 1)]
def lookupDuringParamBlock : Declaration :=
  let field : Expr := .app (.lam `x (.sort 0) (.bvar 0) .default) recListAtOne
  .inductDecl [] 1 [⟨`IE.W, .forallE `α (.sort 1) (.sort 0) .default,
    [⟨`IE.W.mk, .forallE `α (.sort 1)
      (.forallE `h field (mkApp (mkConst `IE.W) (.bvar 1)) .default) .default⟩]⟩] false

/-- `IE.U70.{u_1 … u_70} : Type` with one constructor: a recursor of 71 universe
parameters (review rvI21 R4-3: no fixed limit). -/
def manyNames : List Name := (List.range 70).map fun i => Name.mkSimple s!"u_{i + 1}"
def manyBlock : Declaration :=
  .inductDecl manyNames 0 [⟨`IE.U70, .sort 1,
    [⟨`IE.U70.unit, mkConst `IE.U70 (manyNames.map .param)⟩]⟩] false

def stripped : List Stripped := [
  { id := "after.and-left-out-then-use-rec", block := blockDecl "ind.and",
    uses := fun r => [useRecOf r], lean := "accepted", leanforth := "accepted", rule := "B4 G1" },
  { id := "after.or-left-out-then-use-rec", block := blockDecl "ind.or",
    uses := fun r => [useRecOf r], lean := "accepted", leanforth := "accepted",
    rule := "B4 G1 E1" },
  { id := "after.exists-left-out-then-use-rec", block := blockDecl "ind.exists",
    uses := fun r => [useRecOf r], lean := "accepted", leanforth := "accepted",
    rule := "B4 G1 E4" },
  { id := "after.true-left-out-then-use-rec", block := blockDecl "ind.true",
    uses := fun r => [useRecOf r], lean := "accepted", leanforth := "accepted",
    rule := "B4 G1 K1" },
  { id := "after.empty-prop-left-out-then-use-rec", block := blockDecl "ind.empty-prop",
    uses := fun r => [useRecOf r], lean := "accepted", leanforth := "accepted",
    rule := "B4 G1 E2" },
  { id := "after.unit-left-out-then-use-rec", block := blockDecl "ind.unit",
    uses := fun r => [useRecOf r], lean := "accepted", leanforth := "accepted", rule := "B4 G1" },
  { id := "after.universe-max-left-out-then-use-rec", block := blockDecl "ind.universe-max",
    uses := fun r => [useRecOf r], lean := "accepted", leanforth := "accepted",
    rule := "B4 G1 U1" },
  { id := "after.predicate-any-field-left-out-then-use-rec",
    block := blockDecl "universe.predicate-any-field",
    uses := fun r => [useRecOf r], lean := "accepted", leanforth := "accepted",
    rule := "B4 G1 E4" },
  { id := "after.eq-left-out-then-use-rec", block := blockDecl "ind.eq",
    uses := fun r => [useRecOf r], lean := "accepted", leanforth := "accepted",
    rule := "B4 G1 K1", task := "5.2.1c" },
  { id := "after.index-left-out-then-use-rec", block := blockDecl "params.index-one-universe-up",
    uses := fun r => [useRecOf r], lean := "accepted", leanforth := "accepted",
    rule := "B4 G1", task := "5.2.1c" },
  { id := "after.mutual-left-out-then-use-rec", block := blockDecl "mutual.single-ctor-props",
    uses := fun r => [useRecOf r], lean := "accepted", leanforth := "accepted",
    rule := "B4 G1", task := "5.2.5" },
  { id := "after.recursor-left-out-then-lookup-in-def", block := blockDecl "ind.bool",
    uses := fun _ => [lookupInDef], lean := "accepted", leanforth := "accepted",
    rule := "B4 G1" },
  { id := "after.recursor-left-out-then-lookup-during-block", block := blockDecl "ind.bool",
    uses := fun _ => [lookupDuringBlock], lean := "accepted", leanforth := "accepted",
    rule := "B4 G1" },
  { id := "after.many-universes-left-out-then-use-rec", block := pure manyBlock,
    uses := fun r => [useRecOf r], lean := "accepted", leanforth := "accepted",
    rule := "B4 G1" },
  { id := "after.eq-at-renamed", block := blockDecl "ind.eq",
    uses := fun r => [useRecAt "Renamed" [`a, `b] [lp `a, lp `b] 0 r],
    lean := "accepted", leanforth := "accepted", rule := "B4 G1", task := "5.2.1c" },
  { id := "after.eq-at-concrete", block := blockDecl "ind.eq",
    uses := fun r => [useRecAt "Concrete" [] [lv 0, lv 1] 0 r],
    lean := "accepted", leanforth := "accepted", rule := "B4 G1", task := "5.2.1c" },
  { id := "after.eq-at-applied", block := blockDecl "ind.eq",
    uses := fun r => [useRecAt "Applied" [`a, `b] [lp `a, lp `b] 2 r],
    lean := "accepted", leanforth := "accepted", rule := "B4 G1", task := "5.2.1c" },
  { id := "after.exists-at-renamed", block := blockDecl "ind.exists",
    uses := fun r => [useRecAt "Renamed" [`b] [lp `b] 0 r],
    lean := "accepted", leanforth := "accepted", rule := "B4 G1" },
  { id := "after.exists-at-concrete", block := blockDecl "ind.exists",
    uses := fun r => [useRecAt "Concrete" [] [lv 1] 0 r],
    lean := "accepted", leanforth := "accepted", rule := "B4 G1" },
  { id := "after.exists-at-applied", block := blockDecl "ind.exists",
    uses := fun r => [useRecAt "Applied" [`b] [lp `b] 2 r],
    lean := "accepted", leanforth := "accepted", rule := "B4 G1" },
  { id := "after.universe-max-at-renamed", block := blockDecl "ind.universe-max",
    uses := fun r => [useRecAt "Renamed" [`a, `b, `c] [lp `a, lp `b, lp `c] 0 r],
    lean := "accepted", leanforth := "accepted", rule := "B4 G1" },
  { id := "after.universe-max-at-concrete", block := blockDecl "ind.universe-max",
    uses := fun r => [useRecAt "Concrete" [] [lv 0, lv 1, lv 2] 0 r],
    lean := "accepted", leanforth := "accepted", rule := "B4 G1" },
  { id := "after.universe-max-at-swapped", block := blockDecl "ind.universe-max",
    uses := fun r => [useRecAt "Swapped" [`u_1, `u, `v] [lp `u_1, lp `v, lp `u] 0 r],
    lean := "accepted", leanforth := "accepted", rule := "B4 G1" },
  { id := "after.universe-max-at-applied", block := blockDecl "ind.universe-max",
    uses := fun r => [useRecAt "Applied" [`a, `b, `c] [lp `a, lp `b, lp `c] 2 r],
    lean := "accepted", leanforth := "accepted", rule := "B4 G1" },
  { id := "after.redex-type-left-out-then-use-rec", block := pure redexBlock,
    uses := fun _ => [redexUse], lean := "declTypeMismatch", leanforth := "rejected",
    rule := "B4 G1" },
  -- Recursive blocks (plan task 5.2.1b): the generated recursor, with its induction
  -- hypotheses, at its own universes and at others.
  { id := "after.nat-left-out-then-use-rec", block := blockDecl "ind.nat",
    uses := fun r => [useRecOf r], lean := "accepted", leanforth := "accepted",
    rule := "B4 G1", task := "5.2.1b" },
  { id := "after.list-left-out-then-use-rec", block := blockDecl "ind.list",
    uses := fun r => [useRecOf r], lean := "accepted", leanforth := "accepted",
    rule := "B4 G1", task := "5.2.1b" },
  { id := "after.reflexive-left-out-then-use-rec", block := blockDecl "ind.reflexive",
    uses := fun r => [useRecOf r], lean := "accepted", leanforth := "accepted",
    rule := "B4 G1", task := "5.2.1b" },
  { id := "after.binary-tree-left-out-then-use-rec", block := blockDecl "ind.binary-tree",
    uses := fun r => [useRecOf r], lean := "accepted", leanforth := "accepted",
    rule := "B4 G1", task := "5.2.1b" },
  { id := "after.list-at-renamed", block := blockDecl "ind.list",
    uses := fun r => [useRecAt "Renamed" [`a, `b] [lp `a, lp `b] 0 r],
    lean := "accepted", leanforth := "accepted", rule := "B4 G1", task := "5.2.1b" },
  { id := "after.list-at-concrete", block := blockDecl "ind.list",
    uses := fun r => [useRecAt "Concrete" [] [lv 0, lv 1] 0 r],
    lean := "accepted", leanforth := "accepted", rule := "B4 G1", task := "5.2.1b" },
  { id := "after.list-at-applied", block := blockDecl "ind.list",
    uses := fun r => [useRecAt "Applied" [`a, `b] [lp `a, lp `b] 2 r],
    lean := "accepted", leanforth := "accepted", rule := "B4 G1", task := "5.2.1b" },
  { id := "after.list-sort-max-at-concrete", block := blockDecl "ind.list-sort-max",
    uses := fun r => [useRecAt "Concrete" [] [lv 2, lv 0] 0 r],
    lean := "accepted", leanforth := "accepted", rule := "B4 G1 U1", task := "5.2.1b" },
  { id := "after.reflexive-parameter-at-renamed", block := blockDecl "ind.reflexive-parameter",
    uses := fun r => [useRecAt "Renamed" [`w] [lp `w] 0 r],
    lean := "accepted", leanforth := "accepted", rule := "B4 G1", task := "5.2.1b" },
  { id := "after.list-left-out-then-lookup-during-param-block", block := blockDecl "ind.list",
    uses := fun _ => [lookupDuringParamBlock], lean := "accepted", leanforth := "accepted",
    rule := "B4 G1 C2", task := "5.2.1b" }
]

/-- A stripped case's block constants without recursors, the environment Lean's
replay of them makes, and Lean's recursor of the block's first type. -/
def strippedStart (base : Kernel.Environment) (s : Stripped) :
    CommandElabM (List ConstantInfo × Kernel.Environment × RecursorVal) := do
  let d ← s.block
  let cs ← ownConstants base d
  let kept := cs.filter fun c => !(c matches .recInfo _)
  let some (.inductInfo t) := cs.find? (fun c => c matches .inductInfo _) | throwError "no type"
  let some (.recInfo r) := cs.find? (·.name == t.name ++ `rec) | throwError "no recursor"
  let map := kept.foldl (fun (m : Std.HashMap Name ConstantInfo) c => m.insert c.name c) {}
  match ← (base.replay map).toBaseIO with
  | .ok env => pure (kept, env, r)
  | .error e => throwError "{s.id}: not replayed: {e}"

/-- A stripped case as a file holds it: the block's constants without recursors,
then each declaration as `chainSegments` writes it; the marker names the last. -/
def writeStripped (add : KernelAdd) (base : Kernel.Environment) (baseRecs : NameMap NameSet)
    (kept : List ConstantInfo) (r : RecursorVal) (s : Stripped) : IO Unit :=
  let e := kept.foldl add base
  let root := (kept.head?.map (·.name)).getD .anonymous
  let segs := [(⟨e, kept.map (·.name), [root]⟩ : Segment)] ++ chainSegments add base e (s.uses r)
  writeSegments base baseRecs s.id segs (some ((segs.getLast?.map (·.own)).getD []))

/-- A replayed set of constants as a file holds it. -/
def writeMutation (add : KernelAdd) (base : Kernel.Environment) (baseRecs : NameMap NameSet)
    (root : Name) (cs : List ConstantInfo) (m : Mutation) : IO Unit :=
  let cs' := cs.filterMap m.change
  writeCase base baseRecs m.id (cs'.foldl add base) (cs'.map (·.name)) [root]

end InductiveExpected

open InductiveExpected in
run_cmd do
  let env ← getEnv
  let base := env.toKernelEnv
  IO.println "id\tlean\tleanforth\trule\ttask\tfacts"
  let row (id got lf rule task facts : String) : CommandElabM Unit :=
    IO.println s!"{id}\t{got}\t{lf}\t{rule}\t{task}\t{facts}"
  -- 1. Inductive declarations.
  for b in accepted ++ checks do
    let d ← liftTermElabM b.decl
    let r := base.addDeclCore 0 0 d none
    let got := verdict r
    unless got == b.lean do throwError "{b.id}: Lean's verdict is {got}, expected {b.lean}"
    let fs := match r with | .ok e => facts e b | .error _ => ""
    row b.id got b.leanforth b.rule b.task fs
  -- 2. Reductions.
  for r in reductions do
    let d ← liftTermElabM (r.decl (`IE ++ r.id.toName))
    let got := verdict (base.addDeclCore 0 0 d none)
    unless got == r.lean do throwError "{r.id}: Lean's verdict is {got}, expected {r.lean}"
    row r.id got r.leanforth r.rule r.task ""
  -- 3. Replay of the `ind.nat` block, unchanged and mutated.
  let some natBlock := accepted.find? (·.id == "ind.nat") | throwError "no ind.nat"
  let d ← liftTermElabM natBlock.decl
  let .ok withN := base.addDeclCore 0 0 d none | throwError "ind.nat not accepted"
  let names := [`IE.N, `IE.N.zero, `IE.N.succ, `IE.N.rec]
  let cs ← names.mapM fun n => match withN.find? n with
    | some c => pure c
    | none => throwError "missing {n}"
  for m in mutations do
    let got ← replayVerdict base (cs.filterMap m.change)
    unless got == m.lean do throwError "{m.id}: Lean's verdict is {got}, expected {m.lean}"
    row m.id got m.leanforth m.rule "5.2.1b" ""
  -- 3b. Replay of the non-recursive `ind.bool` block, unchanged and mutated.
  let some boolBlock := accepted.find? (·.id == "ind.bool") | throwError "no ind.bool"
  let bd ← liftTermElabM boolBlock.decl
  let .ok withB := base.addDeclCore 0 0 bd none | throwError "ind.bool not accepted"
  let bcs ← [`IE.B, `IE.B.false, `IE.B.true, `IE.B.rec].mapM fun n => match withB.find? n with
    | some c => pure c
    | none => throwError "missing {n}"
  for m in boolMutations do
    let got ← replayVerdict base (bcs.filterMap m.change)
    unless got == m.lean do throwError "{m.id}: Lean's verdict is {got}, expected {m.lean}"
    row m.id got m.leanforth m.rule "5.2.1a" ""
  -- 3c. Replays of three more blocks, mutated.
  for (blockId, ms) in blockReplays do
    let cs ← blockConstants base blockId
    for m in ms do
      let got ← replayVerdict base (cs.filterMap m.change)
      unless got == m.lean do throwError "{m.id}: Lean's verdict is {got}, expected {m.lean}"
      row m.id got m.leanforth m.rule "5.2.1a" ""
  -- 3d. Declarations after a block: the last one's verdict.
  let some (.recInfo bRec) := withB.find? `IE.B.rec | throwError "no IE.B.rec"
  for s in sequels bRec.type do
    let got := lastVerdict (← sequelStart base bcs s) s.decls
    unless got == s.lean do throwError "{s.id}: Lean's verdict is {got}, expected {s.lean}"
    row s.id got s.leanforth s.rule s.task ""
  -- 3e. A block without its recursors, then a use of the generated one.
  for s in stripped do
    let (_, start, r) ← strippedStart base s
    let got := lastVerdict start (s.uses r)
    unless got == s.lean do throwError "{s.id}: Lean's verdict is {got}, expected {s.lean}"
    row s.id got s.leanforth s.rule s.task ""
  -- 4. Hand-built declarations, in the `import Lean` environment.
  for c in onBase do
    let got := verdict (addAll base c.decls)
    unless got == c.lean do throwError "{c.id}: Lean's verdict is {got}, expected {c.lean}"
    row c.id got c.leanforth c.rule c.task ""
  let twiceDecl ← liftTermElabM twice.decl
  let got := verdict (addAll base [twiceDecl, twiceDecl])
  unless got == twice.lean do throwError "{twice.id}: Lean's verdict is {got}, expected {twice.lean}"
  row twice.id got twice.leanforth twice.rule twice.task ""
  -- 5. Primitive names and quotient initialisation, from an empty environment.
  let empty := (← mkEmptyEnvironment).toKernelEnv
  for c in chains do
    let got := verdict (addAll empty c.decls)
    unless got == c.lean do throwError "{c.id}: Lean's verdict is {got}, expected {c.lean}"
    row c.id got c.leanforth c.rule c.task ""
  -- 6. Every case as a file, after the rows (see `writeCase`).
  let .ok add := kernelAddFn env | throwError "no Kernel.Environment.add"
  let baseRecs ← recursorsOf base
  for b in accepted ++ checks do
    let d ← liftTermElabM b.decl
    let e := addOrHold add base base d
    writeCase base baseRecs b.id e (ownOf base e d) ((typeNames d).take 1)
  for r in reductions do
    let n := `IE ++ r.id.toName
    let d ← liftTermElabM (r.decl n)
    writeCase base baseRecs r.id (addOrHold add base base d) [n] [n]
  for m in mutations do writeMutation add base baseRecs `IE.N cs m
  for m in boolMutations do writeMutation add base baseRecs `IE.B bcs m
  for (blockId, ms) in blockReplays do
    let cs ← blockConstants base blockId
    let root := (cs.head?.map (·.name)).getD .anonymous
    for m in ms do writeMutation add base baseRecs root cs m
  for s in sequels bRec.type do writeSequel add base baseRecs bcs s
  for s in stripped do
    let (kept, _, r) ← strippedStart base s
    writeStripped add base baseRecs kept r s
  for c in onBase do
    writeSegments base baseRecs c.id (chainSegments add base base c.decls)
  writeSegments base baseRecs twice.id (chainSegments add base base [twiceDecl, twiceDecl])
  for c in chains do
    writeSegments empty {} c.id (chainSegments add base empty c.decls)

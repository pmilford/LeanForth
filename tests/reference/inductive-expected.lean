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
  `Nat.add` and so on, whatever their definitions say. `forged.*`: the same
  with `Nat.pow`, `Nat.shiftLeft` or a block named `Nat.add`, met while a
  block is checked (review rvN1 B1, B2).
* `quotinit.*`: initialising quotients (`Declaration.quotDecl`) needs `Eq`
  with exactly Lean's shape.

Columns: `id`, Lean's verdict (checked here), the outcome LeanForth must give
once its plan task is done, the ADR 0015 rule, the plan task, and the facts
of an accepted block (empty otherwise). Until its task is done LeanForth
answers *unsupported* for the row, never *accepted*.
-/

open Lean Elab Command Term Meta

universe u v

/-- `Type`, as a definition: a type whose telescope ends in it is a `Sort` only after
unfolding (row `universe.type-a-sort-by-definition`). -/
def PSortDef : Type 1 := Type

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
  ("because its second argument does not fit in a 32-bit unsigned integer", "natCountTooBig"),
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
  /-- false: the block's file leaves the recursors Lean generated out, as a
  file may (ADR 0015 B4; Lean's replay accepts it). -/
  recursors : Bool := true

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
    lean := "accepted", leanforth := "accepted", rule := "A1 P1 G1", task := "5.2.1b" },
  -- Review rvN1 (M1): a W type; recursive blocks with indices (task 5.2.1c's, decided
  -- already: the hypothesis's indices read under its own binders, the minor premise's
  -- past the hypotheses), an `Acc` among them; reflexive fields whose binders are
  -- annotated or whose Pi body is a redex.
  { id := "ind.w-type", lparams := [`u, `v], nparams := 2,
    types := [⟨"W", "(α : Type u) → (α → Type v) → Type (max u v)",
      [("sup", "(α : Type u) → (β : α → Type v) → (a : α) → (β a → W α β) → W α β")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 U1 G1", task := "5.2.1b" },
  { id := "ind.acc", lparams := [`u], nparams := 2,
    types := [⟨"MAcc", "(α : Sort u) → (α → α → Prop) → α → Prop",
      [("intro", "(α : Sort u) → (r : α → α → Prop) → (x : α) → " ++
        "((y : α) → r y x → MAcc α r y) → MAcc α r x")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 E3 G1", task := "5.2.1c" },
  { id := "ind.vec", nparams := 1, types := [⟨"Vec", "Type → Nat → Type",
      [("nil", "(α : Type) → Vec α Nat.zero"),
       ("cons", "(α : Type) → (n : Nat) → α → Vec α n → Vec α (Nat.succ n)")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 G1", task := "5.2.1c" },
  { id := "ind.reflexive-indexed", types := [⟨"RI", "Nat → Type",
      [("z", "RI Nat.zero"), ("lim", "((n : Nat) → RI n) → RI Nat.zero")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 G1", task := "5.2.1c" },
  { id := "ind.indexed-mixed", types := [⟨"DT", "Nat → Type",
      [("leaf", "DT Nat.zero"),
       ("node", "(n : Nat) → DT n → (m : Nat) → (Nat → DT m) → DT (Nat.succ n)")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 G1", task := "5.2.1c" },
  { id := "ind.reflexive-indexed-dependent", types := [⟨"IR", "Nat → Type",
      [("z", "IR Nat.zero"),
       ("mk", "(n : Nat) → (f : (k : Nat) → IR (Nat.succ k)) → IR (Nat.succ n) → IR n")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 G1", task := "5.2.1c" },
  { id := "ind.indexed-predicate-one-constructor", types := [⟨"LeOne", "Nat → Prop",
      [("mk", "(n : Nat) → LeOne n → LeOne n")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 E3 G1", task := "5.2.1c" },
  { id := "ind.reflexive-annotated-binders", types := [⟨"AX", "Type",
      [("z", "AX"), ("mk", "((n : optParam Nat Nat.zero) → (m : outParam Nat) → AX) → AX")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 G1", task := "5.2.1b" },
  { id := "ind.reflexive-body-redex", types := [⟨"BR", "Type",
      [("z", "BR"), ("mk", "(Nat → (fun (X : Type) => X) BR) → BR")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 P1 G1", task := "5.2.1b" },
  { id := "ind.redex-with-parameter", nparams := 1, types := [⟨"RBP", "Type → Type",
      [("z", "(α : Type) → RBP α"),
       ("mk", "(α : Type) → (fun (X : Type) => α → X) (RBP α) → RBP α")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 P1 G1", task := "5.2.1b" },
  -- A block of 600 constructors `c0 … c599`: LeanForth's 512 per block
  -- were a fixed limit until plan task 6.2.0 (2026-11-04). Its file leaves
  -- the recursor out: with it, its 600 rules of 601 binders each make the
  -- file about 29 MB and Lean's run several minutes longer.
  { id := "ind.many-constructors", types := [⟨"Many", "Type",
      (List.range 600).map fun j => (s!"c{j}", "Many")⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1", task := "5.2.1a",
    recursors := false }
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
  -- A redex in a Pi's domain that drops the type: Lean tests the domain for an
  -- occurrence before any reduction (review rvN1 M1). And the type as an index of
  -- another inductive type: no nesting, a non-valid occurrence.
  { id := "pos.negative-redex-domain",
    types := [⟨"Bad", "Type", [("mk", "((fun (X : Type) => Nat) Bad → Bad) → Bad")]⟩],
    lean := "nonPositive", leanforth := "rejected", rule := "P1", task := "5.2.1b" },
  { id := "pos.negative-redex-domain-later",
    types := [⟨"Bad", "Type",
      [("z", "Bad"), ("mk", "(Nat → (fun (X : Type) => Nat) Bad → Bad) → Bad")]⟩],
    lean := "nonPositive", leanforth := "rejected", rule := "P1", task := "5.2.1b" },
  -- Positivity and the recursor's hypothesis through iota (task 5.2.1b, iota.fs): a
  -- field whose type Bool.rec reduces to the type itself (recursive), or to Nat, which
  -- erases a negative occurrence.
  { id := "pos.through-recursor",
    types := [⟨"T", "Type", [("z", "T"), ("mk", "@Bool.rec (fun _ => Type) Nat T Bool.true → T")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 P1 R1 G1", task := "5.2.1b" },
  { id := "pos.erased-by-recursor",
    types := [⟨"T", "Type",
      [("z", "T"), ("mk", "@Bool.rec (fun _ => Type) (T → Nat) Nat Bool.true → T")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 P1 R1", task := "5.2.1b" },
  { id := "pos.non-valid-index-of-other",
    types := [⟨"Bad", "Type", [("z", "Bad"), ("mk", "@HEq Type Nat Type Bad → Bad")]⟩],
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
  -- A telescope that ends in a definition equal to `Type` (review rvN1 M1).
  { id := "universe.type-a-sort-by-definition",
    types := [⟨"TD", "PSortDef", [("z", "TD"), ("mk", "TD → TD")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 T2", task := "5.2.1b" },
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
    lean := "accepted", leanforth := "accepted", rule := "A1 E1", task := "5.2.5a" },
  { id := "mutual.tree-forest",
    types := [⟨"Tree", "Type", [("node", "Nat → Forest → Tree")]⟩,
              ⟨"Forest", "Type", [("nil", "Forest"), ("cons", "Tree → Forest → Forest")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1", task := "5.2.5a" },
  { id := "mutual.single-ctor-props",
    types := [⟨"A", "Prop", [("a", "A")]⟩, ⟨"B", "Prop", [("b", "B")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 E1", task := "5.2.5a" },
  { id := "mutual.universe-mismatch",
    types := [⟨"A", "Type", [("a", "B → A")]⟩, ⟨"B", "Prop", [("b", "B")]⟩],
    lean := "mutualUniverseMismatch", leanforth := "rejected", rule := "T4", task := "5.2.5a" },
  { id := "mutual.parameter-mismatch", nparams := 1,
    types := [⟨"A", "Type → Type", []⟩, ⟨"B", "Prop → Type", []⟩],
    lean := "mutualParamMismatch", leanforth := "rejected", rule := "T3", task := "5.2.5a" },
  { id := "mutual.parameter-count", nparams := 1,
    types := [⟨"A", "Type → Type", []⟩, ⟨"B", "Type", []⟩],
    lean := "paramCountMismatch", leanforth := "rejected", rule := "T3", task := "5.2.5a" },
  -- Mutual blocks without literals (plan task 5.2.5): predicates and data with indices,
  -- three types with a parameter and a universe, a function field into the other type,
  -- and a negative occurrence of the other type.
  { id := "mutual.even-odd-constructors",
    types := [⟨"Ev", "Nat → Prop", [("zero", "Ev Nat.zero"),
                                     ("succ", "(n : Nat) → Od n → Ev (Nat.succ n)")]⟩,
              ⟨"Od", "Nat → Prop", [("succ", "(n : Nat) → Ev n → Od (Nat.succ n)")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 E1 G1", task := "5.2.5a" },
  { id := "mutual.indexed-data",
    types := [⟨"MA", "Nat → Type", [("a0", "MA Nat.zero"),
                                     ("a1", "(n : Nat) → MB n → MA (Nat.succ n)")]⟩,
              ⟨"MB", "Nat → Type", [("b", "(n : Nat) → MA n → MB n")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 G1", task := "5.2.5a" },
  { id := "mutual.three-types", lparams := [`u], nparams := 1,
    types := [⟨"X", "Type u → Type u", [("x", "(α : Type u) → α → Y α → X α"),
                                         ("xe", "(α : Type u) → X α")]⟩,
              ⟨"Y", "Type u → Type u", [("y", "(α : Type u) → Z α → Y α")]⟩,
              ⟨"Z", "Type u → Type u", [("z", "(α : Type u) → X α → Z α"),
                                         ("ze", "(α : Type u) → Z α")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 G1", task := "5.2.5a" },
  { id := "mutual.reflexive",
    types := [⟨"MR", "Type", [("r", "(Nat → MS) → MR")]⟩,
              ⟨"MS", "Type", [("s", "MR → MS"), ("s0", "MS")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 P1 G1", task := "5.2.5a" },
  { id := "mutual.non-positive",
    types := [⟨"MA", "Type", [("a", "(MB → Nat) → MA")]⟩, ⟨"MB", "Type", [("b", "MA → MB")]⟩],
    lean := "nonPositive", leanforth := "rejected", rule := "P1", task := "5.2.5a" },
  -- One constructor in the whole block, whose field is a proof: a single type would
  -- eliminate into every universe (E3), a mutual block only into Prop (E1).
  { id := "mutual.one-constructor",
    types := [⟨"OA", "Prop", [("a", "OB → OA")]⟩, ⟨"OB", "Prop", []⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 E1", task := "5.2.5a" },
  -- Nested blocks.
  { id := "nested.tree", types := [⟨"Tree", "Type", [("node", "List Tree → Tree")]⟩],
    lean := "accepted", leanforth := "accepted", rule := "A1 N1", task := "5.2.5b" },
  { id := "nested.non-positive",
    types := [⟨"Bad", "Type", [("mk", "List (Bad → Nat) → Bad")]⟩],
    lean := "nonPositive", leanforth := "rejected", rule := "N1 P1", task := "5.2.5b" },
  { id := "nested.local-variable",
    types := [⟨"Bad", "Type", [("mk", "(α : Type) → List (Prod α Bad) → Bad")]⟩],
    lean := "nestedLocalVariable", leanforth := "rejected", rule := "N2", task := "5.2.5b" },
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
  -- Iota without literals (task 5.2.1b, iota.fs): a constructor major premise, a rule's
  -- fields and induction hypotheses, an argument after the major premise, a major
  -- premise that is stuck, Nat.zero; Nat.succ, which Lean's reduce_nat turns into a
  -- literal first (L1, task 5.2.3); and Eq.refl, a K-like recursor's constructor.
  { id := "iota.bool-true", type := "@Bool.rec (fun _ => Prop) False True Bool.true",
    value := "True.intro",
    lean := "accepted", leanforth := "accepted", rule := "R1", task := "5.2.1b" },
  { id := "iota.bool-true-wrong", type := "@Bool.rec (fun _ => Prop) True False Bool.true",
    value := "True.intro",
    lean := "declTypeMismatch", leanforth := "rejected", rule := "R1", task := "5.2.1b" },
  { id := "iota.list-hypothesis",
    type := "@List.rec Bool (fun _ => Prop) True (fun _ _ ih => ih) (List.cons Bool.true List.nil)",
    value := "True.intro",
    lean := "accepted", leanforth := "accepted", rule := "R1", task := "5.2.1b" },
  { id := "iota.list-hypothesis-wrong",
    type := "@List.rec Bool (fun _ => Prop) False (fun _ _ ih => ih) (List.cons Bool.true List.nil)",
    value := "True.intro",
    lean := "declTypeMismatch", leanforth := "rejected", rule := "R1", task := "5.2.1b" },
  { id := "iota.list-field",
    type := "@List.rec Prop (fun _ => Prop) False (fun h _ _ => h) (List.cons True List.nil)",
    value := "True.intro",
    lean := "accepted", leanforth := "accepted", rule := "R1", task := "5.2.1b" },
  { id := "iota.argument-after-major",
    type := "@Bool.rec (fun _ => Prop → Prop) (fun p => p) (fun _ => False) Bool.false True",
    value := "True.intro",
    lean := "accepted", leanforth := "accepted", rule := "R1", task := "5.2.1b" },
  { id := "iota.bool-stuck", type := "∀ b : Bool, @Bool.rec (fun _ => Prop) True True b",
    value := "fun (b : Bool) => True.intro",
    lean := "declTypeMismatch", leanforth := "rejected", rule := "R1", task := "5.2.1b" },
  { id := "iota.nat-zero", type := "@Nat.rec (fun _ => Prop) True (fun _ _ => False) Nat.zero",
    value := "True.intro",
    lean := "accepted", leanforth := "accepted", rule := "R1", task := "5.2.1b" },
  { id := "iota.nat-succ",
    type := "@Nat.rec (fun _ => Prop) False (fun _ _ => True) (Nat.succ Nat.zero)",
    value := "True.intro",
    lean := "accepted", leanforth := "accepted", rule := "R1 L1", task := "5.2.3" },
  { id := "iota.eq-refl",
    type := "@Eq.rec Bool Bool.true (fun _ _ => Prop) True Bool.true (Eq.refl Bool.true)",
    value := "True.intro",
    lean := "accepted", leanforth := "accepted", rule := "R1 R2", task := "5.2.1c" },
  -- Review rvN1 round 2 (L1; its io.* probes): a reduct whose recursive call keeps the
  -- recursor's universe arguments, and structure eta in iota (R3) on PUnit and Prod, not
  -- on And (a proposition, BL-8).
  { id := "iota.levels-in-reduct",
    type := "∀ (b : Bool) (l : List Bool), @Eq.{2} Type (@List.rec.{2, 0} Bool " ++
      "(fun (_ : List Bool) => Type) Bool (fun (_ : Bool) (_ : List Bool) (ih : Type) => ih → Bool) " ++
      "(List.cons b l)) (@List.rec.{2, 0} Bool (fun (_ : List Bool) => Type) Bool " ++
      "(fun (_ : Bool) (_ : List Bool) (ih : Type) => ih → Bool) l → Bool)",
    value := "fun (b : Bool) (l : List Bool) => @Eq.refl.{2} Type (@List.rec.{2, 0} Bool " ++
      "(fun (_ : List Bool) => Type) Bool (fun (_ : Bool) (_ : List Bool) (ih : Type) => ih → Bool) l → Bool)",
    lean := "accepted", leanforth := "accepted", rule := "R1", task := "5.2.1b" },
  { id := "iota.levels-in-reduct-wrong",
    type := "∀ (b : Bool) (l : List Bool), @Eq.{2} Type (@List.rec.{2, 0} Bool " ++
      "(fun (_ : List Bool) => Type) Bool (fun (_ : Bool) (_ : List Bool) (ih : Type) => ih → Bool) " ++
      "(List.cons b l)) (@List.rec.{2, 0} Bool (fun (_ : List Bool) => Type) Bool " ++
      "(fun (_ : Bool) (_ : List Bool) (ih : Type) => ih → Bool) l → @List.rec.{2, 0} Bool " ++
      "(fun (_ : List Bool) => Type) Bool (fun (_ : Bool) (_ : List Bool) (ih : Type) => ih → Bool) l)",
    value := "fun (b : Bool) (l : List Bool) => @Eq.refl.{2} Type (@List.rec.{2, 0} Bool " ++
      "(fun (_ : List Bool) => Type) Bool (fun (_ : Bool) (_ : List Bool) (ih : Type) => ih → Bool) " ++
      "l → @List.rec.{2, 0} Bool (fun (_ : List Bool) => Type) Bool " ++
      "(fun (_ : Bool) (_ : List Bool) (ih : Type) => ih → Bool) l)",
    lean := "declTypeMismatch", leanforth := "rejected", rule := "R1", task := "5.2.1b" },
  { id := "iota.punit-eta", type := "∀ p : PUnit.{1}, @PUnit.rec.{1, 1} (fun _ => Bool) true p = true",
    value := "fun (p : PUnit.{1}) => Eq.refl true",
    lean := "accepted", leanforth := "accepted", rule := "R1 R3", task := "5.2.2" },
  { id := "iota.prod-eta",
    type := "∀ p : Bool × Bool, @Prod.rec Bool Bool (fun _ => Bool) (fun _ _ => true) p = true",
    value := "fun (p : Bool × Bool) => Eq.refl true",
    lean := "accepted", leanforth := "accepted", rule := "R1 R3", task := "5.2.2" },
  { id := "iota.and-prop-stuck-bool",
    type := "∀ (h : True ∧ True), @And.rec True True (fun _ => Bool) (fun _ _ => true) h = true",
    value := "fun (h : True ∧ True) => Eq.refl true",
    lean := "declTypeMismatch", leanforth := "rejected", rule := "R1 R3", task := "5.2.2" },
  { id := "iota.structure-eta",
    type := "∀ p : Nat × Nat, @Prod.rec Nat Nat (fun _ => Nat) (fun a _ => a) p = p.1",
    value := "fun (p : Nat × Nat) => Eq.refl p.1",
    lean := "accepted", leanforth := "accepted", rule := "R1 R3", task := "5.2.2" },
  -- Two projections of one term that differ only in the field (p.1, p.2 unfolded).
  { id := "proj.index-differs",
    type := "∀ p : Nat × Nat, p.1 = p.2", value := "fun (p : Nat × Nat) => Eq.refl p.1",
    lean := "declTypeMismatch", leanforth := "rejected", rule := "J1", task := "5.2.2" },
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
  -- K whose types agree only up to unfolding (`id b` is `b`), whose major premise's
  -- type is the inductive type only after whnf (`id (a = a)`), and on `True`, a type
  -- without indices.
  { id := "k.eq-ends-defeq",
    type := "∀ (b : Nat) (h : b = id b), @Eq.rec Nat b (fun _ _ => Nat) 5 (id b) h = 5",
    value := "fun (b : Nat) (h : b = id b) => Eq.refl 5",
    lean := "accepted", leanforth := "accepted", rule := "R2", task := "5.2.1c" },
  { id := "k.type-through-definition",
    type := "∀ (a : Nat) (h : id (a = a)), @Eq.rec Nat a (fun _ _ => Nat) 5 a h = 5",
    value := "fun (a : Nat) (h : id (a = a)) => Eq.refl 5",
    lean := "accepted", leanforth := "accepted", rule := "R2", task := "5.2.1c" },
  { id := "k.true-variable-proof",
    type := "∀ (h : True), @True.rec (fun _ => Nat) 5 h = 5",
    value := "fun (h : True) => Eq.refl 5",
    lean := "accepted", leanforth := "accepted", rule := "R2", task := "5.2.1c" },
  -- K's types differ by a wrong right side: Eq.rec stays stuck on h.
  { id := "k.eq-different-ends-wrong",
    type := "∀ (a : Nat) (h : a = a + 1), @Eq.rec Nat a (fun _ _ => Nat) 5 (a + 1) h = 5",
    value := "fun (a : Nat) (h : a = a + 1) => Eq.refl 5",
    lean := "declTypeMismatch", leanforth := "rejected", rule := "R2", task := "5.2.1c" },
  { id := "eta.structure",
    type := "∀ p : Nat × Nat, p = (p.1, p.2)", value := "fun (p : Nat × Nat) => Eq.refl p",
    lean := "accepted", leanforth := "accepted", rule := "R4", task := "5.2.2" },
  -- Structure eta the other way round (the constructor on the left: try_eta_struct's
  -- second core), and with a field that is not the projection.
  { id := "eta.structure-left",
    type := "∀ p : Nat × Nat, (p.1, p.2) = p", value := "fun (p : Nat × Nat) => Eq.refl (p.1, p.2)",
    lean := "accepted", leanforth := "accepted", rule := "R4", task := "5.2.2" },
  { id := "eta.structure-wrong-field",
    type := "∀ p : Bool × Bool, p = (p.1, true)", value := "fun (p : Bool × Bool) => Eq.refl p",
    lean := "declTypeMismatch", leanforth := "rejected", rule := "R4", task := "5.2.2" },
  -- The shape of Init's WellFounded.extrinsicFix₂ (its let value F'): G's hypothesis
  -- R ⟨a, b⟩ x where F wants R ⟨a, b⟩ ⟨x.1, x.2⟩, equal by structure eta on PSigma.
  { id := "eta.psigma-extrinsic-fix", thm := false,
    type := "∀ (β : Nat → Type) (C : (a : Nat) → β a → Type) (R : PSigma β → PSigma β → Prop) " ++
      "(F : (a : Nat) → (b : β a) → ((a' : Nat) → (b' : β a') → R ⟨a', b'⟩ ⟨a, b⟩ → C a' b') → " ++
      "C a b) (x : PSigma β) (G : (y : PSigma β) → R y x → C y.1 y.2), C x.1 x.2",
    value := "fun (β : Nat → Type) (C : (a : Nat) → β a → Type) (R : PSigma β → PSigma β → Prop) " ++
      "(F : (a : Nat) → (b : β a) → ((a' : Nat) → (b' : β a') → R ⟨a', b'⟩ ⟨a, b⟩ → C a' b') → " ++
      "C a b) (x : PSigma β) (G : (y : PSigma β) → R y x → C y.1 y.2) => " ++
      "F x.1 x.2 (fun a b => G ⟨a, b⟩)",
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
  -- Task 5.2.3's own: a wrong product, Nat.pow without `^` (no instances), a value of
  -- two limbs right and wrong, and get_count_arg: an exponent of 2^32 refused, 2^32 - 1 not.
  { id := "lit.mul-wrong", type := "123456789 * 987654321 = 121932631112635268",
    value := "Eq.refl 121932631112635268",
    lean := "declTypeMismatch", leanforth := "rejected", rule := "L1", task := "5.2.3" },
  { id := "lit.pow-direct", type := "Nat.pow 2 64 = 18446744073709551616",
    value := "Eq.refl 18446744073709551616",
    lean := "accepted", leanforth := "accepted", rule := "L1", task := "5.2.3" },
  { id := "lit.pow-direct-wrong", type := "Nat.pow 2 64 = 18446744073709551617",
    value := "Eq.refl 18446744073709551617",
    lean := "declTypeMismatch", leanforth := "rejected", rule := "L1", task := "5.2.3" },
  { id := "lit.pow-count-too-big", type := "Nat.pow 2 4294967296 = 0", value := "Eq.refl 0",
    lean := "natCountTooBig", leanforth := "rejected", rule := "L1", task := "5.2.3" },
  { id := "lit.pow-count-limit", type := "Nat.pow 1 4294967295 = 1", value := "Eq.refl 1",
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

/-! ### Forged arithmetic in a block's check (review rvN1 B1, B2)

Lean's `whnf` computes the `Nat` operations by name (rules L1, L5), also where it puts
a constructor's field in whnf for positivity and for the recursor (`check_positivity`,
`is_rec_argument`), on fields that mention no type of the block too. It refuses
`Nat.pow` and `Nat.shiftLeft` with a second argument of 2^32 or more (`get_count_arg`,
`type_checker.cpp` 308-313), whatever their declarations say: a fixed rule, not a
setting. And it computes on a block's own type named `Nat.add`. The numbers are written
with `Nat.zero`, `Nat.succ` and the operations only, no literal. -/

def nzero : Expr := mkConst `Nat.zero
def nsucc (e : Expr) : Expr := .app (mkConst `Nat.succ) e
def none1 : Expr := nsucc nzero
def ntwo : Expr := nsucc none1
def npow (a b : Expr) : Expr := mkAppN (mkConst `Nat.pow) #[a, b]
def nshl (a b : Expr) : Expr := mkAppN (mkConst `Nat.shiftLeft) #[a, b]
/-- `2 ^ 65536`. -/
def nbig : Expr := npow ntwo (npow ntwo (npow ntwo (npow ntwo ntwo)))
/-- `Nat.pow 1 (2 ^ 65536)`: the second argument does not fit in 32 bits. -/
def nhuge : Expr := npow none1 nbig
/-- `1 <<< (1 <<< (1 <<< 5))`: the outer shift is 2^32. -/
def nshlHuge : Expr := nshl none1 (nshl none1 (nshl none1 (nsucc (nsucc (nsucc ntwo)))))

/-- `def n (a b : Nat) : Nat := b`, named like one of Lean's operations. -/
def binaryDef (n : Name) : Declaration :=
  .defnDecl { name := n, levelParams := [], type := .forallE `a nat (.forallE `b nat nat .default) .default,
              value := .lam `a nat (.lam `b nat (.bvar 0) .default) .default, hints := .regular 1,
              safety := .safe }

/-- `@Nat.rec.{2} (fun _ => Type) Nat (fun _ _ => Nat) major`: `Nat` once `major` is a numeral. -/
def recType (major : Expr) : Expr :=
  mkAppN (mkConst `Nat.rec [2])
    #[.lam `x nat (.sort 1) .default, nat, .lam `n nat (.lam `ih (.sort 1) nat .default) .default, major]

/-- `def IE.D (n : Nat) : Type := recType n`. -/
def dDef : Declaration :=
  .defnDecl { name := `IE.D, levelParams := [], type := .forallE `n nat (.sort 1) .default,
              value := .lam `n nat (recType (.bvar 0)) .default, hints := .regular 1, safety := .safe }
def dOf (major : Expr) : Expr := .app (mkConst `IE.D) major

/-- `n : Type` with constructors `z : n` and `mk : field → n`, or `mk : field → n → n`
when `recursive`. -/
def fieldBlock (n : Name) (field : Expr) (recursive : Bool := false) : Declaration :=
  let t : Expr := mkConst n
  let mk : Expr := .forallE `h field (if recursive then .forallE `t t t .default else t) .default
  .inductDecl [] 0 [⟨n, .sort 1, [⟨n ++ `z, t⟩, ⟨n ++ `mk, mk⟩]⟩] false

/-- A field that mentions the type only in a redex that drops it:
`(fun (X : Type) => IE.D major) n`. -/
def erasedField (n : Name) (major : Expr) : Expr :=
  .app (.lam `X (.sort 1) (dOf major) .default) (mkConst n)

/-- `inductive n : Nat → Nat → Type | base : n 0 0 | step : n 0 0 → n 1 0`. -/
def addLike (n : Name) : Declaration :=
  let app (a b : Expr) : Expr := mkAppN (mkConst n) #[a, b]
  .inductDecl [] 0 [⟨n, .forallE `a nat (.forallE `b nat (.sort 1) .default) .default,
    [⟨n ++ `base, app nzero nzero⟩,
     ⟨n ++ `step, .forallE `x (app nzero nzero) (app none1 nzero) .default⟩]⟩] false

def renameConsts (m : List (Name × Name)) (e : Expr) : Expr :=
  e.replace fun x => match x with
    | .const c ls => (m.lookup c).map fun c' => Expr.const c' ls
    | _ => none

/-- `IE.Q` named `Nat.add`. -/
def addMap : List (Name × Name) :=
  [(`IE.Q, `Nat.add), (`IE.Q.base, `Nat.add.base), (`IE.Q.step, `Nat.add.step),
   (`IE.Q.rec, `Nat.add.rec)]

/-- The recursor of `addLike IE.Q` (whose `step` field is recursive: a hypothesis)
renamed to `Nat.add.rec`: the recursor `Nat.add`'s block would have if `whnf` left
`Nat.add 0 0` as it is. -/
def forgedAddRec (q : RecursorVal) : RecursorVal :=
  let renamed : RecursorVal := { q with name := `Nat.add.rec }
  let typed : RecursorVal := { renamed with type := renameConsts addMap q.type }
  { typed with all := [`Nat.add], rules := q.rules.map fun ru =>
      { ru with ctor := (addMap.lookup ru.ctor).getD ru.ctor, rhs := renameConsts addMap ru.rhs } }

/-- `Nat` and the block `addLike Nat.add` as Lean's kernel makes them, with that
recursor in place of Lean's. -/
def forgedAddConstants (empty : Kernel.Environment) :
    CommandElabM (Kernel.Environment × List ConstantInfo) := do
  let .ok env0 := empty.addDeclCore 0 0 natDecl none | throwError "no Nat"
  let .ok envA := env0.addDeclCore 0 0 (addLike `Nat.add) none | throwError "Nat.add refused"
  let .ok envQ := env0.addDeclCore 0 0 (addLike `IE.Q) none | throwError "IE.Q refused"
  let some (.recInfo q) := envQ.find? `IE.Q.rec | throwError "no IE.Q.rec"
  let own ← [`Nat.add, `Nat.add.base, `Nat.add.step].mapM fun n => match envA.find? n with
    | some c => pure c
    | none => throwError "missing {n}"
  pure (env0, own ++ [.recInfo (forgedAddRec q)])

structure Chain where
  id : String
  decls : List Declaration
  lean : String
  leanforth : String
  rule : String
  task : String

def chains : List Chain := [
  { id := "primitive.forged-add-computes", decls := [natDecl, eqDecl, forgedAdd, five],
    lean := "accepted", leanforth := "accepted", rule := "L5", task := "5.2.3" },
  { id := "primitive.forged-add-unfolds", decls := [natDecl, eqDecl, forgedAdd, five, twoAny],
    lean := "accepted", leanforth := "accepted", rule := "L5", task := "5.2.3" },
  { id := "primitive.five-is-two", decls := [natDecl, eqDecl, forgedAdd, five, twoAny, fiveIsTwo],
    lean := "accepted", leanforth := "accepted", rule := "L5", task := "5.2.3" },
  { id := "forged.pow-field", decls := [natDecl, binaryDef `Nat.pow, fieldBlock `IE.PowF (recType nhuge)],
    lean := "natCountTooBig", leanforth := "rejected", rule := "L1 L5", task := "5.2.3" },
  { id := "forged.pow-field-recursive",
    decls := [natDecl, binaryDef `Nat.pow, fieldBlock `IE.PowR (recType nhuge) true],
    lean := "natCountTooBig", leanforth := "rejected", rule := "L1 L5", task := "5.2.3" },
  { id := "forged.pow-field-small",
    decls := [natDecl, binaryDef `Nat.pow, fieldBlock `IE.PowS (recType (npow ntwo ntwo)) true],
    lean := "accepted", leanforth := "accepted", rule := "L1 L5", task := "5.2.3" },
  { id := "forged.pow-through-definition",
    decls := [natDecl, binaryDef `Nat.pow, dDef, fieldBlock `IE.PowD (dOf nhuge) true],
    lean := "natCountTooBig", leanforth := "rejected", rule := "L1 L5", task := "5.2.3" },
  { id := "forged.pow-through-definition-nonrecursive",
    decls := [natDecl, binaryDef `Nat.pow, dDef, fieldBlock `IE.PowN (dOf nhuge)],
    lean := "natCountTooBig", leanforth := "rejected", rule := "L1 L5", task := "5.2.3" },
  { id := "forged.pow-erased-by-beta",
    decls := [natDecl, binaryDef `Nat.pow, dDef, fieldBlock `IE.PowE (erasedField `IE.PowE nhuge)],
    lean := "natCountTooBig", leanforth := "rejected", rule := "L1 L5 P1", task := "5.2.3" },
  { id := "forged.shiftleft-field",
    decls := [natDecl, binaryDef `Nat.shiftLeft, fieldBlock `IE.ShlF (recType nshlHuge) true],
    lean := "natCountTooBig", leanforth := "rejected", rule := "L1 L5", task := "5.2.3" },
  { id := "forged.type-named-nat-add", decls := [natDecl, addLike `Nat.add],
    lean := "accepted", leanforth := "accepted", rule := "L1 L5 P1 G1", task := "5.2.3" },
  { id := "forged.type-named-nat-pow",
    decls := [natDecl, .inductDecl [] 0 [⟨`Nat.pow, .sort 1, [⟨`Nat.pow.mk, mkConst `Nat.pow⟩]⟩] false],
    lean := "accepted", leanforth := "accepted", rule := "L1 L5", task := "5.2.3" },
  { id := "quotinit.with-eq", decls := [eqDecl, .quotDecl],
    lean := "accepted", leanforth := "accepted", rule := "Q1", task := "5.2.4" },
  { id := "quotinit.without-eq", decls := [.quotDecl],
    lean := "unknownConstant", leanforth := "rejected", rule := "Q1", task := "5.2.4" },
  { id := "quotinit.eq-wrong-shape", decls := [eqDecl (wrong := true), .quotDecl],
    lean := "quotEqShape", leanforth := "rejected", rule := "Q1", task := "5.2.4" }
]

/-! ## Names Lean's kernel matches inside a comparison (K7; review rvU4 B1)

Lean's `is_def_eq` runs lazy delta reduction before it compares two
applications argument by argument (type_checker.cpp 1166-1192), and that loop
first asks `is_def_eq_offset` and `reduce_nat` (1043-1066), which match
`Nat.succ` and fourteen `Nat` operations by name and read the constant
`Nat.zero` as the literal `0`, whatever the environment says those constants
are. Here `Nat.zero` is an empty inductive proposition (an inductive type, so
`whnf` leaves it as it is) and `Nat.add` a definition ignoring its second
argument: the claim `Nat.add Nat.zero Nat.zero → Nat.add Nat.zero ((fun x =>
x) Nat.zero)` holds by one beta step, but Lean computes the literal `0 + 0`
and then needs the type `Nat` (or `Bool` for `Nat.beq`), which is missing or a
proposition. LeanForth answers unknown there (K7, ADR 0014 Q8) until plan task
5.2.3 ports literals; it must never accept. The twins under other names, a
free variable (no `reduce_nat`) and the same declaration with a regular hint
(Lean's argument test first) are accepted. `k7.whnf-sort` reaches K7 in `whnf`
instead: `Nat.succ Nat.zero` becomes the literal `1`, no type; and
`k7.rec-on-succ-variable` shows where `reduce_nat` gives nothing (no literal
argument). From an empty environment, as `chains`. -/

namespace K7Rows

def prop : Expr := .sort .zero
def typ : Expr := .sort (.succ .zero)
def arr (a b : Expr) : Expr := .forallE `a a b .default
def pi (t b : Expr) : Expr := .forallE `x t b .default
def lam (t b : Expr) : Expr := .lam `x t b .default
def k (n : Name) : Expr := .const n []
def ap (f : Expr) (as : List Expr) : Expr := mkAppN f as.toArray
def idProp (e : Expr) : Expr := .app (lam prop (.bvar 0)) e
def defn (n : Name) (t v : Expr) (h : ReducibilityHints := .regular 1) : Declaration :=
  .defnDecl { name := n, levelParams := [], type := t, value := v, hints := h, safety := .safe }
/-- An inductive proposition (or type) with no constructors. -/
def empty (n : Name) (t : Expr := prop) : Declaration := .inductDecl [] 0 [⟨n, t, []⟩] false
/-- `def op : Prop → Prop → Prop := fun a b => a`. -/
def op (n : Name) : Declaration := defn n (arr prop (arr prop prop)) (lam prop (lam prop (.bvar 1)))
/-- `theorem t : op z z → op z ((fun x : Prop => x) z) := fun h => h`. -/
def claim (o z : Name) : Declaration :=
  let d := ap (k o) [k z, k z]
  .thmDecl { name := `t, levelParams := [], type := pi d (ap (k o) [k z, idProp (k z)]),
             value := lam d (.bvar 0) }
/-- The same under a variable `A : Prop`: `op z A → op z ((fun x => x) A)`. -/
def claimOpen (o z : Name) : Declaration :=
  let d := ap (k o) [k z, .bvar 0]
  .thmDecl { name := `t, levelParams := [],
             type := pi prop (pi d (ap (k o) [k z, idProp (.bvar 1)])),
             value := lam prop (lam d (.bvar 0)) }
/-- `def g : Prop → Prop := fun a => Nat.add a a` with the hint given. -/
def g (h : ReducibilityHints) : Declaration :=
  defn `g (arr prop prop) (lam prop (ap (k `Nat.add) [.bvar 0, .bvar 0])) h
/-- `theorem t : g Nat.zero → g ((fun x : Prop => x) Nat.zero) := fun h => h`. -/
def gClaim : Declaration :=
  let d := .app (k `g) (k `Nat.zero)
  .thmDecl { name := `t, levelParams := [], type := pi d (.app (k `g) (idProp (k `Nat.zero))),
             value := lam d (.bvar 0) }
/-- `inductive Nat | zero | succ (n : Nat)`. -/
def natInd : Declaration :=
  .inductDecl [] 0 [⟨`Nat, typ, [⟨`Nat.zero, k `Nat⟩, ⟨`Nat.succ, arr (k `Nat) (k `Nat)⟩]⟩] false
/-- `@Nat.rec.{1} (fun _ => Prop) A (fun _ ih => ih) m`. -/
def recProp (A m : Expr) : Expr :=
  ap (.const `Nat.rec [.succ .zero]) [lam (k `Nat) prop, A, lam (k `Nat) (lam prop (.bvar 0)), m]
/-- `theorem t (A : Prop) (n : Nat) (h : rec A n) : rec A (Nat.succ n) := h`: iota on
`Nat.succ n`, a constructor application whose argument is a variable. -/
def recSuccVariable : Declaration :=
  .thmDecl { name := `t, levelParams := [],
             type := pi prop (pi (k `Nat) (pi (recProp (.bvar 1) (.bvar 0))
               (recProp (.bvar 2) (.app (k `Nat.succ) (.bvar 1))))),
             value := lam prop (lam (k `Nat) (lam (recProp (.bvar 1) (.bvar 0)) (.bvar 0))) }
/-- `succ : Type → Type := fun _ => Prop`, then `def kk : Π (A : succ zero) (h : A), A`. -/
def sortUse (zero succ : Name) : List Declaration :=
  let dom := .app (k succ) (k zero)
  [empty zero typ, defn succ (arr typ typ) (lam typ prop),
   defn `kk (pi dom (pi (.bvar 0) (.bvar 1))) (lam dom (lam (.bvar 0) (.bvar 0)))]

end K7Rows

open K7Rows in
def k7Chains : List Chain := [
  { id := "k7.unknown-nat", decls := [empty `Nat.zero, op `Nat.add, claim `Nat.add `Nat.zero],
    lean := "unknownConstant", leanforth := "rejected", rule := "K7", task := "5.2.3" },
  { id := "k7.nat-is-prop",
    decls := [empty `Nat, empty `Nat.zero, op `Nat.add, claim `Nat.add `Nat.zero],
    lean := "declTypeMismatch", leanforth := "rejected", rule := "K7", task := "5.2.3" },
  { id := "k7.beq-bool", decls := [empty `Nat.zero, op `Nat.beq, claim `Nat.beq `Nat.zero],
    lean := "unknownConstant", leanforth := "rejected", rule := "K7", task := "5.2.3" },
  { id := "k7.mul", decls := [empty `Nat.zero, op `Nat.mul, claim `Nat.mul `Nat.zero],
    lean := "unknownConstant", leanforth := "rejected", rule := "K7", task := "5.2.3" },
  { id := "k7.abbrev-head", decls := [empty `Nat.zero, op `Nat.add, g .abbrev, gClaim],
    lean := "unknownConstant", leanforth := "rejected", rule := "K7", task := "5.2.3" },
  { id := "k7.opaque-hint-head", decls := [empty `Nat.zero, op `Nat.add, g .opaque, gClaim],
    lean := "unknownConstant", leanforth := "rejected", rule := "K7", task := "5.2.3" },
  { id := "k7.regular-head", decls := [empty `Nat.zero, op `Nat.add, g (.regular 2), gClaim],
    lean := "accepted", leanforth := "accepted", rule := "delta", task := "4.2.2d" },
  { id := "k7.twin", decls := [empty `Zz, op `Zadd, claim `Zadd `Zz],
    lean := "accepted", leanforth := "accepted", rule := "delta", task := "4.2.2d" },
  { id := "k7.with-free-variable",
    decls := [empty `Nat.zero, op `Nat.add, claimOpen `Nat.add `Nat.zero],
    lean := "accepted", leanforth := "accepted", rule := "delta", task := "4.2.2d" },
  { id := "k7.whnf-sort", decls := sortUse `Nat.zero `Nat.succ,
    lean := "typeExpected", leanforth := "rejected", rule := "K7", task := "5.2.3" },
  { id := "k7.whnf-sort-twin", decls := sortUse `Zz `Zs,
    lean := "accepted", leanforth := "accepted", rule := "whnf", task := "4.2.2c" },
  -- reduce_nat needs literals: on Nat.succ n with n a variable it gives
  -- nothing, and iota takes Nat.succ n as a constructor (K7 only where
  -- reduce_nat computes; N1's observation).
  { id := "k7.rec-on-succ-variable", decls := [natInd, recSuccVariable],
    lean := "accepted", leanforth := "accepted", rule := "R1", task := "5.2.1b" }
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

/-- `def n : (Bool, Nat).1 := value`, the type an `Expr.proj` of a constructor application
(task 5.2.2): `reduce_proj` makes it `Bool`. -/
def projDef (n : Name) (value : Expr) : Declaration :=
  let pair := mkAppN (mkConst `Prod.mk [1, 1]) #[.sort 1, .sort 1, mkConst `Bool, mkConst `Nat]
  .defnDecl { name := n, levelParams := [], type := .proj `Prod 0 pair, value,
              hints := .regular 1, safety := .safe }

/-! ### Axioms and opaque declarations (plan tasks 5.3.1 and 4.2.6)

`add_axiom` accepts an axiom whose type is well formed; `add_opaque` checks the value
against the type, and the kernel never unfolds an opaque constant. LeanForth gives the
same verdicts; an axiom outside its allowlist (a file's own, or `propext` with another
statement) marks its users NOT PROVED, which tests/core/inductive-table.py checks from
the axiom bits LeanForth reports. -/
def axiomD (n : Name) (type : Expr) : Declaration :=
  .axiomDecl { name := n, levelParams := [], type := type, isUnsafe := false }
def secretUse : List Declaration :=
  [axiomD `IE.Secret (.sort 0), axiomD `IE.secret (mkConst `IE.Secret),
   .thmDecl { name := `IE.usesSecret, levelParams := [], type := mkConst `IE.Secret,
              value := mkConst `IE.secret }]
-- `propext` with the statement `∀ a : Prop, a`, and a theorem proved by it.
def alteredPropext : List Declaration :=
  [axiomD `propext (foralls [(`a, .sort 0)] (v `a)),
   .thmDecl { name := `IE.anything, levelParams := [], type := foralls [(`a, .sort 0)] (v `a),
              value := mkConst `propext }]
def opaqueD (n : Name) (value : Expr) : Declaration :=
  .opaqueDecl { name := n, levelParams := [], type := nat, value := value, isUnsafe := false, all := [n] }
-- The twin: `IE.hidden` a definition, which the kernel unfolds.
def hiddenDef : Declaration :=
  .defnDecl { name := `IE.hidden, levelParams := [], type := nat, value := lit 5,
              hints := .regular 1, safety := .safe }
-- `IE.hidden = 5` by `Eq.refl 5`: true only if `IE.hidden` unfolds.
def hiddenFive : Declaration :=
  .thmDecl { name := `IE.hiddenFive, levelParams := [], type := eqC 1 nat (mkConst `IE.hidden) (lit 5),
             value := reflC 1 nat (lit 5) }

def onBase : List Chain := [
  { id := "postulate.declared-and-used", decls := secretUse,
    lean := "accepted", leanforth := "accepted", rule := "A1", task := "5.3.1" },
  { id := "opaque.accepted", decls := [opaqueD `IE.hidden (lit 5)],
    lean := "accepted", leanforth := "accepted", rule := "O1", task := "4.2.6" },
  { id := "opaque.wrong-value", decls := [opaqueD `IE.hiddenWrong (mkConst `Bool.true)],
    lean := "declTypeMismatch", leanforth := "rejected", rule := "O1", task := "4.2.6" },
  { id := "opaque.never-unfolds", decls := [opaqueD `IE.hidden (lit 5), hiddenFive],
    lean := "declTypeMismatch", leanforth := "rejected", rule := "O1", task := "4.2.6" },
  { id := "opaque.unfolds-as-definition", decls := [hiddenDef, hiddenFive],
    lean := "accepted", leanforth := "accepted", rule := "O1", task := "4.2.6" },
  { id := "names.reserved-nested-prefix", decls := [reservedPrefix],
    lean := "reservedNestedPrefix", leanforth := "rejected", rule := "T0", task := "5.2.5b" },
  { id := "names.reserved-nested-prefix-declared", decls := [nestedAux, usesNestedAux],
    lean := "reservedNestedPrefix", leanforth := "rejected", rule := "T0", task := "5.2.1a" },
  { id := "names.constructor-already-declared", decls := [takenName, takenBlock],
    lean := "alreadyDeclared", leanforth := "rejected", rule := "N2", task := "5.2.1a" },
  { id := "proj.reduces", decls := [projDef `IE.projReduces (mkConst `Bool.true)],
    lean := "accepted", leanforth := "accepted", rule := "J1", task := "5.2.2" },
  { id := "proj.reduces-wrong", decls := [projDef `IE.projReducesWrong (mkConst `Nat.zero)],
    lean := "declTypeMismatch", leanforth := "rejected", rule := "J1", task := "5.2.2" }
]

-- `Iff` as Lean's Init/Core.lean declares it, or forged: a constructor without fields,
-- so that `Iff a b` holds for any `a b`.
open K7Rows in
def iffDecl (forged : Bool := false) : Declaration :=
  let fields := if forged then [] else [(`mp, arr (v `a) (v `b)), (`mpr, arr (v `b) (v `a))]
  .inductDecl [] 2 [⟨`Iff, arr prop (arr prop prop),
    [⟨`Iff.intro, foralls ([(`a, prop), (`b, prop)] ++ fields) (ap (k `Iff) [v `a, v `b])⟩]⟩] false
-- `propext` with Lean's statement: ∀ {a b : Prop}, (a ↔ b) → a = b.
open K7Rows in
def propextDecl : Declaration :=
  axiomD `propext (foralls [(`a, prop), (`b, prop)]
    (arr (ap (k `Iff) [v `a, v `b]) (eqC 1 prop (v `a) (v `b))))
-- Any two propositions equal, by `propext` on the forged `Iff`.
open K7Rows in
def collapse : Declaration :=
  .thmDecl { name := `IE.collapse, levelParams := [],
             type := foralls [(`a, prop), (`b, prop)] (eqC 1 prop (v `a) (v `b)),
             value := funs [(`a, prop), (`b, prop)]
               (ap (k `propext) [v `a, v `b, ap (k `Iff.intro) [v `a, v `b]]) }

-- Axioms in an empty environment, where `propext` is free to take another statement,
-- or Lean's statement about another `Iff` (NOT PROVED), or about Lean's own (proved).
def axiomChains : List Chain := [
  { id := "postulate.propext-altered", decls := alteredPropext,
    lean := "accepted", leanforth := "accepted", rule := "A1", task := "5.3.1" },
  { id := "postulate.propext-forged-iff",
    decls := [eqDecl, iffDecl (forged := true), propextDecl, collapse],
    lean := "accepted", leanforth := "accepted", rule := "A1", task := "5.3.1" },
  { id := "postulate.propext-own-iff", decls := [eqDecl, iffDecl, propextDecl],
    lean := "accepted", leanforth := "accepted", rule := "A1", task := "5.3.1" }
]

/-! ### Quotient records replayed (ADR 0015 Q1)

Lean's replay adds `Declaration.quotDecl` for an exported quotient record and ignores the
record itself (`Replay.lean`; `add_quot` builds the four types): a record with another type
or other universe parameters is accepted, and a later definition is checked against Lean's
own `Quot.mk`. LeanForth accepts such a record with a warning and uses Lean's types. -/
def quotRel (u : Level) : List (Name × Expr) :=
  [(`α, .sort u), (`r, .forallE `x (v `α) (.forallE `y (v `α) (.sort 0) .default) .default)]
-- `IE.mkUse.{u} {α : Sort u} (r : α → α → Prop) (a : α) : Quot r := Quot.mk r a`
def quotUse : ConstantInfo :=
  let u := Level.param `u
  let bs := quotRel u ++ [(`a, v `α)]
  .defnInfo { name := `IE.mkUse, levelParams := [`u],
              type := foralls bs (mkAppN (.const `Quot [u]) #[v `α, v `r]),
              value := funs bs (mkAppN (.const `Quot.mk [u]) #[v `α, v `r, v `a]),
              hints := .regular 1, safety := .safe, all := [`IE.mkUse] }
def onQuot (n : Name) (f : QuotVal → QuotVal) : ConstantInfo → Option ConstantInfo
  | .quotInfo q => some (.quotInfo (if q.name == n then f q else q))
  | c => some c
def quotMutations : List Mutation := [
  { id := "replay-quot.original", change := some,
    lean := "accepted", leanforth := "accepted", rule := "Q1" },
  { id := "replay-quot.mk-given-quot-type",
    change := onQuot `Quot.mk fun q => { q with type := foralls (quotRel (.param `u)) (.sort (.param `u)) },
    lean := "accepted", leanforth := "accepted", rule := "Q1" },
  { id := "replay-quot.lift-universe-dropped",
    change := onQuot `Quot.lift fun q => { q with levelParams := [`u] },
    lean := "accepted", leanforth := "accepted", rule := "Q1" }
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

/-- `IE.B.rec (fun _ => Bool) true false IE.B.false = rhs`, proved by `Eq.refl rhs`: Lean's
rule for `false` gives `true`, the swapped one `false` (review rvN1 round 2). -/
def bRecApp (major : Expr) : Expr :=
  mkAppN (mkConst `IE.B.rec [1])
    #[.lam `x (mkConst `IE.B) (mkConst `Bool) .default, mkConst `Bool.true, mkConst `Bool.false, major]
def bIota (n : Name) (rhs : Expr) : Declaration :=
  .thmDecl { name := n, levelParams := [],
             type := mkAppN (mkConst `Eq [1]) #[mkConst `Bool, bRecApp (mkConst `IE.B.false), rhs],
             value := mkAppN (mkConst `Eq.refl [1]) #[mkConst `Bool, rhs] }

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
    rule := "B4 L1" },
  -- Review rvN1 round 2 (L1): after B3 refused the block's swapped rules, Lean's
  -- generated recursor reduces, with its own rules; the file's are never used.
  { id := "after.b3-swapped-then-iota-lean-rule", bool := some true, change := onRec swapRules,
    decls := [bIota `IE.iotaLean (mkConst `Bool.true)], lean := "accepted",
    leanforth := "accepted", rule := "B3 R1", task := "5.2.1b" },
  { id := "after.b3-swapped-then-iota-forged-rule", bool := some true, change := onRec swapRules,
    decls := [bIota `IE.iotaForged (mkConst `Bool.false)], lean := "declTypeMismatch",
    leanforth := "rejected", rule := "B3 R1", task := "5.2.1b" }
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
  | .opaqueDecl v => [.opaqueInfo v]
  | .axiomDecl v => [.axiomInfo v]
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

/-- The constants a block's file holds: its own, without the recursors when
it leaves them out (`Block.recursors`). -/
def Block.kept (b : Block) (env : Kernel.Environment) (own : List Name) : List Name :=
  if b.recursors then own else own.filter fun n => !(env.find? n matches some (.recInfo _))

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
  /-- Which type's recursor the uses meet (0: the first type's). -/
  which : Nat := 0

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
    rule := "B4 G1", task := "5.2.5a" },
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
    rule := "B4 G1 C2", task := "5.2.1b" },
  -- Mutual blocks (plan task 5.2.5): the generated recursors of the first and of a later
  -- type, with indices, and at other universes.
  { id := "after.even-odd-left-out-then-use-rec", block := blockDecl "mutual.even-odd-constructors",
    uses := fun r => [useRecOf r], lean := "accepted", leanforth := "accepted",
    rule := "B4 G1", task := "5.2.5a" },
  { id := "after.even-odd-left-out-then-use-second-rec",
    block := blockDecl "mutual.even-odd-constructors", which := 1,
    uses := fun r => [useRecOf r], lean := "accepted", leanforth := "accepted",
    rule := "B4 G1", task := "5.2.5a" },
  { id := "after.indexed-data-left-out-then-use-second-rec", block := blockDecl "mutual.indexed-data",
    which := 1, uses := fun r => [useRecOf r], lean := "accepted", leanforth := "accepted",
    rule := "B4 G1", task := "5.2.5a" },
  { id := "after.three-types-at-concrete", block := blockDecl "mutual.three-types", which := 2,
    uses := fun r => [useRecAt "Concrete" [] [lv 0, lv 1] 0 r],
    lean := "accepted", leanforth := "accepted", rule := "B4 G1", task := "5.2.5a" },
  { id := "after.three-types-at-renamed", block := blockDecl "mutual.three-types", which := 1,
    uses := fun r => [useRecAt "Renamed" [`a, `b] [lp `a, lp `b] 0 r],
    lean := "accepted", leanforth := "accepted", rule := "B4 G1", task := "5.2.5a" },
  -- Review rvN1 (M1): the generated recursors of indexed and reflexive blocks.
  { id := "after.w-left-out-then-use-rec", block := blockDecl "ind.w-type",
    uses := fun r => [useRecOf r], lean := "accepted", leanforth := "accepted",
    rule := "B4 G1", task := "5.2.1b" },
  { id := "after.w-at-swapped", block := blockDecl "ind.w-type",
    uses := fun r => [useRecAt "Swapped" [`a, `b, `c] [lp `a, lp `c, lp `b] 0 r],
    lean := "accepted", leanforth := "accepted", rule := "B4 G1", task := "5.2.1b" },
  { id := "after.w-at-concrete", block := blockDecl "ind.w-type",
    uses := fun r => [useRecAt "Concrete" [] [lv 3, lv 0, lv 1] 0 r],
    lean := "accepted", leanforth := "accepted", rule := "B4 G1", task := "5.2.1b" },
  { id := "after.acc-left-out-then-use-rec", block := blockDecl "ind.acc",
    uses := fun r => [useRecOf r], lean := "accepted", leanforth := "accepted",
    rule := "B4 G1", task := "5.2.1c" },
  { id := "after.acc-at-concrete", block := blockDecl "ind.acc",
    uses := fun r => [useRecAt "Concrete" [] [lv 1, lv 2] 0 r],
    lean := "accepted", leanforth := "accepted", rule := "B4 G1", task := "5.2.1c" },
  { id := "after.vec-left-out-then-use-rec", block := blockDecl "ind.vec",
    uses := fun r => [useRecOf r], lean := "accepted", leanforth := "accepted",
    rule := "B4 G1", task := "5.2.1c" },
  { id := "after.reflexive-indexed-left-out-then-use-rec", block := blockDecl "ind.reflexive-indexed",
    uses := fun r => [useRecOf r], lean := "accepted", leanforth := "accepted",
    rule := "B4 G1", task := "5.2.1c" },
  { id := "after.indexed-mixed-left-out-then-use-rec", block := blockDecl "ind.indexed-mixed",
    uses := fun r => [useRecOf r], lean := "accepted", leanforth := "accepted",
    rule := "B4 G1", task := "5.2.1c" },
  { id := "after.reflexive-indexed-dependent-left-out-then-use-rec",
    block := blockDecl "ind.reflexive-indexed-dependent",
    uses := fun r => [useRecOf r], lean := "accepted", leanforth := "accepted",
    rule := "B4 G1", task := "5.2.1c" },
  { id := "after.annotated-binders-left-out-then-use-rec",
    block := blockDecl "ind.reflexive-annotated-binders",
    uses := fun r => [useRecOf r], lean := "accepted", leanforth := "accepted",
    rule := "B4 G1", task := "5.2.1b" },
  { id := "after.redex-parameter-left-out-then-use-rec", block := blockDecl "ind.redex-with-parameter",
    uses := fun r => [useRecOf r], lean := "accepted", leanforth := "accepted",
    rule := "B4 G1", task := "5.2.1b" }
]

/-- A stripped case's block constants without recursors, the environment Lean's
replay of them makes, and Lean's recursor of the block's first type. -/
def strippedStart (base : Kernel.Environment) (s : Stripped) :
    CommandElabM (List ConstantInfo × Kernel.Environment × RecursorVal) := do
  let d ← s.block
  let cs ← ownConstants base d
  let kept := cs.filter fun c => !(c matches .recInfo _)
  let some (.inductInfo t) := (cs.filter (fun c => c matches .inductInfo _))[s.which]?
    | throwError "no type"
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
  for c in chains ++ k7Chains ++ axiomChains do
    let got := verdict (addAll empty c.decls)
    unless got == c.lean do throwError "{c.id}: Lean's verdict is {got}, expected {c.lean}"
    row c.id got c.leanforth c.rule c.task ""
  -- 5b. The block named `Nat.add` replayed with a recursor that has a hypothesis.
  let (env0, forgedCs) ← forgedAddConstants empty
  let forgedId := "forged.type-named-nat-add-recursor-with-hypothesis"
  let got ← replayVerdict env0 forgedCs
  unless got == "invalidRecursor" do throwError "{forgedId}: Lean's verdict is {got}"
  row forgedId got "rejected" "L1 L5 B3" "5.2.3" ""
  -- 5c. The quotient records replayed, unchanged and changed, then a definition.
  let .ok envEq := empty.addDeclCore 0 0 (eqDecl) none | throwError "no Eq"
  let .ok envQ := envEq.addDeclCore 0 0 .quotDecl none | throwError "no quotients"
  let qcs ← [`Quot, `Quot.mk, `Quot.lift, `Quot.ind].mapM fun n => match envQ.find? n with
    | some c => pure c
    | none => throwError "missing {n}"
  let qcs := qcs ++ [quotUse]
  for m in quotMutations do
    let got ← replayVerdict envEq (qcs.filterMap m.change)
    unless got == m.lean do throwError "{m.id}: Lean's verdict is {got}, expected {m.lean}"
    row m.id got m.leanforth m.rule "5.2.4" ""
  -- 6. Every case as a file, after the rows (see `writeCase`).
  let .ok add := kernelAddFn env | throwError "no Kernel.Environment.add"
  let baseRecs ← recursorsOf base
  for b in accepted ++ checks do
    let d ← liftTermElabM b.decl
    let e := addOrHold add base base d
    writeCase base baseRecs b.id e (b.kept e (ownOf base e d)) ((typeNames d).take 1)
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
  for c in chains ++ k7Chains ++ axiomChains do
    writeSegments empty {} c.id (chainSegments add base empty c.decls)
  writeCase env0 (← recursorsOf env0) forgedId (forgedCs.foldl add env0)
    (forgedCs.map (·.name)) [`Nat.add]
  let eqRecs ← recursorsOf envEq
  for m in quotMutations do
    let cs' := qcs.filterMap m.change
    writeCase envEq eqRecs m.id (cs'.foldl add envEq) (cs'.map (·.name)) [`Quot, `IE.mkUse]

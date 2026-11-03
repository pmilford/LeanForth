# LeanForth syntax: a design sketch

**Design sketch, not implemented.** This page shows how theorems and
proofs are meant to be written in LeanForth itself, as proposed in
[ADR 0017](../adr/0017-leanforth-syntax.md) (plan task 8.1.1). LeanForth
does not define these words yet: they and the printer's Forth mode are
task 8.1.2. Every LeanForth example below was run as Forth words by a
throwaway prototype on 2026-11-02, on Gforth 1.0 and 0.7.3, which printed
the Lean form shown; the Lean examples are checked with pinned Lean 4.35.0
(`make check` runs them). Today theorems reach LeanForth from Lean exports
([workflows](WORKFLOWS.md#checking-a-theorem)).

**Trust.** The words decide nothing. They run in a separate authoring
program, which hands the checker finished terms; only the checker can
accept a theorem, and the checked statement can be printed back for you to
read.
Words such as *term*, *binder* and *universe level* are explained in
[terms for new readers](TERMS_FOR_NEW_READERS.md) and
[concepts in three forms](CONCEPTS.md).

## How to read it

Every token is a Forth word, and Forth's own interpreter runs it; there is
no other parser and no mathematics inside strings. It is postfix, like all
Forth: the parts come first, then the word that combines them.

- `$` applies a function to an argument: Lean's `f a b` is `f a $ b $`, and
  `g (f value)` is `g f value $ $`.
- `TYPE explicit: NAME` starts a variable of that type (also `implicit:`,
  `strict-implicit:`, `instance:` for Lean's `{x}`, `⦃x⦄`, `[x]`). Like
  Forth's `:`, it reads the name after it and defines a word for the
  variable; using the name pushes the variable. `fun` or `forall` ends the
  variable's scope, making a function or a "for all".
- `A B ->` is "A implies B" (or "functions from A to B").
- `Prop`, `l Type`, `l Sort` are the universes; `c l ^` gives the constant
  `c` the universe level `l` (Lean's `c.{l}`).
- `theorem NAME … := … end NAME`: the variables still open at `:=` are the
  theorem's hypotheses; before `:=` comes the statement, after it the proof.
  `end NAME` defines a word for the theorem, so later proofs can use it.
- Names are Lean's names, exactly, with upper and lower case distinct
  (`x : X` works), although Forth finds words regardless of case: each
  word checks the spelling it was called with. LeanForth's own words are
  either Lean keywords or contain a character no Lean name has (`-`, `:`,
  `$`, `^`), so they never clash with a name. Forth's own words, such as
  `+`, are not visible while a proof runs.

## Example: identity

**Mathematics.** For every proposition $P$: $P \to P$.

**LeanForth** (sketch):

```text
theorem identity
  Prop implicit: P
  P explicit: proof
  P
:=
  proof
end identity
```

**Lean**, and what both Lean and the prototype print for it:

```lean
theorem identity {P : Prop} (proof : P) : P := proof
set_option pp.unicode.fun true in
#print identity
```

```text
theorem identity : ∀ {P : Prop}, P → P :=
fun {P} proof ↦ proof
```

## Example: composition

**Mathematics.** For all propositions $A, B, C$: if $A \to B$ and
$B \to C$, then $A \to C$.

**LeanForth** (sketch): `f` and `g` are the two hypotheses; the proof takes
a proof `value` of A and returns `g (f value)`.

```text
theorem composition
  Prop implicit: A   Prop implicit: B   Prop implicit: C
  A B ->  explicit: f
  B C ->  explicit: g
  A C ->
:=
  A explicit: value   g f value $ $   fun
end composition
```

**Lean**:

```lean
theorem composition {A B C : Prop} (f : A → B) (g : B → C) : A → C :=
  fun value => g (f value)
set_option pp.unicode.fun true in
#print composition
```

```text
theorem composition : ∀ {A B C : Prop}, (A → B) → (B → C) → A → C :=
fun {A B C} f g value ↦ g (f value)
```

## Example: commutativity of addition

**Mathematics.** For all natural numbers $n, m$: $n + m = m + n$.

**LeanForth** (sketch). The form below is the *kernel form*: exactly the
term the checker checks, with every hidden argument written out. Lean's
`n + m` is generic addition `HAdd.hAdd` at the type `Nat`, with "addition
of naturals" (`instHAdd 0 ^ Nat $ instAddNat $`) passed as an argument, and
`0 ^` and `1 ^` are universe levels. Shorter forms, where a helper fills in
such arguments, are planned (task 8.3.1); the `+` sign itself stays with
the printer and editors, because in Forth `+` means machine addition.

```text
theorem add_comm'
  Nat explicit: n
  Nat explicit: m
  Eq 1 ^ Nat $
    HAdd.hAdd 0 ^ 0 ^ 0 ^ Nat $ Nat $ Nat $  instHAdd 0 ^ Nat $ instAddNat $  $  n $ m $
  $
    HAdd.hAdd 0 ^ 0 ^ 0 ^ Nat $ Nat $ Nat $  instHAdd 0 ^ Nat $ instAddNat $  $  m $ n $
  $
:=
  Nat.add_comm n $ m $
end add_comm'
```

**Lean**, printed without the `+` and `=` notation, as the prototype prints
it today:

```lean
theorem add_comm' (n m : Nat) : n + m = m + n := Nat.add_comm n m
set_option pp.unicode.fun true in
set_option pp.notation false in
#print add_comm'
```

```text
theorem add_comm' : ∀ (n m : Nat), Eq (HAdd.hAdd n m) (HAdd.hAdd m n) :=
fun n m ↦ Nat.add_comm n m
```

## Example: a proof with notes that evolves

**Mathematics.** From $A \to B$, $B \to C$ and $C \to D$ follows
$A \to D$.

**LeanForth** (sketch). Any step can get a label and a note. `note"` marks
a note written by a person, `ai-note"` one written by an AI. Notes are
never checked; they stay in the file next to their step and are printed
with the proof. Here a person has replaced an AI's first two steps by the
earlier theorem `composition` and rewritten that note; the last step and
its note did not change:

```text
theorem chain
  Prop implicit: A   Prop implicit: B   Prop implicit: C   Prop implicit: D
  A B ->  explicit: f
  B C ->  explicit: g
  C D ->  explicit: h
  A D ->
:=
  A explicit: a
    h  composition A $ B $ C $ f $ g $ a $
              label: to-C  note" composition does the first two steps at once"
       $      label: to-D  note" h finishes the chain: a proof of D"
  fun
end chain
```

The prototype printed the steps with their notes (the line numbers are
those of its input file, which begins with `composition`):

```text
  step chain/to-C (line 24), note by a person: composition does the first two steps at once
  step chain/to-D (line 25), note by a person: h finishes the chain: a proof of D
```

**Lean**:

```lean
theorem composition {A B C : Prop} (f : A → B) (g : B → C) : A → C :=
  fun value => g (f value)
theorem chain {A B C D : Prop} (f : A → B) (g : B → C) (h : C → D) : A → D :=
  fun a => h (composition f g a)
set_option pp.unicode.fun true in
#print chain
```

```text
theorem chain : ∀ {A B C D : Prop}, (A → B) → (B → C) → (C → D) → A → D :=
fun {A B C D} f g h a ↦ h (composition f g a)
```

## Mistakes point at your text

A missing `$` or a misspelt name stops at the word, with its line and
column; for an unclosed variable the message also names where that
variable was opened, for example:

```text
error at line:col 8:27 (token `valeu`): unknown name: no syntax word, bound variable, universe parameter or constant has it
```

## Not designed in detail yet

Universe levels with `max`, literals, `let`, projections, inductive types,
structures, and tactic proofs (`by`) are sketched in
[ADR 0017](../adr/0017-leanforth-syntax.md), with its open decisions for
the owner.

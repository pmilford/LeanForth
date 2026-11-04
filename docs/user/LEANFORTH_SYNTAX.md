# LeanForth syntax: theorems and proofs as Forth words

**Status (2026-11-03): implemented, experimental, not yet relied on.** The
words of [ADR 0017](../adr/0017-leanforth-syntax.md), which the owner
approved as the design, exist in `src/author/` (plan task 8.1.2): you can
write a theorem, a definition and its proof as Forth words, run them,
get your mistakes back with line and column, and print the result back
as words or in Lean's notation. They still pass the [parser] review gate
of `AGENTS.md` before anything relies on them. What is not built yet: the
separate authoring program that hands the checker finished terms (plan
task 8.2.1), so today these words build terms and print them but do not
send them to the checker; and helpers that fill in implicit arguments or
run tactics (8.3). Today theorems reach the checker from Lean exports
([workflows](WORKFLOWS.md#checking-a-theorem)).

**Trust.** The words decide nothing. They only build terms; only the
checker can accept a theorem, and the checked statement can always be
printed back for you to read. The checker never loads `src/author/`
(a test checks it). Words such as *term*, *binder* and *universe level*
are explained in [terms for new readers](TERMS_FOR_NEW_READERS.md) and
[concepts in three forms](CONCEPTS.md). Every word, its stack effect and
every error code are in the
[programming reference](../programming/LEANFORTH_WORDS.md).

## How to read it

Every token is a Forth word, and Forth's own interpreter runs it; there is
no other parser and no mathematics inside strings. It is postfix, like all
Forth: the parts come first, then the word that combines them.

- `$` applies a function to an argument: Lean's `f a b` is `f a $ b $`, and
  `g (f value)` is `g f value $ $`.
- `TYPE explicit: NAME` starts a variable of that type (also `implicit:`,
  `strict-implicit:`, `instance:` for Lean's `{x}`, `⦃x⦄`, `[x]`). Like
  Forth's `:`, it reads the name after it; using the name pushes the
  variable. `fun` or `forall` ends the variable's scope, making a function
  or a "for all".
- `A B ->` is "A implies B" (or "functions from A to B").
- `Prop`, `l Type`, `l Sort` are the universes; `c l ^` gives the constant
  `c` the universe level `l` (Lean's `c.{l}`); `u 1 level+`, `u v level-max`
  and `u v level-imax` build levels. Numbers are plain decimals (`0`, `1`,
  `12`, at most nine digits); Forth's other number forms (`-3`, `$10`,
  `1.`, `'a'`) are refused.
- `theorem NAME … := … end NAME` (also `def` and `axiom`): the variables
  still open at `:=` are the hypotheses; before `:=` comes the statement,
  after it the proof. `universe u` right after the name adds a universe
  parameter. `end NAME` defines a word for the theorem, so later proofs can
  use it. `namespace N … end N` and `open N` work as in Lean, and a name
  means the constant Lean would pick: inside `namespace N`, or in a
  declaration named `N.foo`, `bar` means `N.bar` if there is one. Where
  Lean would choose between two open namespaces by type, LeanForth asks
  for the full name.
- Names are Lean's names, exactly, with upper and lower case distinct
  (`x : X` works), although Forth finds words regardless of case: each
  word checks the spelling it was called with. LeanForth's own words are
  either Lean keywords or contain a character no Lean name has (`-`, `:`,
  `$`, `^`), so they never clash with a name. The name of a theorem,
  universe or namespace may not look like a number (`1`, `N.1`, `-x`), so
  a name never hides a number. Forth's own words, such as `+` or `dup`,
  are not visible while a proof runs.
- Comments are Forth's: `\` to the end of the line, `( … )` within a line
  (a `(` must be closed on its line).

Lean's core library is not imported yet (plan 8.2.1): a file names the
constants it uses with `import-stub NAME [universe u]… [TYPE] end NAME`, a
stand-in that only defines the constant's word (and, given a type, lets
the printer hide its implicit arguments as Lean does).

## Running it

From Forth (`gforth`, in the repository):

```text
require src/author/runner.fs
lf-author-begin  s" proof.lf" lf-author-file   \ gives an outcome (0 = ok)
lf-author-error.                               \ the first error, if any
1000 lf-author-print                           \ every declaration as words
```

The examples on this page are run by `make test` through a small helper,
`leanforth`, that runs the rest of its block as LeanForth text and prints
each theorem and definition as Lean's `#print` shows it (or the error); it
is documentation only:

```forth
\ Documentation helpers, not part of LeanForth: leanforth runs the rest of
\ its block as LeanForth text (src/author/) and prints each theorem and
\ definition as Lean's #print shows it, then each note with its step, or
\ the error; leanforth-words prints the declarations back as words.
require ~+/src/author/runner.fs
create text 8192 allot  variable text#
: text+ ( c-addr u -- ) tuck text text# @ + swap move text# +! ;
: line+ ( c-addr u -- ) text+ s"  " text+ 10 text text# @ 1- + c! ;
: rest ( -- c-addr u ) 0 text# ! begin refill while source line+ repeat text text# @ ;
: ok. ( outcome -- ) ok? 0= abort" print failed" ;
: .kind ( decl -- ) lf-fdecl-kind @ lf-decl-theorem = if ." theorem " else ." def " then ;
: .universes ( decl -- )
  dup lf-fdecl-universes @ ?dup 0= if drop exit then
  ." .{" 0 ?do i if ." , " then dup lf-fdecl-universe i cells + @ lf-print-name ok. loop
  drop ." }" ;
: .type ( decl -- )
  dup lf-fdecl-type @ 1000 rot lf-fdecl-kind @ lf-decl-theorem =
  if lf-print-statement else lf-print-term then ok. ;
: .decl ( decl -- )
  dup lf-fdecl-kind @ lf-decl-def > if drop exit then
  dup .kind dup lf-fdecl-name @ lf-print-name ok. dup .universes ."  : " dup .type ."  :=" cr
  lf-fdecl-value @ 1000 lf-print-term ok. cr ;
: label-of ( term -- c-addr u )
  lf-note-count 0 ?do dup i lf-note-on? i lf-note-kind@ lf-note-label = and
    if drop i lf-note-text@ unloop exit then loop drop s" -" ;
: .note ( decl i -- )
  ." step " swap lf-fdecl-name @ lf-print-name ok. ." /" dup lf-note-term@ label-of type
  ."  (line " dup lf-note-source@ lfa-pos> drop 0 .r ." ), note by "
  dup lf-note-kind@ lf-note-person = if ." a person: " else ." an AI: " then
  lf-note-text@ type cr ;
: .notes ( i -- )
  dup lf-author-decl swap lf-author-notes swap ?do
    i lf-note-kind@ lf-note-label <> if dup i .note then loop drop ;
: run-rest ( -- flag )
  lf-author-begin rest lf-author-text ok? dup 0= if lf-author-error. cr then ;
: leanforth ( -- )
  run-rest 0= if exit then
  lf-author-count 0 ?do i lf-author-decl .decl loop
  lf-author-count 0 ?do i .notes loop ;
: leanforth-words ( -- ) run-rest if 1000 lf-author-print ok. then ;
```

## Example: identity

**Mathematics.** For every proposition $P$: $P \to P$.

**LeanForth**, and what the words built, printed as Lean prints it:

```forth
leanforth
theorem identity
  Prop implicit: P
  P explicit: proof
  P
:=
  proof
end identity
```

```text
theorem identity : ∀ {P : Prop}, P → P :=
fun {P} proof ↦ proof
```

**Lean**, and what Lean prints for it:

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

**LeanForth**: `f` and `g` are the two hypotheses; the proof takes a proof
`value` of A and returns `g (f value)`.

```forth
leanforth
theorem composition
  Prop implicit: A   Prop implicit: B   Prop implicit: C
  A B ->  explicit: f
  B C ->  explicit: g
  A C ->
:=
  A explicit: value   g f value $ $   fun
end composition
```

```text
theorem composition : ∀ {A B C : Prop}, (A → B) → (B → C) → A → C :=
fun {A B C} f g value ↦ g (f value)
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

## Example: a universe parameter and a constant used at two levels

**Mathematics.** The identity function $\mathrm{id}_\alpha(x) = x$ for
$\alpha$ in any universe $u$; used at level $0$ it maps a proof $h$ of
$P$ to $h$.

**LeanForth**: `end fixtureId` defines the word `fixtureId`, which the
theorem then uses with the universe argument `0 ^`.

```forth
leanforth
def fixtureId
  universe u
  u Sort implicit: α
  α explicit: x
  α
:=
  x
end fixtureId

theorem fixtureUse
  Prop implicit: P
  P explicit: h
  P
:=
  fixtureId 0 ^ P $ h $      \ @fixtureId.{0} P h
end fixtureUse
```

```text
def fixtureId.{u} : {α : Sort u} → α → α :=
fun {α} x ↦ x
theorem fixtureUse : ∀ {P : Prop}, P → P :=
fun {P} h ↦ fixtureId h
```

**Lean**:

```lean
universe u
def fixtureId {α : Sort u} (x : α) : α := x
theorem fixtureUse {P : Prop} (h : P) : P := fixtureId h
set_option pp.unicode.fun true in
#print fixtureUse
```

```text
theorem fixtureUse : ∀ {P : Prop}, P → P :=
fun {P} h ↦ fixtureId h
```

## Example: commutativity of addition

**Mathematics.** For all natural numbers $n, m$: $n + m = m + n$.

**LeanForth.** This is the *kernel form*: exactly the term the checker
checks, with every hidden argument written out. Lean's `n + m` is generic
addition `HAdd.hAdd` at the type `Nat`, with "addition of naturals"
(`instHAdd 0 ^ Nat $ instAddNat $`) passed as an argument, and `0 ^` and
`1 ^` are universe levels. Shorter forms, where a helper fills in such
arguments, are planned (task 8.3.1); the `+` sign itself stays with the
printer and editors, because in Forth `+` means machine addition. The
import stubs stand in for Lean's core library:

```forth
leanforth
import-stub Nat end Nat
import-stub instAddNat end instAddNat
import-stub instHAdd  universe u_1  end instHAdd
import-stub HAdd  universe u  universe v  universe w  end HAdd
import-stub outParam  universe u  end outParam
import-stub Nat.add_comm end Nat.add_comm
import-stub Eq
  universe u_1
  u_1 Sort implicit: α
  α α Prop -> ->
end Eq
import-stub HAdd.hAdd
  universe u  universe v  universe w
  u Type implicit: α
  v Type implicit: β
  outParam w 2 level+ ^  w Type $  implicit: γ
  HAdd u ^ v ^ w ^  α $ β $ γ $  instance: self
  α β γ -> ->
end HAdd.hAdd

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

```text
theorem add_comm' : ∀ (n m : Nat), Eq (HAdd.hAdd n m) (HAdd.hAdd m n) :=
fun n m ↦ Nat.add_comm n m
```

**Lean**, printed without the `+` and `=` notation, as the term printer
prints it today:

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

**LeanForth.** Any step can get a label and a note. `note"` marks a note
written by a person, `ai-note"` one written by an AI. Notes are never
checked; they stay in the file next to their step, are printed with the
proof, and survive printing the proof back as words. Here a person has
replaced an AI's first two steps by the earlier theorem `composition` and
rewritten that note; the last step and its note did not change:

```forth
leanforth
theorem composition
  Prop implicit: A   Prop implicit: B   Prop implicit: C
  A B ->  explicit: f
  B C ->  explicit: g
  A C ->
:=
  A explicit: value   g f value $ $   fun
end composition

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

```text
theorem composition : ∀ {A B C : Prop}, (A → B) → (B → C) → A → C :=
fun {A B C} f g value ↦ g (f value)
theorem chain : ∀ {A B C D : Prop}, (A → B) → (B → C) → (C → D) → A → D :=
fun {A B C D} f g h a ↦ h (composition f g a)
step chain/to-C (line 19), note by a person: composition does the first two steps at once
step chain/to-D (line 20), note by a person: h finishes the chain: a proof of D
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

## Example: names that differ only in case

**Mathematics.** The identity on a type $X$, written with an element
$x : X$.

**LeanForth.** Forth would find `X` and `x` as one word; LeanForth's
words tell them apart, as Lean does:

```forth
leanforth
def caseVar
  0 Type implicit: X
  X explicit: x
  X
:=
  x
end caseVar
```

```text
def caseVar : {X : Type} → X → X :=
fun {X} x ↦ x
```

**Lean**:

```lean
def caseVar {X : Type} (x : X) : X := x
set_option pp.unicode.fun true in
#print caseVar
```

```text
def caseVar : {X : Type} → X → X :=
fun {X} x ↦ x
```

## Printing a proof back as words

The printer's Forth mode writes a declaration as the words that build it,
with a line per universe parameter and per hypothesis; running those
words gives the identical term, with the same names, binder kinds, labels
and notes (the tests check this for every example file and for every term
of the term printer's tests). Layout carries no meaning, so this is also
the normal form of a file:

```forth
leanforth-words
theorem composition  Prop implicit: A  Prop implicit: B  Prop implicit: C
  A B -> explicit: f  B C -> explicit: g  A C ->  :=  A explicit: value g f value $ $ fun
end composition
```

```text
theorem composition
  Prop implicit: A
  Prop implicit: B
  Prop implicit: C
  A B -> explicit: f
  B C -> explicit: g
  A C ->
:=
  A explicit: value g f value $ $ fun
end composition
```

## Mistakes point at your text

A missing `$`, a misspelt name or a Forth word stops at the word, with its
line and column, a stable error code and, where it helps, a second place:
for a body with two values instead of one, the place where its variable
was opened.

```forth
leanforth
theorem composition
  Prop implicit: A   Prop implicit: B   Prop implicit: C
  A B ->  explicit: f
  B C ->  explicit: g
  A C ->
:=
  A explicit: value   g f value $   fun
end composition
```

```text
error 12 at line:col 7:37 (token `fun`): the body of the binder must be exactly one term; see line:col 7:5
```

```forth
leanforth
theorem composition
  Prop implicit: A   Prop implicit: B   Prop implicit: C
  A B ->  explicit: f
  B C ->  explicit: g
  A C ->
:=
  A explicit: value   g f valeu $ $   fun
end composition
```

```text
error 1 at line:col 7:27 (token `valeu`): unknown name: no syntax word, bound variable, universe parameter or constant has it
```

Lean reports the second one as ``Unknown identifier `valeu` ``. Forth's
own words are unknown names too: `A dup` in a proof stops at `dup`.

## Limits today

- **Store sizes.** A run builds its terms in LeanForth's stores, which hold
  64 terms, 64 levels, 64 names and 32 constant references. While they are
  this small, equal subterms share one node (which keeps the position
  where it was first written); a step with a label or note always has a
  node of its own. A larger proof stops with an "out of room" error.
  Mathlib-scale stores are planned ([ADR 0016](../adr/0016-compact-store.md)).
- **Not supported yet** (each stops with a "not supported yet" error):
  natural-number and string literals, `let`/`have`, projections, holes
  `_`, tactic blocks `by`, `import`, and `_root_` in a declaration's name.
  Inductive types and structures are sketched in ADR 0017 only.
- **One line per word and name.** A word that reads a name, a note and a
  `( … )` comment must have it on the same line; lines are at most 1023
  characters in a file.
- **Where LeanForth is stricter than Lean.** Lean chooses between two
  constants a name could mean (from two open namespaces, or one open and
  the root) by their types; LeanForth has no types here and asks for the
  full name (error 27). A name Lean reads as a field of a variable or
  constant (`h.symm`) is an unknown name: projections are not supported
  yet. `_root_.x` is written `root: x`.
- **Printing.** In Lean notation an instance argument's name is shown in
  `fun [inst : C]` where Lean writes `fun [C]` when the printed body does
  not show the name (ADR 0017, example 8); the terms are the same. A Pi
  printed as `A B ->` comes back with the anonymous binder name, so a
  hygienic name there is not kept; Lean does not show such names either.

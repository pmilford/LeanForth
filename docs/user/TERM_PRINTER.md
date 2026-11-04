# Printing terms readably

LeanForth stores a term — a proposition, a proof, a type — as numbered nodes
with de Bruijn indices instead of variable names. The **term printer** turns
such a term back into text a person can read: in Lean's own notation, in
plain ASCII, or in LaTeX for rendered mathematics. It is the first piece of
the readable proofs the plan asks for (tasks 2.4.2 and 2.4.3 of
[the draft plan](../project/PLAN_DRAFT.md), §7); the [proof-outline printer](PROOF_OUTLINE.md)
that puts reasons between proof lines (2.4.4) builds on it.

**Trust.** The printer is presentation code. The checker never loads it,
and nothing it prints is evidence that anything was checked. A wrong or
missing binder name changes only the text. Until an outside Lean expert has
audited the checker, every accepted result is *experimental — not
independently audited*; the printer does not change that.

## What it prints

The same term in the three forms, for the theorem `composition` (the pinned
fixture `tests/reference/composition.lean`). The mathematics is the
printer's own LaTeX output:

```math
\forall \{A\ B\ C : \mathrm{Prop}\},\ (A \to B) \to (B \to C) \to A \to C
```

In words: for all propositions A, B and C, if A implies B and B implies C,
then A implies C. Lean writes the theorem, and prints it back with
`#print`, as

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

and LeanForth prints the checked declaration's statement and proof exactly
so (`tests/present/fixtures.golden`, compared with pinned Lean by
`make check`). In ASCII mode the same declaration is

```text
theorem composition : forall {A B C : Prop}, (A -> B) -> (B -> C) -> A -> C :=
fun {A B C} f g value => g (f value)
```

and in LaTeX the proof term is
`\lambda\ \{A\ B\ C\}\ f\ g\ \mathit{value} \mapsto g\ (f\ \mathit{value})`:

```math
\lambda\ \{A\ B\ C\}\ f\ g\ \mathit{value} \mapsto g\ (f\ \mathit{value})
```

In LeanForth Forth, a program prints a term with the words below. Terms
come from the importer, from LeanForth's own words for *writing* them
([LeanForth syntax](LEANFORTH_SYNTAX.md); the printer's Forth mode,
`src/present/print-forth.fs`, prints a term back as those words), or from
Forth words such as the test helpers in `tests/present/build.fs`, used
here. The examples on this page run after
`gforth src/main.fs` from the repository root, with these helpers loaded
first; `make test` checks that each prints exactly the text shown after it.

```forth
\ Helpers for the examples (documentation only): the printer's test words
\ of tests/present/build.fs, loaded from the repository root (~+ is
\ Gforth's name for the working directory). t-prop, t-var, t-pi and t-lam
\ build terms; ex. and im. name the newest binder, explicit or implicit;
\ nm, nm. and lparam make names and universe parameters.
require ~+/tests/present/build.fs
\ .result ( outcome -- ): end a printed line with the outcome's name.
: .result ( outcome -- )
  case outcome-ok of ."   (ok)" endof  outcome-exhausted of ."   (exhausted)" endof
    ."   (other)" endcase cr ;
```

The statement `∀ {P : Prop}, P → P` of the fixture identity, in the three
modes and as Markdown math; a universe level; two names; and a print that
runs out of fuel after part of the text:

```forth
fresh
t-prop  0 t-var 1 t-var t-pi s" proof" ex.  t-pi s" P" im.  constant statement
' type lf-print-unicode lf-print-setup   \ print to the terminal, in Lean's notation
statement 1000 lf-print-statement .result
' type lf-print-ascii lf-print-setup    statement 1000 lf-print-term .result
' type lf-print-latex lf-print-setup    statement 1000 lf-print-term .result
statement 1000 lf-print-inline .result   \ Markdown math, whatever the mode
' type lf-print-unicode lf-print-setup
s" u" lparam s" v" lparam lmax 1000 lf-print-level .result   \ a universe level
s" Nat" nm s" add" nm. lf-print-name .result                   \ a structured name
0 lf-print-name .result                                        \ the anonymous name
statement 10 lf-print-term .result       \ too little fuel: part of the text
```

```text
∀ {P : Prop}, P → P  (ok)
forall {P : Prop}, P -> P  (ok)
\forall \{P : \mathrm{Prop}\},\ P \to P  (ok)
$\forall \{P : \mathrm{Prop}\},\ P \to P$  (ok)
max u v  (ok)
Nat.add  (ok)
[anonymous]  (ok)
∀ {P : Prop}  (exhausted)
```

## Binder names without capture

A de Bruijn index says *which* binder a variable refers to, not its name.
The printer takes each binder's name from the presentation side table and
chooses the displayed name as Lean's delaborator does: it keeps the recorded
name unless that would make a variable refer to the wrong binder, and then
appends `_1`, `_2`, … (LaTeX shows them as subscripts).

| Term (binders named in the side table) | Printed | LaTeX |
| --- | --- | --- |
| λ x : Prop. λ x : Prop. (inner x) | `fun x x_1 ↦ x_1` | $\lambda\ x\ x_{1} \mapsto x_{1}$ |
| ∀ x : Prop. ∀ x : Prop. (outer x) | `∀ (x x_1 : Prop), x` | $\forall (x\ x_{1} : \mathrm{Prop}),\ x$ |
| ∀ x : Prop. ∀ x : Prop. (inner x) | `∀ (x x : Prop), x` | (the outer x is never used, so Lean keeps both names) |

A binder with no recorded name prints as `x`; Lean's anonymous name prints
as `a`, and a hygienic name such as `a._@._internal._hyg.0` prints as `a`,
as Lean prints them.

## Notation, as Lean prints it

- **Π types.** A proposition prints with `∀` and grouped binders
  (`∀ {A B C : Prop}, …`); a binder that the body does not use prints as an
  arrow `A → B`; a dependent type that is not a proposition prints as
  `{α : Sort u} → α → α`. Binders group when they have the same kind and
  the same type, as `{A B C : Prop}`. Kinds: `(x : A)` explicit, `{x : A}`
  implicit, `⦃x : A⦄` strict implicit (`{{x : A}}` in ASCII), `[h : A]`
  instance, or `[A]` when unused and hygienic.
- **Functions.** Consecutive λs print as one `fun` with explicit binders as
  bare names and implicit ones in braces: `fun {A B C} f g value ↦ …`.
- **Sorts and universes.** `Prop`, `Type`, `Type u` for `Sort (u + 1)`,
  `Sort u` otherwise; levels with `max`, `imax` and `u + 1`, flattened as
  Lean does: `Sort (max u v w)`, `Type ((max u v) + 1)`.
- **Constants** print by name, `My.name.space`; with the option
  `lf-print-universes` with universe arguments, `undeclaredL.{max u v, u + 1, 0}`.
  When the side table knows a constant's declared type, implicit arguments
  are hidden as Lean hides them: `fixtureId h`, not `@fixtureId P h`; when
  every argument must show, `@` comes first.
- **Parentheses** only where Lean's grammar needs them: `g (f value)`,
  `(A → B) → C`, `(fun x ↦ x) p`, and `g fun x ↦ x` when a `fun` is the last
  argument.

## The three modes and Markdown

| Mode (`lf-print-setup` option) | ∀ | → | λ | Prop | Identifiers |
| --- | --- | --- | --- | --- | --- |
| `lf-print-unicode` | `∀` | `→` | `fun x ↦ b` | `Prop` | as stored |
| `lf-print-ascii` | `forall` | `->` | `fun x => b` | `Prop` | as stored (UTF-8 letters such as α stay) |
| `lf-print-latex` | `\forall` | `\to` | `\lambda\ x \mapsto b` | `\mathrm{Prop}` | `x`, `\alpha`, `\mathit{value}`, `x_{1}`, `\mathsf{Nat.add}` |

LaTeX escapes `_ # % & { } $ ^ ~ \` in names, writes a trailing `_2` or `₂`
as the subscript `_{2}` and keeps primes. `lf-print-inline` and
`lf-print-display` wrap a term's LaTeX in `$…$` or `$$…$$` for Markdown;
GitHub renders those, and also fenced `math` blocks as used on this page.
Rendering on GitHub was not checked in the session that wrote the printer;
no LaTeX installation is used or needed by the tests.

## Interface (Forth)

The modules are in `src/present/`; load `src/present/term-printer.fs`.
Outcomes are the shared ones of `src/lib/outcome.fs`.

| Word | Stack effect | Does |
| --- | --- | --- |
| `lf-pres-binder!` | `( term name kind -- outcome )` | record a λ or Π node's binder name ID and kind (`lf-binder-default`, `-implicit`, `-strict`, `-instance`) |
| `lf-pres-source!` | `( term source -- outcome )` | record a node's source record ID (for example its NDJSON expression index) |
| `lf-pres-declare` | `( name type -- outcome )` | record a constant's declared type, so its implicit arguments can be hidden |
| `lf-pres-binder@`, `lf-pres-source@`, `lf-pres-type@` | read them back | false when absent or stale |
| `lf-pres-kind-text` | `( c-addr u -- kind true \| false )` | Lean's export spelling of a binder kind |
| `lf-pres-reset` | `( -- )` | forget every side-table entry and declaration |
| `lf-print-setup` | `( sink options -- )` | sink xt `( c-addr u -- )`, mode and option bits |
| `lf-print-term` | `( term fuel -- outcome )` | print a closed term |
| `lf-print-statement` | `( term fuel -- outcome )` | print a theorem's statement: its Π spine is a proposition |
| `lf-print-level` | `( level fuel -- outcome )` | print a universe level |
| `lf-print-name` | `( id -- outcome )` | print a structured name; the anonymous name 0 prints as `[anonymous]` (one unit of fuel) |
| `lf-print-inline`, `lf-print-display` | `( term fuel -- outcome )` | LaTeX between `$` or `$$` |
| `lf-print-scoped` | `( term addr count fuel -- outcome )` | print an open term in the scope of `count` λ or Π nodes at `addr`, outermost first, named as one `fun`'s binders (no repeats, no capture); for the proof outline |
| `lf-print-scope-name` | `( addr count fuel -- outcome )` | print the display name of the innermost of those binders |
| `lf-print-limit!` | `( n -- flag )` | at most n nested visits per print (default: no limit, the heap bounds a print); false for n < 1 or during a print |
| `lf-print-fuel` | `( -- addr )` | fuel left after the last print |
| `lf-print-reset` | `( -- )` | recover after a THROW out of a print: the printer is idle again, in the mode `lf-print-setup` set |

**Outcomes.** *ok*: printed. *invalid*: malformed input — a bad term
index, a bad level index, a stale constant reference, an unknown tag, a
variable outside the term's binders, a universe parameter that is not a
name, a corrupted name store, negative fuel — or a sink that tries to
print while a print is in progress, or that called `lf-print-reset` during
the print. *exhausted*: out of fuel. *full*: the heap has no room for the
print's work stack, its binders in scope or their names (the name pool,
which also holds the spelling of a LaTeX name; all three grow as a print
needs them), or out of nested visits when the caller set a limit with
`lf-print-limit!`. After a failure the sink has received part of the text.
Numbers print in decimal whatever `BASE` is, and `BASE` is kept.

**Sink rules.** The sink receives the text piece by piece:

- It uses the text, or copies it, before it returns and before any
  pictured numeric output (`<#` … `#>`) of its own: the text may lie in
  the printer's name pool or in the pictured numeric output buffer.
- It calls no `lf-print-*` or `lf-pres-*` word and changes no store
  (terms, levels, names, constant references). The printer refuses
  another print while one is in progress (invalid) and `lf-print-limit!`
  answers false; a print during which the sink called `lf-print-reset` goes
  on to its end and ends invalid, and the printer is then reset.
  `lf-print-inline` and `lf-print-display` write their `$`
  delimiters while no print is in progress, so a print the sink starts
  then is not refused; it runs before or after the term's own print and
  does not disturb it. A changed store is not detected: the text is then
  meaningless.
- It does not THROW. After a THROW out of a print, call `lf-print-reset`;
  it also ends the LaTeX mode that `lf-print-inline` and
  `lf-print-display` use, which never changes the options `lf-print-setup`
  set.

As defence in depth, every count the printer reads from its own state is
clamped into range, and a reset from the sink leaves the print's own work
stack whole, so a sink that breaks these rules cannot make a print loop
without end or address memory outside the printer's; the
sweep below resets the printer from the sink at every sink call of every
case to check this.

**Side table.** Every entry is stamped with its term's identity and the
name store's generation, so after a reset of either store it reads as
absent instead of describing another term. The coming Forth NDJSON reader
fills it as it decodes each record; tests fill it directly. It holds one
entry per term (64 today) and 32 declarations.

## Limits and differences from Lean

- **Propositions.** Lean decides whether a Π is a proposition (∀ or →) by
  type inference. The printer uses Lean's own quick test (`isPropQuick`):
  the body's head must be a variable whose type is arrows ending in `Prop`.
  Where that test cannot decide, Lean falls back to inferring the type,
  which the printer cannot do; it then prints a dependent arrow where Lean
  prints `∀`. Confirmed with pinned Lean 4.35.0; the printer's side is
  pinned by unit tests in `tests/present/term-printer.fs`:

  | Body | Lean prints | The printer prints |
  | --- | --- | --- |
  | headed by a `fun` applied to arguments | `∀ (x : Prop), (fun y ↦ y) x` | `(x : Prop) → (fun y ↦ y) x` |
  | a variable whose type unfolds to `Prop` (`def MyProp : Type := Prop`) | `∀ (p : MyProp), p` | `(p : MyProp) → p` |
  | headed by a constant (`def isP (_ : Prop) : Prop`) | `∀ (x : Prop), isP x` | `(x : Prop) → isP x` |

  `lf-print-statement` prints a theorem's statement with `∀` in all three
  cases. A `fun` applied to arguments is otherwise printed as Lean prints
  it: its own binders give the kinds of its parameters, so
  `fun p ↦ (fun {a} b ↦ b) p` hides the implicit argument (a case of the
  differential below).
- **Levels by index.** A `Sort` term refers to its level by index in the
  level store, with no generation stamp. After the level store is reset
  while terms are kept, such a `Sort` is invalid, or, once a new level has
  that index, prints the new level. Reset the term store with the level
  store (as `fresh` in the tests does).
- **Universe parameters are name IDs.** The printer prints a universe
  parameter by treating its parameter ID as a name ID of the name store,
  because `src/core/level-scope.fs` uses name IDs as parameter IDs. Each
  universe parameter must therefore be a valid name ID other than 0 (the
  anonymous name), or the print is invalid. This is a current coupling
  between the two modules, not a rule of Lean.
- **Implicit arguments** are hidden only for constants declared in the side
  table and for variables whose type is a Π; otherwise all arguments show,
  with `@` as Lean does when it cannot compute parameter kinds.
- **Not yet:** notation such as `a + b` or `a = b` (plan 4.4.3), `let`,
  literals, projections, line breaking (Lean breaks lines at 120 columns),
  and Lean's `«»` quoting of unusual names.
- **Cost and depth.** Fuel counts visited nodes; printing a chain of n
  binders costs on the order of n² fuel, because each Π re-examines the
  rest of the chain as Lean does. No depth is tied to the host's stacks
  or to a constant (plan task 6.2.0): every node is a visit on the print's
  own work stack, which grows on the heap, as do the binders in scope and
  their names. `tests/present/print-deep.fs` paints the host stacks
  (`tests/support/stack-paint.fs`) of the terms of
  `tests/reference/depth-terms.lean`, the lambda chain
  `fun P h.1 … h.n ↦ h.1` and the application chain
  `fun P h ↦ (fun x ↦ x) ((fun x ↦ x) (… h))`, of the application chain in
  the Forth mode, and of a level alternating `max` and `imax`: each uses
  the same cells at depths 31, 2,000 and 10,000, but for the lambda
  chain's three more where its arrays grow (painted on Gforth 1.0, below
  the caller's: 16 or 19, 14, 9 and 13 return-stack cells and at most 2
  data-stack cells; on 0.7.3 one cell fewer for the last two), as does the
  statement `∀ (P : Prop), P → … → P` at 31 and 2,000 (16). On the
  development machine the 10,000-deep lambda chain prints in about 1.3 s
  on Gforth 1.0 and 2.0 s on 0.7.3 (each new name is compared with every
  name in scope, as Lean's `getUnusedName` does: n² comparisons), the
  application chain in 73 and 248 ms; the 2,000-deep statement takes about
  1.5 and 3.1 s and 8 million units of fuel.

## Evidence

- `make test` runs `tests/present/term-printer.fs` (every public word's
  outcomes, sinks that break the rules, a non-decimal `BASE`, bad level
  indices, a corrupted name store, invalid UTF-8 in LaTeX names),
  `print-sweep.fs` (each of 50 cases in 3 modes at every fuel level below
  what it needs and at visit limits 1 to 24: 5,517 prints, each exhausted
  (fuel) or full (visit limit) or ok; then 1,891 prints whose sink calls
  `lf-print-reset` at each of its calls in turn, each invalid and leaving
  the printer idle; every print with both stacks balanced),
  `print-deep.fs` (the deep prints above, with their sizes and ends, and a
  print that the heap refuses room is full), `check_golden.py` (the text
  of all cases and of the five pinned
  fixtures, `print-cases.golden` and `fixtures.golden`) and the examples
  on this page. Also on Gforth 0.7.3.
- `make check` adds `test-printer-differential`: the 50 cases are built as
  Lean expressions in `tests/reference/printer-cases.lean` and printed by
  Lean; the five fixtures (identity, composition, type identity,
  polymorphic identity, constant fixture) are `#print`ed by Lean. Every
  Unicode line must equal LeanForth's, and every fixture declaration's
  ASCII statement and proof, given back to Lean as source, must elaborate
  against the original constant. This is finite evidence about these cases,
  not a proof that the printer is right.

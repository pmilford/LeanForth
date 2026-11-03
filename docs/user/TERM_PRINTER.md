# Printing terms readably

LeanForth stores a term — a proposition, a proof, a type — as numbered nodes
with de Bruijn indices instead of variable names. The **term printer** turns
such a term back into text a person can read: in Lean's own notation, in
plain ASCII, or in LaTeX for rendered mathematics. It is the first piece of
the readable proofs the plan asks for (tasks 2.4.2 and 2.4.3 of
[the draft plan](../project/PLAN_DRAFT.md), §7); the proof-outline printer
that puts reasons between proof lines (2.4.4) builds on it and does not
exist yet.

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
then A implies C. Lean writes the theorem as

```lean
theorem composition {A B C : Prop} (f : A → B) (g : B → C) : A → C :=
  fun value => g (f value)
```

and LeanForth prints the checked declaration's statement and proof exactly
as Lean's `#print` does (with `set_option pp.unicode.fun true`):

```text
theorem composition : ∀ {A B C : Prop}, (A → B) → (B → C) → A → C :=
fun {A B C} f g value ↦ g (f value)
```

In ASCII mode the same declaration is

```text
theorem composition : forall {A B C : Prop}, (A -> B) -> (B -> C) -> A -> C :=
fun {A B C} f g value => g (f value)
```

and in LaTeX the proof term is
`\lambda\ \{A\ B\ C\}\ f\ g\ \mathit{value} \mapsto g\ (f\ \mathit{value})`:

```math
\lambda\ \{A\ B\ C\}\ f\ g\ \mathit{value} \mapsto g\ (f\ \mathit{value})
```

In LeanForth Forth, a program prints a term with the words below. LeanForth's
own syntax for *writing* terms is not designed yet (plan task 8.1.1); today
terms come from the importer or from Forth words such as the test helpers in
`tests/present/build.fs`, used here:

```forth
\ ∀ {P : Prop}, P → P   — the statement of the fixture identity
t-prop  0 t-var 1 t-var t-pi s" proof" ex.  t-pi s" P" im.  constant statement
' type lf-print-unicode lf-print-setup     \ print to the terminal, Lean notation
statement 1000 lf-print-statement drop      \ prints ∀ {P : Prop}, P → P
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
| `lf-print-setup` | `( sink options -- )` | sink xt `( c-addr u -- )`, mode and option bits |
| `lf-print-term` | `( term fuel -- outcome )` | print a closed term |
| `lf-print-statement` | `( term fuel -- outcome )` | print a theorem's statement: its Π spine is a proposition |
| `lf-print-level` | `( level fuel -- outcome )` | print a universe level |
| `lf-print-name` | `( id -- outcome )` | print a structured name |
| `lf-print-inline`, `lf-print-display` | `( term fuel -- outcome )` | LaTeX between `$` or `$$` |
| `lf-print-limit!` | `( n -- flag )` | most nested visits per print (default 128) |
| `lf-print-fuel` | `( -- addr )` | fuel left after the last print |

**Outcomes.** *ok*: printed. *invalid*: malformed input — a bad term
index, a stale constant reference, an unknown tag, a variable outside the
term's binders, a universe parameter that is not a name, a corrupted name
store, negative fuel, or a sink that tries to print while a print is in
progress. *exhausted*: out of fuel. *full*: out of nested visits, or out
of room for binder names (4,096 bytes). After a failure the sink has received part
of the text. A sink must not THROW; after one, call `lf-print-reset`.

**Side table.** Every entry is stamped with its term's identity and the
name store's generation, so after a reset of either store it reads as
absent instead of describing another term. The coming Forth NDJSON reader
fills it as it decodes each record; tests fill it directly. It holds one
entry per term (64 today) and 32 declarations.

## Limits and differences from Lean

- **Propositions.** Lean decides whether a Π is a proposition (∀ or →) by
  type inference. The printer uses Lean's own quick test (`isPropQuick`):
  the body's head must be a variable whose type ends in `Prop`. For a body
  headed by a constant it cannot tell, and prints `(x : A) → c x` where Lean
  prints `∀ (x : A), c x`; `lf-print-statement` fixes this for a theorem's
  statement.
- **Implicit arguments** are hidden only for constants declared in the side
  table and for variables whose type is a Π; otherwise all arguments show,
  with `@` as Lean does when it cannot compute parameter kinds.
- **Not yet:** notation such as `a + b` or `a = b` (plan 4.4.3), `let`,
  literals, projections, line breaking (Lean breaks lines at 120 columns),
  and Lean's `«»` quoting of unusual names.
- **Cost.** Fuel counts visited nodes; printing a chain of n binders costs
  on the order of n² fuel, because each Π re-examines the rest of the chain
  as Lean does. At the deepest nesting tried (62 nested arrows, and the
  128-visit limit on a level tower) a print used at most 635 return-stack
  and 61 data-stack cells on Gforth 0.7.3 and 1.0.

## Evidence

- `make test` runs `tests/present/term-printer.fs` (every public word's
  outcomes), `print-sweep.fs` (each of 49 cases in 3 modes at every fuel
  level below what it needs and at visit limits 1 to 24: 5,409 prints, each
  exhausted (fuel) or full (visit limit) or ok, with the stack balanced) and `check_golden.py` (the text
  of all cases and of the five pinned fixtures, `print-cases.golden` and
  `fixtures.golden`). Also on Gforth 0.7.3.
- `make check` adds `test-printer-differential`: the 49 cases are built as
  Lean expressions in `tests/reference/printer-cases.lean` and printed by
  Lean; the five fixtures (identity, composition, type identity,
  polymorphic identity, constant fixture) are `#print`ed by Lean. Every
  Unicode line must equal LeanForth's, and every fixture declaration's
  ASCII statement and proof, given back to Lean as source, must elaborate
  against the original constant. This is finite evidence about these cases,
  not a proof that the printer is right.

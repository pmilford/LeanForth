# Checking a theorem with the first checker

**Status, 2026-11-02: experimental.** The first checker (plan task 2.2.3)
is [kernel] code that has not yet passed its review gate (`AGENTS.md`), and
no outside Lean expert has audited it. Every result it accepts is printed
*accepted (experimental, not independently audited)*, with the axioms the
result depends on. Do not rely on an accepted result until the owner has
approved the checker; until then, Lean's own kernel is the referee.

This page shows one real check from start to end: the `composition`
theorem, read from the file that Lean's exporter wrote, checked by
LeanForth and accepted; then a broken copy, rejected. The rules behind
each answer are in [ADR 0011](../adr/0011-definite-rejection.md); every
answer for 62 such cases, with Lean's own verdict beside it, is in the
[expected results](../reviews/FIRST_CHECKER_EXPECTED.md).

## What the first checker does

For each definition or theorem of its input, in order, it answers one of:

- **accepted** — every step succeeded, as Lean's kernel would take it;
- **rejected** — Lean's kernel certainly rejects it, for the reason named;
- **unknown** — deciding it needs a rule the first checker does not have
  yet (such as unfolding a definition), so it does not guess;
- **unsupported** — it uses something not built yet: axioms, `let`,
  numbers, data types, …;
- **invalid**, **exhausted**, **full** — malformed input, out of fuel, out
  of room.

Only *accepted* declarations can be used by later ones. The steps, in the
order Lean's kernel takes them: an audit (supported kinds and forms,
closed terms), the name, the universe parameters, the statement's type
(it must be a `Sort`, and for a theorem a proposition), the proof's type,
and finally that the proof's type is the statement.

## The example, in three forms

**Mathematics.** For all propositions *A*, *B*, *C*: if *A* implies *B*
and *B* implies *C*, then *A* implies *C*,

$$\forall A\, B\, C : \mathrm{Prop},\ (A \to B) \to (B \to C) \to A \to C,$$

proved by $\lambda f\, g\, a.\ g\,(f\,a)$: given $f : A \to B$,
$g : B \to C$ and a proof $a$ of $A$, the proof of $C$ is $g$ applied to
$f\,a$. It uses no axiom. Applying $g$ to $a$ itself would be a mistake:
$g$ needs a proof of $B$, and $a$ proves $A$.

**LeanForth Forth.** The pinned export `tests/reference/composition.ndjson`
is read with the test-only transport `tests/support/ndjson-input.fs`
(phase 3 replaces it with the real importer), which hands the declaration
to the checker; `ni-check` then checks every declaration of the file, with
fuel 100,000 each, and prints each verdict. Load the transport first:

```forth
[undefined] ni-check [if] require ~+/tests/support/ndjson-input.fs [then]
```

The export as Lean wrote it:

```forth
s" tests/reference/composition.ndjson" 100000 ni-check
```

```text
composition: accepted (experimental, not independently audited); axioms: none
```

A copy of the export with one number changed, so that the proof applies
`g` to `value` instead of to `f value`
(`tests/core/check-declaration-cases/composition-wrong-argument.ndjson`),
and the diagnostic that explains the verdict: rule D3 (diagnostic code 59,
whose first number is the set of rules used: 4 for D3) found the
argument's type `A` and the expected `B` to be different variables, which
Lean's kernel can never equate:

```forth
s" tests/core/check-declaration-cases/composition-wrong-argument.ndjson" 100000 ni-check
lf-diag. cr
```

```text
composition: rejected
rejected: argument type mismatch (D1-D5) at mixed-infer lf-mixed-infer: 4 0
```

**Lean.** Lean 4.35.0 accepts the theorem and lists its axioms (none):

```lean
theorem composition {A B C : Prop} (f : A → B) (g : B → C) : A → C :=
  fun value => g (f value)
#print axioms composition
```

```text
'composition' does not depend on any axioms
```

and rejects the broken copy for the same reason (its kernel's
`appTypeMismatch`; here Lean's front end finds it first):

```lean
theorem composition {A B C : Prop} (f : A → B) (g : B → C) : A → C :=
  fun value => g value
```

```text
error: Application type mismatch: The argument
  value
has type
  A
but is expected to have type
  B
in the application
  g value
```

## What this does and does not show

- The checked claim is the stored claim: the accepted record points at the
  very terms that were checked ([checked environment](../programming/CHECKED_ENVIRONMENT.md)).
- "axioms: none" is read from the accepted record, which joins the axiom
  sets of everything the declaration uses; in the first checker no axiom
  can be accepted, so every set is empty.
- The transport from the file is untrusted and test-only. It cannot make a
  wrong proof right; it could only hand over a different claim. Nothing
  here prints the checked statement for a person to compare yet (plan task
  2.4.4); the 62 table cases are built from the very terms Lean checks.
- The first checker covers `Sort`s, variables, application, `fun`, `∀` and
  earlier accepted declarations. It does not unfold definitions, so some
  correct proofs are *unknown*; theorems that use data types, numbers or
  axioms are *unsupported* until later phases.
- Limits today: 64 term nodes, 64 levels and 64 names per input, 32
  declarations, 16 dependencies per declaration.

## When a check runs out of fuel or room

A check that runs out of its budget of steps ends *exhausted*; one that
runs out of memory for the terms or levels it builds ends *full* (or
*unknown*, when that happens while it looks for a reason to reject); one
that hits an internal error ends *invalid*. None of these is ever
accepted, and the declaration's work is thrown away: the library of
accepted declarations is exactly as it would be had the declaration
failed for any other reason, so a later declaration that uses it is
*unknown*, never accepted. The test suite `tests/core/failure-paths.fs`
checks this for the fixtures above by making each memory allocation of
each check fail in turn, by giving each check every amount of fuel from
none upward, and by raising an internal error at each allocation
([testing strategy](../development/TESTING_STRATEGY.md)).

`python3 scripts/check-doc-examples.py --gforth GFORTH --lean LEAN
docs/user/FIRST_CHECK.md` runs these examples and compares the output
(`make test` runs its Forth, `make check` its Lean; done on 2026-11-02
with Gforth 1.0 and 0.7.3 and pinned Lean 4.35.0).

## See also

- [Running the checks](RUNNING_THE_CHECKS.md): the `make` targets.
- [Concepts](CONCEPTS.md): theorem, definition, kernel and the outcomes.
- [Diagnostics](../programming/DIAGNOSTICS.md): every code a failure records.

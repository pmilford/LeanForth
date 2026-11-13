# Checking a theorem with the first checker

The checker (first built as plan task 2.2.3) is [kernel] code that has
not yet passed its review gate (`AGENTS.md`). Every result it accepts is
printed *accepted*, with the axioms the result depends on. Until the
owner has approved the checker, Lean's own kernel is the referee. What it
checks is a proof that Lean produced and exported; LeanForth text is checked by
`leanforth check FILE.lf` since 2026-11-12 ([checking a file](LEANFORTH_SYNTAX.md#checking-a-file)),
but nothing on this page is LeanForth input.

This page shows one real check from start to end: the `composition`
theorem, read from the file that Lean's exporter wrote, checked by
LeanForth and accepted; then a broken copy, rejected. The rules behind
each answer are in [ADR 0011](../adr/0011-definite-rejection.md); every
answer for 69 such cases, with Lean's own verdict beside it, is in the
[expected results](../reviews/FIRST_CHECKER_EXPECTED.md).

## What the first checker does

For each definition or theorem of its input, in order, it answers one of:

- **accepted** — every step succeeded, as Lean's kernel would take it.
  Until 2026-11-03 this was not always true for universe levels: LeanForth
  accepted a few declarations whose levels have equal values but which
  Lean's level comparison rejects; it now builds and compares levels
  exactly as Lean does ([ADR 0011, Amendment 1](../adr/0011-definite-rejection.md#amendment-1-proposed-2026-11-03-universe-levels-are-built-and-compared-as-lean-builds-and-compares-them));
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

**The checking run in Forth** (the proof is Lean's, not LeanForth text). The pinned export `tests/reference/composition.ndjson`
is staged by the importer stage (`src/import/stage.fs`), which checks it
against its manifest, and fed to the checker (`src/import/feed.fs`);
`cli-check`, the word behind [the command line](COMMAND_LINE.md)'s
`bin/leanforth check`, then checks every declaration of the file, with
fuel 100,000,000 each, prints each verdict and a summary, and leaves the exit
code (0: every declaration accepted). `cli-options` sets those defaults:

```forth
cli-options
```

The export as Lean wrote it:

```forth
s" tests/reference/composition.ndjson" cli-check .
```

```text
composition: accepted; axioms: none
1 declaration: 1 accepted
accepted: 1; axioms: none
0
```

A copy of the export with one number changed, so that the proof applies
`g` to `value` instead of to `f value`
(`tests/core/check-declaration-cases/composition-wrong-argument.ndjson`;
it has no manifest, so `cli-no-manifest` reads it without one). The
indented line is the diagnostic that explains the verdict: Lean's
definitional equality, as LeanForth ports it, says the argument's type
`A` and the expected `B` are not equal -- two different variables that
Lean's kernel can never equate (diagnostic code 59, an argument's type
mismatch; until plan task 4.2.2d ADR 0011's rule D3 found it, and the
first number was the set of rules used); the exit code is 1, rejected:

```forth
cli-no-manifest
s" tests/core/check-declaration-cases/composition-wrong-argument.ndjson" cli-check .
```

```text
note: the export's manifest is not checked (--no-manifest)
composition: rejected
  rejected: argument type mismatch (D1-D5); diagnostic 59 at mixed-infer lf-mixed-infer: 0 0
1 declaration: 1 rejected
1
```

From a shell, `bin/leanforth check tests/reference/composition.ndjson`
prints the same lines and exits with that code
([the command line](COMMAND_LINE.md)).

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
  sets of everything the declaration uses; the cases on this page use no
  axiom, so their sets are empty (an axiom outside Lean's standard three is
  reported NOT PROVED).
- Reading and staging the file (`src/import/ndjson.fs`, `checker-input.fs`) are
  untrusted. They cannot make a wrong proof right; they could only hand
  over a different claim. This page does not show the checked statement;
  `leanforth print` prints it for a person to compare (plan tasks 4.4.3,
  2.4.4); the 69 table cases are built
  from the very terms Lean checks.
- The first checker covers `Sort`s, variables, application, `fun`, `∀` and
  earlier accepted declarations. Where Lean's kernel needs a type to be a
  `Sort` or a function type, it computes the type's weak head normal form
  as Lean does, unfolding definitions and theorems (never opaque
  declarations) since plan task 4.2.2c: with `def dqProp : Type := Prop`,
  `theorem t (A : dqProp) (h : A) : A := h` is accepted, as by Lean, and
  it unfolds definitions to compare two terms as Lean's lazy delta
  reduction does (since plan task 4.2.2d). Proof irrelevance and function eta
  (plan tasks 4.2.5, 4.2.4), `let`, literals, projections, quotients and
  inductive types are built too; they are merged and approved. A few constructs can still end *unknown* or
  *unsupported* (see `bin/leanforth capabilities`).
- Limits today: `bin/leanforth check` holds exports of any size (all of
  Lean's `Init`; the stores grow), with no fixed limit on how deep a term
  nests or how many constants a declaration uses (memory only; each
  check's scratch grows too); `check --record`, `replay` and
  `print` hold 64 term nodes, 64 levels and 64 names per input and 32
  declarations ([the command line](COMMAND_LINE.md)).

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

## Keeping the evidence, and checking it again

A check can leave a *run record*: a JSON file that says which file was
checked (its SHA-256, size and whether its manifest matched), which Lean
and exporter versions wrote it, which LeanForth commit and Forth system
checked it, with which fuel and limits, and the verdict of every
declaration, read from the library of accepted declarations after the
check. *Replay* checks the same file again and compares the new record
with the old one, field by field; any difference, in a verdict, the file,
a tool or a setting, is reported with a code and the field's name, never
passed over. Both run in Forth alone, from the command line (which
checks the manifest too, [the command line](COMMAND_LINE.md#run-records-and-replay))
or through `make` (which does not):

```sh
bin/leanforth check --record composition.json tests/reference/composition.ndjson
bin/leanforth replay tests/reference/composition.ndjson composition.json
make run-record EXPORT=tests/reference/composition.ndjson RECORD=composition.json
make replay EXPORT=tests/reference/composition.ndjson RECORD=composition.json
```

The second prints `"result":"confirmed"` and exits with status 0 when the
record holds; otherwise `"result":"refused"` with the findings, such as
`{"code":"verdict-differs","path":"$.declarations[0].verdict"}`. The part
of the record that holds the verdicts, written by the same words:

```forth
require ~+/tests/support/run-records.fs
s" tests/reference/composition.ndjson" 100000 ni-run drop
rr-text s\" \"declarations\":[" search drop type cr
```

```text
"declarations":[{"index":0,"name":"composition","verdict":"accepted","axioms":[]}]}
```

A record is evidence, not an approval: it says what the checker
established, accepted only where the library holds the declaration, with
its label and its axioms. The fields, the replay codes and the limits are
in [run records](../programming/RUN_RECORDS.md).

## See also

- [Running the checks](RUNNING_THE_CHECKS.md): the `make` targets.
- [Run records](../programming/RUN_RECORDS.md): the evidence of a check, and its replay.
- [Concepts](CONCEPTS.md): theorem, definition, kernel and the outcomes.
- [Diagnostics](../programming/DIAGNOSTICS.md): every code a failure records.

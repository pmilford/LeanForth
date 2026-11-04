# Readable proofs: the proof outline

When LeanForth checks a declaration it can keep a notebook of every small
rule it applies, the [derivation log](../programming/DERIVATION_LOG.md).
The **proof outline** turns that notebook into a short proof a person can
read, in which every line names the checker steps behind it. This page
shows the outline of the theorem `composition` in three forms
(mathematics, LeanForth's own words, and Lean), how to print one, and what
in it is checked and what is only explanation.

Words used here: a *proposition* is a statement that can be true or false;
a *proof* of `A → B` is a function that turns any proof of `A` into a proof
of `B`; the *kernel* is the part of LeanForth that checks proofs (see
[terms for new readers](TERMS_FOR_NEW_READERS.md) and
[concepts](CONCEPTS.md)).

**Status.** Implemented (plan tasks 2.4.1 and 2.4.4; [ADR 0013](../adr/0013-derivation-log.md)).
The checker itself is experimental and not independently audited, so is
every accepted result; the outline is untrusted presentation: it cannot
change a verdict, and its sentences are not checked reasoning.

## The theorem in three forms

**Mathematics.** For all propositions A, B and C: if A implies B, and B
implies C, then A implies C.

```math
\forall \{A\ B\ C : \mathrm{Prop}\},\ (A \to B) \to (B \to C) \to A \to C
```

The proof is a function: given a proof `f` of `A → B`, a proof `g` of
`B → C` and a proof `value` of `A`, the proof of `C` is `g (f value)`.

**LeanForth words** ([LeanForth syntax](LEANFORTH_SYNTAX.md); the file
`tests/author/02-composition.lf`, which `make test` checks against Lean's
own term):

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

**Lean** (the pinned fixture `tests/reference/composition.lean`, checked
with Lean 4.35.0 by `make check`):

```lean
theorem composition {A B C : Prop} (f : A → B) (g : B → C) : A → C :=
  fun value => g (f value)

#print axioms composition
```

```text
'composition' does not depend on any axioms
```

## The outline

LeanForth reads Lean's export of the fixture, checks it with the log on,
and prints:

```forth
\ The print driver for exports (tests/support/print-outline.fs), loaded
\ from the repository root (~+ is Gforth's name for the working directory).
require ~+/tests/support/print-outline.fs
```

```forth
s" tests/reference/composition.ndjson" false po-file
```

```text
Theorem composition
  accepted (experimental, not independently audited); axioms: none
  Statement: ∀ {A B C : Prop}, (A → B) → (B → C) → A → C
  Input:     tests/reference/composition.ndjson line 35
  Checker log: 65 steps, complete. The statement is a proposition: s26 (from s3).

Proof (reconstructed from the proof term).
  1  Let A, B, C be propositions.                  [∀-introduction]                   s27–s29
  2  Assume f : A → B.                             [assumption]                       s34
  3  Assume g : B → C.                             [assumption]                       s39
  4  Assume value : A.                             [assumption]                       s41
  5    Then f value : B,                           [→-elimination ← 2, 4]             s50
         because f turns any proof of A into a proof of B.
  6    Then g (f value) : C,                       [→-elimination ← 3, 5]             s53
         because g turns any proof of B into a proof of C.
  7  Discharging 4, 3, 2 and 1 gives               [→/∀-introduction ← 1, 2, 3, 4, 6] s54–s59
       ∀ {A B C : Prop}, (A → B) → (B → C) → A → C.
  8  This is the statement.                        [definitional equality ← 7]        s63
∎
Rules, formulas and step numbers come from the checker's log; the sentences are
fixed templates (structured-template), not checked reasoning.
Templates: let-props/v0, assume/v0, implies-elim/v0, discharge/v0, statement/v0.
```

How to read it:

- Each line has a number, a sentence, the rule in brackets with the
  earlier lines it uses after `←`, and the checker steps it covers
  (`s27–s29` is steps 27 to 29 of the log; `s26 (from s3)` is a step and
  the first step of its sub-derivation).
- Lines 1–4 bring the binders of the proof into scope: `A`, `B` and `C`
  range over propositions; `f`, `g` and `value` are assumptions, because
  their types are propositions.
- Lines 5 and 6 apply a proof of an implication to a proof of its
  premise; they are indented because they lie under those assumptions.
- Line 7 discharges the assumptions: the function as a whole proves the
  implication, and its type is the formula on the next line. Line 8 says
  that this is exactly the statement (the checker compared the two).

The same outline as a table, in mathematical notation (written by hand from
the lines above; the printer's LaTeX mode is plan task 8.6.1):

| # | Line | Rule | Uses | Checker steps |
| ---: | --- | --- | --- | --- |
| 1 | Let $A, B, C$ be propositions. | ∀-introduction | | s27–s29 |
| 2 | Assume $f : A \to B$. | assumption | | s34 |
| 3 | Assume $g : B \to C$. | assumption | | s39 |
| 4 | Assume $\mathit{value} : A$. | assumption | | s41 |
| 5 | Then $f\ \mathit{value} : B$, because $f$ turns any proof of $A$ into a proof of $B$. | →-elimination | 2, 4 | s50 |
| 6 | Then $g\ (f\ \mathit{value}) : C$, because $g$ turns any proof of $B$ into a proof of $C$. | →-elimination | 3, 5 | s53 |
| 7 | Discharging 4, 3, 2 and 1 gives $\forall \{A\ B\ C : \mathrm{Prop}\},\ (A \to B) \to (B \to C) \to A \to C$. | →/∀-introduction | 1, 2, 3, 4, 6 | s54–s59 |
| 8 | This is the statement. | definitional equality | 7 | s63 |

## Printing an outline

From the repository root, for any Lean export the checker's input reader
(`src/import/checker-input.fs`) holds (64 names, levels and term nodes,
32 declarations):

```text
make print EXPORT=tests/reference/composition.ndjson            # the outlines
make print EXPORT=tests/reference/composition.ndjson DETAIL=1   # every step
```

or, in Forth, after `require ~+/tests/support/print-outline.fs`:
`s" FILE" false po-file` (outlines) or `s" FILE" true po-file` (every
step). Each declaration of the file is checked in turn with the log at
level `terms`, and printed after its check. `--detail` (`DETAIL=1`) lists
all 65 steps of `composition` instead, for example

```text
  s49    instantiate         depth 6   (fun x ↦ B) value ⟶ B
  s50    application         depth 6   f value : B  ← s45, s47, s48, s49
```

(the full list is in [`tests/present/outlines.golden`](../../tests/present/outlines.golden)).
`leanforth print FILE` will replace `make print` when the command line
lands (plan task 3.4).

**When there is no outline.** The printer prints the verdict and says why
instead:

- the declaration was not accepted: `No proof outline: the declaration was
  not accepted.` (with `--detail`, the steps end with the rules that
  failed, each marked with its outcome, such as `[rejected]`);
- the log ran out of room: `Proof outline not available: the checker's log
  was truncated at step 31 (records); the verdict is unaffected.` (owner
  decision D2: never an outline from an incomplete log);
- the log was kept without formulas (level `steps`);
- no template covers the proof: its steps are listed.

## What is checked, and what is only explanation

- **From the checker** (experimental, not independently audited): the
  verdict, its label and the axioms, read from the checked environment;
  every formula on every line, which is a term the checker computed for
  that step (an input term, or the copy the log kept of a term the checker
  built), printed by the [term printer](TERM_PRINTER.md); the rules, the
  step numbers, and which steps each step used.
- **Only explanation** (tagged `structured-template`, each template named
  in the footer with a version): every English sentence ("Let", "Assume",
  "because …", "Discharging", "by applying"), how steps are grouped into
  lines, the line numbers and which lines a line "uses", the indentation,
  the choice of names. A badly worded template could mislead a reader; it
  cannot change a verdict.
- A Lean export holds the proof term, not its author's reasoning, so an
  outline of an imported proof is always *reconstructed from the proof
  term*, and says so.
- The log never changes an answer: every test of LeanForth passes the same
  with the log off, on, and full at every step
  ([evidence](../programming/DERIVATION_LOG.md#evidence-that-nothing-changed)).

## Limits

- Recognised: chains of `fun` binders (over propositions, types, or
  elements of a type; assumptions), applications of a variable, a
  constant or an application, variables and constants. Anything else (a
  value that is a `Sort` or a Π, a `fun` applied directly) prints its
  steps instead. Phase 4 (definitions that compute) adds "by definition
  of" lines for unfolding.
- Unicode text only; Markdown, LaTeX and JSON outputs are later printer
  modes (plan tasks 2.4.4 and 8.6.1).
- The input is the checker's input reader of today (small exports only);
  formulas print from the context that ran the check, between checks.

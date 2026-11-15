# Readable proofs: what a checked proof will look like

> **Superseded: the printer is implemented.** See
> [the proof outline](../../user/PROOF_OUTLINE.md) for what it prints today, checked
> by `make test`. This page is the design sketch it was built from (plan
> task 2.4.4, [ADR 0013](../../adr/0013-derivation-log.md)); its mock-ups
> differ from the output in details. The Lean examples were checked
> by hand with the pinned Lean 4.35.0; the Forth on this page is
> illustrative.

## The idea in two sentences

While LeanForth checks a proof, it can keep a *derivation log*: one
numbered line for every small rule it applies ("this variable has that
type", "applying `f` to `value` gives a proof of `B`"). The proof-outline
printer turns that log into a short proof a person can read, in which every
line names the checker steps behind it.

Words used here: a *proposition* is a statement that can be true or false;
a *proof* of `A → B` is a function that turns any proof of `A` into a proof
of `B`; the *kernel* is the part of LeanForth that checks proofs (see
[terms for new readers](../../user/TERMS_FOR_NEW_READERS.md) and
[concepts](../../user/CONCEPTS.md)).

## The example: `composition`

The theorem says that implication chains: if `A` implies `B` and `B`
implies `C`, then `A` implies `C`. It is one of the pinned test fixtures
(`tests/reference/composition.lean`), so Lean's own export of it is the
input LeanForth checks. In a terminal, the printer would show:

```text
Theorem composition
  accepted; axioms: none
  Statement: ∀ {A B C : Prop}, (A → B) → (B → C) → A → C
  In words:  for all propositions A, B, C: if A implies B, and B implies C, then A implies C.
  Input:     tests/reference/composition.ndjson line 35
             sha256 7778d2ef5da2f0935fb0180c953afa9371843f4ceec2660122f8c792b9ca2fec
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
Rules and step numbers come from the checker's log. The sentences are fixed
templates (structured-template), not checked reasoning.
```

`← 2, 4` means the line uses lines 2 and 4; `s50` names a line of the
checker's log. With `--detail` the printer would list all 65 checker steps
instead (they are listed in
[ADR 0013](../../adr/0013-derivation-log.md#the-log-level-terms-65-steps)).
A JSON form for programs and AI tools carries the same lines with the
checker's step numbers and the input's line numbers.

## The same proof in three forms

### Mathematics

The statement:

```math
\forall \{A\ B\ C : \mathrm{Prop}\},\ (A \to B) \to (B \to C) \to A \to C
```

In words: for all propositions A, B, C: if A implies B, and B implies C,
then A implies C. The outline, as the printer would render it in Markdown:

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

The same proof as a natural-deduction tree; an assumption in brackets with
a number is discharged at the rule marked with that number:

```math
\dfrac{\dfrac{[g : B \to C]^{3} \quad \dfrac{[f : A \to B]^{2} \quad [\mathit{value} : A]^{4}}{f\ \mathit{value} : B}\ {\to}\mathrm{E}}{g\ (f\ \mathit{value}) : C}\ {\to}\mathrm{E}}{\forall \{A\ B\ C : \mathrm{Prop}\},\ (A \to B) \to (B \to C) \to A \to C}\ {\to}\mathrm{I}^{4,3,2},\ \forall\mathrm{I}^{1}
```

(How GitHub renders these formulas has not been checked.)

### LeanForth Forth

How theorems are *written* in LeanForth is still to be designed (plan task
8.1.1); the owner decided that they are ordinary Forth words, not strings
that are parsed. This sketch shows the proof that way, each line of the
outline as a comment beside the words it describes. It is illustrative:
none of these words exists.

```text
theorem composition
  Prop implicit: A   Prop implicit: B   Prop implicit: C   \ 1 Let A, B, C be propositions.
  A B arrow explicit: f                                    \ 2 Assume f : A → B.
  B C arrow explicit: g                                    \ 3 Assume g : B → C.
  A C arrow statement
  A fun: value                                             \ 4 Assume value : A.
    g  f value apply                                       \ 5 Then f value : B.
    apply                                                  \ 6 Then g (f value) : C.
  end-fun proof                                            \ 7 Discharging 4, 3, 2 and 1,
end-theorem                                                \ 8 which is the statement.
```

Forth builds the proof term on the stack: `f value apply` leaves `f value`,
and the second `apply` applies the `g` left below it. Printing the outline
would take two proposed settings before a run (ADR 0013): keep every step
with its formulas, and print each accepted declaration's outline after it
is checked.

```text
lf-log-terms lf-log-level!          \ proposed: log every step, keeping its formulas
' lf-outline-text lf-log-observer!  \ proposed: print the outline after each declaration
```

### Lean

The fixture, as Lean checks it, and its axioms:

```lean
theorem composition {A B C : Prop} (f : A → B) (g : B → C) : A → C :=
  fun value => g (f value)

#print axioms composition
```

```text
'composition' does not depend on any axioms
```

The same reasoning written step by step, one tactic per line of the
outline. Lean builds a slightly different proof term from it (each `have`
adds a step), so LeanForth's outline describes the fixture above, not this
version:

```lean
theorem composition {A B C : Prop} (f : A → B) (g : B → C) : A → C := by
  intro value              -- line 4: assume value : A
  have hB : B := f value   -- line 5: then f value : B
  have hC : C := g hB      -- line 6: then g (f value) : C
  exact hC                 -- line 7: discharging value gives A → C
```

Both Lean blocks were checked with the pinned Lean 4.35.0 and
`-DwarningAsError=true` on 2026-11-02; this page is not yet part of
`make check`.

## What is checked, and what is only explanation

- **Checked by LeanForth** (once the checker exists and has passed its
  review): each formula on a line is exactly the one the checker computed
  for that step; the rule names and step numbers come from the checker's
  log; so do which lines a line uses, the final match with the statement,
  the verdict and the list of axioms.
- **Only explanation**: the English sentences ("Let", "Assume",
  "because …", "Discharging", the statement in words), how steps are
  grouped into lines, the line numbers, the names and notation. They come
  from fixed templates and are tagged `structured-template`. A badly worded
  template could mislead a reader, but it cannot change a verdict.
- A Lean export contains the proof term, not its author's reasoning, so an
  outline of an imported proof is always *reconstructed from the proof
  term*, and says so.
- The log never changes an answer. If it runs out of room it stops, the
  printer says "proof outline not available: the checker's log was
  truncated", and the verdict stands.

## Where this comes from

The plan's mock-ups ([§7 of the plan](../../project/PLAN_DRAFT.md#7-readable-proofs-what-the-output-could-look-like)),
the proof-step format of [the interface contracts](../../programming/INTERFACE_CONTRACTS.md),
the [term printer](../../user/TERM_PRINTER.md) that prints each formula, and
[ADR 0013](../../adr/0013-derivation-log.md), the proposed design with its
open questions for the owner.

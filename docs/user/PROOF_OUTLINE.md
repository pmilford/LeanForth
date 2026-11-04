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
  Statement in Lean:        ∀ {A B C : Prop}, (A → B) → (B → C) → A → C
  Statement in mathematics: $\forall \{A\ B\ C : \mathrm{Prop}\},\ (A \to B) \to (B \to C) \to A \to C$
  Statement in LeanForth (as an axiom states a type; this assumes nothing):
    axiom composition
      Prop implicit: A
      Prop implicit: B
      Prop implicit: C
      A B -> explicit: f
      B C -> explicit: g
      A C ->
    end composition
  Input:     tests/reference/composition.ndjson line 35
  Checker log: 51 steps, complete. The statement is a proposition: s20 (from s3).

Proof (reconstructed from the proof term).
  1  Let A, B, C be propositions.                  [∀-introduction]                   s21–s23
  2  Assume f : A → B.                             [assumption]                       s26
  3  Assume g : B → C.                             [assumption]                       s29
  4  Assume value : A.                             [assumption]                       s30
  5    Then f value : B,                           [→-elimination ← 2, 4]             s36
         because f turns any proof of A into a proof of B.
  6    Then g (f value) : C,                       [→-elimination ← 3, 5]             s39
         because g turns any proof of B into a proof of C.
  7  Discharging 4, 3, 2 and 1 gives               [→/∀-introduction ← 1, 2, 3, 4, 6] s40–s45
       ∀ {A B C : Prop}, (A → B) → (B → C) → A → C.
  8  This is the statement.                        [definitional equality ← 7]        s49
∎
Rules, formulas and step numbers come from the checker's log; the sentences are
fixed templates (structured-template), not checked reasoning.
Templates: let-props/v0, assume/v0, implies-elim/v0, discharge/v0, statement/v0.
```

How to read it:

- The header gives the statement three times, because readers differ: in
  Lean's notation, in mathematics (LaTeX between `$` and `$`, for a
  Markdown viewer or a paper) and in LeanForth words. The LeanForth block
  states the type the way an `axiom` of the same name does, the one form
  of the words that states a type without a proof; it assumes nothing, and
  running it with the [authoring words](../programming/LEANFORTH_WORDS.md)
  builds exactly the statement term (`make test` checks this for every
  example on this page). `leanforth print --statement lean,leanforth`
  chooses which forms to print.
- Each line has a number, a sentence, the rule in brackets with the
  earlier lines it uses after `←`, and the checker steps it covers
  (`s21–s23` is steps 21 to 23 of the log; `s20 (from s3)` is a step and
  the first step of its sub-derivation).
- Lines 1–4 bring the binders of the proof into scope: `A`, `B` and `C`
  range over propositions; `f`, `g` and `value` are assumptions, because
  their types are propositions.
- Lines 5 and 6 apply a proof of an implication to a proof of its
  premise; they are indented because they lie under those assumptions.
- Line 7 discharges the assumptions: the function as a whole proves the
  implication, and its type is the formula on the next line. Line 8 says
  that this is exactly the statement (the checker compared the two).

The same outline as a table, in mathematical notation (the printer's LaTeX
style, [below](#latex), writes such a table):

| # | Line | Rule | Uses | Checker steps |
| ---: | --- | --- | --- | --- |
| 1 | Let $A, B, C$ be propositions. | ∀-introduction | | s21–s23 |
| 2 | Assume $f : A \to B$. | assumption | | s26 |
| 3 | Assume $g : B \to C$. | assumption | | s29 |
| 4 | Assume $\mathit{value} : A$. | assumption | | s30 |
| 5 | Then $f\ \mathit{value} : B$, because $f$ turns any proof of $A$ into a proof of $B$. | →-elimination | 2, 4 | s36 |
| 6 | Then $g\ (f\ \mathit{value}) : C$, because $g$ turns any proof of $B$ into a proof of $C$. | →-elimination | 3, 5 | s39 |
| 7 | Discharging 4, 3, 2 and 1 gives $\forall \{A\ B\ C : \mathrm{Prop}\},\ (A \to B) \to (B \to C) \to A \to C$. | →/∀-introduction | 1, 2, 3, 4, 6 | s40–s45 |
| 8 | This is the statement. | definitional equality | 7 | s49 |

## Printing an outline

With the [command line](COMMAND_LINE.md#printing-a-readable-proof), from
the repository root, for any Lean export `check` takes (the export is
staged and fed to the checker as `check` does it, so there is no size limit
of the printer; `--name` prints one declaration of a library, for example
`Eq.symm` of Lean's `Init`):

```text
bin/leanforth print tests/reference/composition.ndjson                 # the outlines
bin/leanforth print --detail tests/reference/composition.ndjson        # every step
bin/leanforth print --name fixtureUse tests/reference/constant-fixture.ndjson
bin/leanforth print --name Eq.symm init.ndjson     # Lean's Init, 345.7 MB (a few minutes)
bin/leanforth print --latex tests/reference/composition.ndjson        # LaTeX fragments
bin/leanforth print --statement lean,leanforth tests/reference/composition.ndjson
```

The outline of `Eq.symm` from Lean's own `Init` library, as the command
above printed it on 2026-11-04 (accepted by LeanForth: the statement in
Lean's notation, the LeanForth words with its universe parameter, and the
steps of its proof term; a long formula runs past its column):

```text
Theorem Eq.symm
  accepted (experimental, not independently audited); axioms: none
  Statement in Lean:        ∀ {α : Sort u} {a b : α} (h : Eq a b), Eq b a
  Statement in mathematics: $\forall \{\alpha : \mathrm{Sort}\ u\}\ \{a\ b : \alpha\}\ (h : \mathsf{Eq}\ a\ b),\ \mathsf{Eq}\ b\ a$
  Statement in LeanForth (as an axiom states a type; this assumes nothing):
    axiom Eq.symm
      universe u
      u Sort implicit: α
      α implicit: a
      α implicit: b
      Eq u ^ α $ a $ b $ explicit: h
      Eq u ^ α $ b $ a $
    end Eq.symm
  Input:     init.ndjson line 4005
  Checker log: 174 steps, complete. The statement is a proposition: s47 (from s3).
```

`make print EXPORT=FILE [DETAIL=1] [NAME=NAME]` runs the same, and in
Forth, after `require ~+/tests/support/print-outline.fs`,
`s" FILE" false po-file` (outlines) or `s" FILE" true po-file` (every
step). Each declaration of the file is checked in turn with the log at
level `terms`, and printed after its check; the exit status is `check`'s
for a declaration refused, 3 for a log that ran out of room
([details](COMMAND_LINE.md#printing-a-readable-proof)). `--detail` lists
all 51 steps of `composition` instead, for example

```text
  s35    instantiate         depth 6   (fun x ↦ B) value ⟶ B
  s36    application         depth 6   f value : B  ← s32, s33, s34, s35
```

(the full list is in [`tests/present/outlines.golden`](../../tests/present/outlines.golden)).

**When there is no outline.** The printer prints the verdict and says why
instead:

- the declaration was not accepted: `No proof outline: the declaration was
  not accepted.` (with `--detail`, the steps end with the rules that
  failed, each marked with its outcome, such as `[rejected]`);
- the log ran out of room: `No proof outline: the declaration is
  accepted, but the checker's log was truncated at step 31 (records); the
  verdict is unaffected.` (owner decision D2: never an outline from an
  incomplete log);
- the log was kept without formulas (level `steps`);
- no template covers the proof: its steps are listed.

The printer does not take the verdict it is given on trust. Unless the
log is the one that verdict belongs to — taken over this very input, which
is still intact, by the check of this declaration, which published that
outcome — it prints only `No outline: the checker's log does not belong to
this declaration's published verdict, or the input changed since the
check.` (`leanforth print` always pairs them correctly; this guards other
callers of the Forth words.) Nor does it print anything from a log that
fails the log's structural check (`src/present/log-check.fs`): it says
`No outline: the checker's log fails its structural check (part N);
nothing is printed from it.`

## LaTeX

`leanforth print --latex FILE` (in Forth, `true lf-outline-latex!` before
printing) writes each outline as a LaTeX fragment (plan task 8.6.1; still
untrusted presentation): the header in a `flushleft` environment, the lines
as the rows of a `tabular` (number, sentence, rule with the lines it uses,
checker steps; a long formula on a continuation row), the footer in a
small `flushleft`. Formulas are inline math; the Lean form is the ASCII
notation in the typewriter font (Unicode symbols are not available in
every LaTeX font), the LeanForth form a typewriter block. The first lines
of the outline of `composition`:

```latex
\begin{flushleft}
\textbf{Theorem }$\mathsf{composition}$ \\
  accepted (experimental, not independently audited); axioms: none \\
Statement in Lean (ASCII): {\ttfamily forall~\{A~B~C~:~Prop\},~(A~->~B)~->~(B~->~C)~->~A~->~C} \\
Statement in mathematics: $\forall \{A\ B\ C : \mathrm{Prop}\},\ (A \to B) \to (B \to C) \to A \to C$ \\
```

and, after the header, the rows of the proof:

```latex
  2 & Assume $f : A \to B$. & [assumption] & s26 \\
  3 & Assume $g : B \to C$. & [assumption] & s29 \\
```

The fragment needs `\usepackage{amsmath,amssymb}` (`\operatorname`,
`\blacksquare`) and, for a name with a Greek letter in the Lean or
LeanForth form, a declaration for it such as
`\usepackage[utf8]{inputenc}` with
`\DeclareUnicodeCharacter{03B1}{\ensuremath{\alpha}}`. The macros it
writes are only those of the term printer ([TERM_PRINTER.md](TERM_PRINTER.md)),
`\textbf \textit \texttt \ttfamily \small \par \noindent \hspace \fontdimen
\multicolumn \linewidth \leftarrow \blacksquare` and the environments
`flushleft` and `tabular`. The pinned examples' fragments are in
[`tests/present/outlines-latex.golden`](../../tests/present/outlines-latex.golden);
`make test` compares them, checks their structure (balanced braces and
environments, only those macros) and, when `pdflatex` is installed,
compiles every one in a small document (the machine that wrote this page
has TeX Live, so they are compiled there; a machine without it checks
the structure only and says so).

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
- Plain Unicode text and LaTeX; Markdown and JSON outputs are later
  printer modes. A statement that mentions constants of other declarations
  prints as LeanForth words that can be run only after those declarations
  (see [the command line](COMMAND_LINE.md#printing-a-readable-proof)); a
  declaration with more than 8 universe parameters, or a name the words
  cannot spell, prints the words' reason instead of the block.
- The input is the importer stage and the feed of `check` (any size);
  formulas print from the context that ran the check, between checks.
  Lean writes `a = b` and `n ≤ m` where the printer writes `Eq a b` and
  `LE.le n m`: notation for such operators is plan task 4.4.3. `--name`
  checks every declaration before the named one (it may use them) and so
  takes the time `check` takes up to there, plus the 2 minutes it takes to
  stage and feed `Init`.

# LeanForth user guide

**Status, 2026-11-12: LeanForth re-checks proofs that Lean produced and
exported, and since 2026-11-12 LeanForth text; it does not yet verify a
program.** From the shell, `bin/leanforth check FILE.ndjson`
([the command line](COMMAND_LINE.md)) checks a Lean 4.35.0 export of any
size (all of Lean's `Init` was accepted, and, on build `d789e45f` of
2026-11-13, all of Mathlib's 729,263 declarations; later builds have not
been run on all of Mathlib: [progress](../project/PROJECT_PROGRESS.md)),
but the checker is [kernel] code
and several parts have not passed their review gates.
`leanforth check [--env EXPORT] FILE.lf` checks LeanForth text with the
same checker ([checking a file](LEANFORTH_SYNTAX.md#checking-a-file); plan 8.2.1c-d).
There is a Forth data model for Lean's terms, a Forth reader for Lean's
export format, a term printer, and the first steps of a program-verification
pipeline whose proofs Lean writes; for the clamp word LeanForth's checker re-checks Lean's
exported proofs and the receipt states its verdict (plan 5.5.1). This guide says what that means for you and where the trust
boundaries are. The detailed status is in
[project progress](../project/PROJECT_PROGRESS.md).

| Page | For |
| --- | --- |
| This page | What LeanForth is and is not; trust boundaries; reading paths |
| [Reading a Lean proof](READING_A_LEAN_PROOF.md) | For readers new to Lean and logic notation: every symbol, three small theorems read as textbook proofs, and each in all its forms (Lean source, `#print`, fully explicit, the kernel's nodes, the NDJSON export, LeanForth's Forth words, the term printer) |
| [The command line](COMMAND_LINE.md) | `bin/leanforth check FILE.ndjson` on exports of any size and the other commands, what they print (text, the resource report, JSON), exit statuses 0–6, and the commands still limited to small exports |
| [First check](FIRST_CHECK.md) | The first checker, experimental: a theorem read from Lean's export, checked and accepted; a broken copy rejected |
| [Concepts, in three forms](CONCEPTS.md) | Level, `Sort`, `Prop`/`Type`, term, binder, de Bruijn index, constant, declaration, theorem and definition, kernel, outcomes — each as mathematics, LeanForth Forth and Lean, with Forth you can run |
| [Workflows](WORKFLOWS.md) | Diagrams of checking a theorem and verifying a program, marking what exists and what is planned |
| [Running the checks](RUNNING_THE_CHECKS.md) | The `make` targets, what a pass shows and what it does not |
| [For AI tools](AI_TOOLS.md) | How to call LeanForth from scripts and agents today, determinism, and where the JSON interface will come |
| [Printing terms](TERM_PRINTER.md) | The term printer: Lean notation, ASCII and LaTeX |
| [Terms for new readers](TERMS_FOR_NEW_READERS.md) | A short glossary |
| [WSL setup](SETUP_WSL.md) | Installing on Windows |

## What LeanForth is

LeanForth is being built as two products that share one small checker:

1. **A Lean-compatible proof checker, written in Forth.** It is to read
   the declarations Lean exports — definitions and theorems with their
   proofs — and check each one independently of Lean, so that a result
   does not rest on Lean's own implementation. The goal is all of Lean's
   mathematics library, Mathlib — 729,263 constants with its dependencies
   in the pinned version — not a selection.
2. **A verifier for executable Forth programs.** For a Forth word and a
   stated contract (what it needs and what it guarantees), it is to produce
   proof obligations, check their proofs, and record everything the result
   rests on in a *receipt*; the destination is most of the Forth-2012 Core
   word set ([owner decision](../project/OWNER_DECISIONS.md#program-track-goal-most-of-forth-2012-core-2026-11-02-night)).

Lean is the referee: LeanForth copies the rules of Lean 4.35.0's kernel and
is tested against it, and a rejection means Lean rejects the same thing
([owner decisions](../project/OWNER_DECISIONS.md)). End users are to need
only a Forth system and an export file; Python and Lean are development
tools.

## What LeanForth is not

- **A checker still in its review gates.** It re-checks real libraries
  that Lean exported. The first checker ([ADR 0011](../adr/0011-definite-rejection.md), rules
  approved on 2026-11-02) accepts and rejects definitions, theorems, inductive types
  (also recursive and mutual), `let`, literals, projections and quotients,
  but several of these parts have not passed their review gates. It accepted all of Lean's `Init` and, on build
  `d789e45f` (2026-11-13, the latest run the progress page records; later
  builds not run on all of Mathlib), all 729,263 declarations of Mathlib's export,
  with nested inductive types; a few constructs (metadata, blocks mixing safe
  and unsafe members; unsafe and partial declarations are skipped as Lean skips
  them) are still *unsupported* ([the command line](COMMAND_LINE.md#a-whole-library-leans-init)).
- **Not a replacement for Lean's front end.** LeanForth checks finished
  proof terms. Writing proofs — the elaborator, tactics, `simp` — stays in
  Lean; you check a Lean file by exporting it. Writing theorems and proofs
  in LeanForth's own Forth syntax is planned (plan phase 8).
- **Not yet audited by an outside Lean expert** (planned: plan task 9.2.1,
  owner decision 1).
- **Not a proof of compiled code or hardware.** Once the verifier exists, a verified
  word will be correct only against its stated semantics and assumptions;
  LeanForth has verified no word yet. The receipt lists
  them (the host Forth, cell size, the reader's translation, …). Runtime
  tests are reported separately and are never called proof.
- **Not something that parsing, testing or an AI can make true.** A
  decoded record, a passing test, a fluent explanation or Lean's acceptance
  of a *reference model* is not a LeanForth-checked proof.

## Trust boundaries

Only the checker will decide *accepted*. Everything else can at worst hand
it the wrong claim, which is why the checked statement is to be printed
for a person to read.

| Part | Where | Role | Trust |
| --- | --- | --- | --- |
| Checker | `src/kernel/` | Decides accepted, rejected, unknown, … | The only part to be trusted, after the review gate of `AGENTS.md`; nothing in it is trusted today |
| Data model and library | `src/core/`, `src/lib/` | Stores terms, levels and names; walks, outcomes, contexts | Verdicts will depend on them, so they fall under the same gate |
| Export reader | `src/import/ndjson.fs`, `checker-input.fs`, `stage.fs` | Decodes Lean's NDJSON export and stages it as the checker's input (and, not yet read by the checker, into the compact store) | Untrusted, fail-closed: it rejects anything malformed and decides nothing about proofs |
| Command line | `bin/leanforth`, `src/cli/` | Runs the reader and the checker; prints each declaration's verdict as the checker published it; exit status | Untrusted: it can misreport a failure, never make a declaration accepted |
| Program words | `src/program/verify.fs` | Translates Forth source into the program IR | Untrusted; receipts name it as the assumption `trusted-reader` |
| Term printer | `src/present/` | Prints terms as Lean does | Presentation only; the checker never loads it |
| Proof outlines, tactics, AI tools, explanations | planned | Presentation and proof search | Untrusted; explanations are labelled as templates, reconstructions or AI-written |
| Lean, Python preview, test scripts | `tests/` | Referee and test oracles | Development tools only |
| Gforth, operating system, hardware | host | Run everything | Stated assumptions |

**Axioms.** The first checker accepts no axioms. Later exactly three may be
allowed — `propext`, `Classical.choice` and `Quot.sound`, with their exact
Lean statements, in a versioned list the owner approves — and every
accepted theorem will list the axioms it depends on. `Lean.ofReduceBool`
and `Lean.trustCompiler` are never allowed.

**Outcomes.** Every check ends in one of seven outcomes: *ok* (accepted),
*rejected*, *unknown*, *unsupported*, *invalid*, *exhausted* (out of fuel)
and *full* (out of room). Only *ok* is ever accepted. See
[Outcomes](CONCEPTS.md#outcomes).

## What you can do today

- Run the test suites and the comparisons with Lean
  ([running the checks](RUNNING_THE_CHECKS.md)).
- Read and count any Lean 4.35.0 export, up to all of Mathlib, with the
  Forth reader ([reader guide](../development/NDJSON_READER.md)).
- Check a Lean export of any size with the experimental checker from the
  shell, `bin/leanforth check FILE.ndjson`, and read the verdict of each
  declaration and the exit status ([the command line](COMMAND_LINE.md),
  [first check](FIRST_CHECK.md)); its answers are not yet to be relied on.
  The proofs are Lean's; LeanForth text is checked by `check FILE.lf`.
- Build terms with the data model's words, run the experimental
  inference and definition probe on them, and print them in Lean's
  notation, ASCII or LaTeX ([concepts](CONCEPTS.md),
  [printing terms](TERM_PRINTER.md)).
- Translate the six example Forth words into the program IR and check, with
  Lean, the proofs that their IR behaves as their reference models
  ([program IR](../programming/PROGRAM_IR.md)).

## Reading paths

| You are | Read |
| --- | --- |
| A Forth user who wants verified words | [Workflows](WORKFLOWS.md) (program path), [program IR](../programming/PROGRAM_IR.md), [program receipts](../programming/PROGRAM_RECEIPTS.md), [program examples](../programming/PROGRAM_EXAMPLES.md) |
| A Forth developer contributing code | [Architecture](../development/ARCHITECTURE.md), [source layout](../../src/README.md), [Forth style](../development/FORTH_STYLE.md), [Forth library](../development/FORTH_LIBRARY.md), [testing strategy](../development/TESTING_STRATEGY.md), [`AGENTS.md`](../../AGENTS.md) |
| A Lean user | [The command line](COMMAND_LINE.md) to check an export, [Concepts](CONCEPTS.md) (the Lean forms first), [ADR 0011](../adr/0011-definite-rejection.md) for the first checker's exact scope and rules, [expected results](../reviews/FIRST_CHECKER_EXPECTED.md), [NDJSON reader](../development/NDJSON_READER.md) |
| A mathematician who knows Lean | This page, [Concepts](CONCEPTS.md), [Workflows](WORKFLOWS.md) (theorem path) |
| A mathematician new to Lean | [Reading a Lean proof](READING_A_LEAN_PROOF.md), [terms for new readers](TERMS_FOR_NEW_READERS.md), then [Concepts](CONCEPTS.md), reading the mathematics and Lean forms and skipping the Forth |
| An AI tool or its author | [For AI tools](AI_TOOLS.md), [the command line](COMMAND_LINE.md) and its exit statuses, [interface contracts](../programming/INTERFACE_CONTRACTS.md) (design), [`AGENTS.md`](../../AGENTS.md) |

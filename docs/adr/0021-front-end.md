# ADR 0021: the front end — an untrusted elaborator and tactic engine in Forth, re-checked by the kernel

Status: **proposed** 2026-11-12 (plan rows FE1–FE12 of the
[plan draft](../project/PLAN_DRAFT.md#phase-8-front-end-fe1fe12-2026-11-12-replaces-831-and-832),
which replace rows 8.3.1 and 8.3.2). Nothing of it is built. Design
gates: [bypass] for D1–D3, [parser] for D4, D8 and D10 (rules that decide
what a statement means), [axiom] for D7, and [owner] for the spellings in
D8 and D9 ([questions 1–4](../design/FRONT_END.md#9-questions-for-the-owner)). The owner answered questions 1–4, 6, 7 and 8 on
2026-11-12 (OWNER_DECISIONS.md, "Front-end syntax"; D10's elaboration-data
exporter approved as a development tool); the ADR as a whole stays proposed
until FE1 is built and reviewed.
It builds on [ADR 0017](0017-leanforth-syntax.md) (LeanForth syntax, with
Amendment 1, accepted, and Amendment 2 on branch `lf-files-2`, proposed),
[ADR 0008](0008-outcome-vocabulary.md) (outcomes),
[ADR 0009](0009-reentrant-state-and-parallel-checking.md) (contexts) and
[ADR 0010](0010-wordlists.md) (word lists). The background — what each
part of Lean's front end does, its measured size, and the plan — is in
[the front-end design](../design/FRONT_END.md).

Approval status: proposed (the owner answered front-end questions 1-4 and 6-8 on 2026-11-12, see OWNER_DECISIONS.md section "Front-end syntax (2026-11-12, evening; docs/design/FRONT_END.md §9)"; decisions D1, D2, D3, D5 and D7 approved by the owner 2026-11-12 night, gates [bypass] and [axioms], [OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md) section "Approval round of 2026-11-12, night (approval pack)"; the ADR as a whole stays proposed until FE1 passes its [parser] gate)

## Summary in plain words

LeanForth checks proof terms; it cannot yet *make* them. Lean's front end
makes them: from `0 + n = n` and "by induction" it works out every hidden
detail and builds the full term the kernel checks. This record decides how
LeanForth gets its own front end:

- it is written in Forth, runs in the same Gforth as the words of ADR 0017,
  and is **untrusted**: its only way to a verdict is the kernel's check of
  the finished term, and it can add no axiom;
- it follows **Lean's behaviour** (the owner's rule of 100% Lean): the same
  statements, and for elaboration and the basic tactics the same proof
  terms, compared with pinned Lean;
- people write **natural LeanForth**: postfix words that build a
  Lean-shaped syntax tree, which the front end elaborates in Lean's order;
  the kernel form of ADR 0017 stays as the exact "assembly" form;
- tactics are **words acting on a list of goals**;
- Lean's library data that its export leaves out (instances, simp sets,
  eliminators …) comes from a second file written by pinned Lean;
- LeanForth does **not read `.lean` files**: "full Lean" means that
  everything Lean users can write can be written in LeanForth, with Lean's
  results.

## Context

- **The owner, 2026-11-12.** The hand-written kernel form is "only usable
  as an 'assembly' language"; LeanForth should be "much closer to that nice
  Lean version"; the goal is "a full implementation of Lean with a
  different front-end language, LeanForth"; reporting that blurred Lean's
  proofs and LeanForth's re-checks was "extremely misleading"; natural
  LeanForth may be postfix; Lean's behaviour by default; front-end work to
  start now. The owner asked what `:=` means; the word `proof` was proposed
  instead (open, plan 8.6.10).
- **What exists** ([design §1](../design/FRONT_END.md#1-what-exists-today-and-what-does-not)):
  the kernel re-checks Lean's exports; ADR 0017's words build kernel terms;
  on branch `lf-files-2`, `leanforth check FILE.lf` checks such terms
  (Amendment 2: the text's declarations are written as export records and
  read by the importer stage). There is no elaborator, unification, type
  class resolution, coercion, tactic, match or recursion compilation,
  generated definition or evaluation. `_` is refused (error 52).
- **Lean's front end is large**: `Lean/Elab` 76,612 lines in 320 files,
  `Lean/Meta` 98,540 in 482, Mathlib's tactics 81,374
  ([design §2.2](../design/FRONT_END.md#22-the-pieces-their-sizes-and-what-they-need)).
- **Lean's front end is driven by data the kernel export lacks**:
  attributes such as instances, default instances, reducibility, simp sets
  and `@[induction_eliminator]`, structure information, `protected`; and by
  Lean code registered as extensions (279 built-in simprocs; Mathlib's 81
  `norm_num` and 119 `positivity` extensions; macros and tactics).
- **Evidence that order matters** (pinned Lean 4.35.0, 2026-11-12;
  [design §2.1](../design/FRONT_END.md#21-the-pipeline)): for
  `theorem zero_add' (n : Nat) : 0 + n = n` proved by the tactics
  `induction n`, `case zero => rfl` and `case succ k ih => exact congrArg
  Nat.succ ih` (design §8.1), Lean's term uses
  `Nat.recAux` (chosen by an attribute), `@Eq.refl Nat (0 + 0)` (the tactic
  `rfl`; the term `rfl` would give `@rfl`), and `congrArg`'s hidden
  argument `Nat.add 0 n` (because the expected type is unified before the
  argument `ih` is looked at). A front end that elaborates in another order
  builds a different term, also correct, but not Lean's.

## Decision

### D1. Untrusted, with one route to the kernel

The front end (the natural reader, the elaborator, tactics, `simp`,
decision procedures, Mathlib's tactics, evaluation) is untrusted code, like
the words of ADR 0017. A declaration it builds becomes a checked
declaration only through the route of ADR 0017 Amendment 2, B1: written as
export records, read by the importer stage, checked by the kernel, its
verdict published by the environment's publisher. The front end has no
word that writes an environment slot, a verdict or a snapshot.

### D2. No metavariable reaches the kernel

Metavariables are new leaf kinds of the term and level stores, used only by
the front end. The export-record writer refuses a declaration that contains
one (invalid: "elaboration incomplete"), whatever the front end believes,
so even a front end that forgets to instantiate cannot send a hole. A
second line stays: Lean's export format has no metavariable kind, and the
importer stage refuses any record kind it does not know.

### D3. No `sorry`, no error recovery

There is no `sorry` word. A goal left open at `end NAME`, a failed tactic or
a failed elaboration stops the text with its line, column, token, the goals
and a stable code, and nothing in the text is checked (Amendment 2, B3 (5)).
Lean fills failures with `sorryAx` to report more errors; LeanForth does not.

### D4. The statement is shown, and the rules that make it are gated

The kernel can decide whether a statement is proved, not whether it is the
statement the author meant. So every verdict line names the declaration and
the printer shows the checked statement in LeanForth words, Lean notation
and mathematics (plan 8.6.2), and each elaboration rule that decides what a
statement means — numerals and default instances, operator words, implicit
arguments, instance resolution, coercions, auto-bound implicits, elaboration
data — passes the [parser] gate, with tests that compare the elaborated
statements with pinned Lean's.

### D5. Lean's behaviour by default

- **Statements**: identical to Lean's elaboration of the same source, node
  for node, universe arguments included.
- **Proof terms** of elaboration and of the core tactics (FE1–FE8):
  identical to Lean's for the same tactic script; binder names compared and
  reported separately (the kernel ignores them).
- **Search tactics** (`simp`, `aesop`, `linarith`, `grind` …): the same
  goals solved or refused, a kernel-accepted proof, identical terms measured
  and reported (owner question 7 asks whether this is enough).
- A difference from Lean is a gap, recorded in a ledger and closed; a
  stricter behaviour exists only behind an opt-in flag (the owner's rule of
  2026-11-03). Every feature not yet ported answers *unsupported* at the
  token that needs it.

### D6. A reduction and unification engine of its own

The front end ports Lean's `Meta` layer — `whnf`, type inference and
`isDefEq` with metavariables, transparency levels, caches and fuel — and
does not call `src/kernel/`. Lean keeps the same split (its C++ kernel and
its `Meta` are separate) because the two do different jobs: the kernel
decides, `Meta` searches with holes and heuristics and may say no where the
kernel says yes. The kernel stays small and unchanged; a front-end fault
cannot reach the kernel's state. Tests may compare the two on closed terms.

### D7. Axioms

Tactics and procedures add no axiom; an accepted theorem's axioms are the
kernel's report, unchanged (a `simp` proof may use `propext`, which is on
the allowlist). `native_decide`, `bv_decide` and anything else resting on
`Lean.ofReduceBool` or `Lean.trustCompiler` are permanently unsupported
(AGENTS.md). `Classical` tactics use `Classical.choice` openly, reported as
today.

### D8. Natural LeanForth: postfix words that build a syntax tree

- Natural words do not build kernel terms; they build a **syntax tree**
  shaped like Lean's syntax after macro expansion, every node with its line
  and column. The elaborator runs Lean's algorithm on it, so elaboration
  happens in Lean's order whatever the order of reading.
- **A name takes its explicit arguments from the stack**: as many as its
  type, unfolded to a Π telescope, has explicit binders. Implicit and
  instance arguments are inserted by the elaborator. `' NAME` pushes a
  function without applying it; `$` applies to one more argument.
- **Numerals** are Lean's (`OfNat`, default instances). **Operator words**
  (`+`, `=`, … if the owner allows them, question 1) are defined by the
  versioned notation table that the printer uses (`src/present/notation-table.fs`),
  each building Lean's `binop%`, `binrel%` or plain application.
- Binder words are ADR 0017's; a binder's type is elaborated when its word
  runs. `:=` and `:= by` keep Lean's spelling unless the owner decides
  otherwise (question 2).
- **Two forms**: natural is the default; the kernel form of ADR 0017 is
  marked by a word at the start of the text or region (proposed
  `kernel-form`, question 4); the printer writes the marker.
- **Commands** use Lean's `#` names (`#check`, `#print`, `#reduce`,
  `#eval`, `#synth`), which ADR 0017's rule R1 allows because no Lean name
  contains `#`; `.goals` prints the goals as `.s` prints the stack.

### D9. Tactics: words over a list of goals

A `by` block opens a proof state: an ordered list of goal metavariables.
Tactic words act on the first goal, take term arguments from the data stack
(built with natural words) and elaborate them against the goal when Lean
would. Proposed spelling (question 3): a `by-` prefix on every tactic word
(`by-rfl`, `n by-induction`, `by-exact`, `by-intro: x`), which rule R1
allows and which no Lean name can equal; `by-case: TAG NAMES… =>` focuses a
case as Lean's `case` does. Backtracking combinators restore the stores by
their marks. A goal left at `end` is D3's error.

### D10. Elaboration data

For an imported library, the attributes and environment data of the
Context (instances with priorities, default instances, reducibility,
simp lemmas, eliminators, `elab_as_elim`, class out-parameters, structure
fields and parents, matcher and equation information, `protected`,
`export` aliases) come from an NDJSON file written by a small Lean program
run with pinned Lean at export time, named with its SHA-256 in the export's
manifest, or given with `--elab-data FILE`. Every record is validated
against the export and the file fails closed on anything malformed. A
LeanForth text's own declarations (`instance`, attribute words) add records
of the same kinds. The data never reaches the kernel; it can change what a
statement means, hence D4.

### D11. Extensions are Forth vocabularies

New tactics, simprocs and notation words are Forth words in reviewed
libraries of the front end, loaded as vocabularies; proof files define no
words of their own (ADR 0017 decision 2 stands). Lean's built-in simprocs
and Mathlib's extensions (`norm_num`, `positivity`, …) are re-implemented
in Forth, most used first, each compared with Lean; LeanForth does not run
Lean code.

### D12. Scope: "full Lean" without reading `.lean` files

"Full Lean" means meaning (B) of [design §3](../design/FRONT_END.md#3-what-full-lean-means-for-leanforth):
everything a Lean user can write can be written in LeanForth text, with
Lean's results. LeanForth reads LeanForth text, Lean's exports and the
elaboration data; it does not parse `.lean` files (meaning C, which would
need Lean's extensible parser and an evaluator for Mathlib's Lean code).
The Lean → LeanForth translator (plan 8.6.8) writes exports as LeanForth
text, in natural form once FE2 provides a natural printer mode.

### D13. Placement, state and resources

- `src/front/` (the syntax store, metavariables, `Meta`, term elaborators,
  instances, coercions, data types, matching, recursion, elaboration data)
  and `src/tactic/` (proof states and tactics). Dependencies point one
  way: `lib/` ← `core/` ← `present/` ← `author/` ← `front/` ← `tactic/` ←
  `cli/`; neither new folder uses `kernel/` or `import/` except through the
  record route of D1, which `cli/` drives.
- All state lives in context members (ADR 0009); every search has fuel and
  store limits with ADR 0008's outcomes (exhausted, full: never ok);
  deep terms use explicit stacks (`lib/frame.fs`); Forth-2012 words with the
  existing host adapters, on Gforth 1.0 and 0.7.3.
- Errors use the authoring error catalogue (codes, line and column, token),
  print the goals as Lean prints them, and have a JSON form for AI tools;
  output is deterministic.

### D14. Evaluation

`#reduce` and `#eval` first by the front end's reduction, with big natural
numbers (`lib/bignum.fs`); later definitions compiled to Forth words. A
computed result is never evidence: `decide` and its relatives leave the
evaluation to the kernel's check of the proof term.

## Consequences

- LeanForth gains the half it lacks, step by step, each step a command a
  user runs (FE1–FE12), with counted coverage against Lean (design §6).
- The kernel, its rules and its gates are unchanged; no [kernel] gate is
  needed for front-end work, unless a milestone needs a kernel feature not
  yet there (then that feature has its own [kernel] row).
- The work is large: about 85,000 lines of Lean for meaning (B) before
  Mathlib's tactics; *speculative* 130,000 to 250,000 lines of Forth.
- Plan rows 8.3.1 and 8.3.2 are replaced by FE1–FE12; 8.6.10 is delivered
  by FE2 and 8.6.11 by FE1, FE5 and FE10.
- ADR 0017 decisions 2, 3 and 5 stand; decision 4 (no `+`) is reopened by
  question 1; §17's sketch (holes, `by-` words) is made concrete here.

## Risks

- **Fidelity drift**: elaboration details are many; the comparisons with
  pinned Lean and the gap ledger are the defence; each Lean upgrade is
  re-measured (plan 9.3.1).
- **Statement meaning** (D4): a wrong instance or default could make a
  different statement; the printed statement, the [parser] gate and the
  comparisons are the defence.
- **Process memory**: the front end runs in the checker's process (ADR 0017
  Amendment 1); its stores are bounded and metered, and a fault there is
  contained by D1 and D2, but memory safety of the front end matters as the
  NDJSON reader's does.
- **Size and time**: the plan says how large the work is; nothing is
  reported as done before the done checker runs it.

## Rejected alternatives

- **Calling Lean to elaborate** (send the text to Lean, check what comes
  back): that is today's arrangement with extra steps; the owner asked for
  proofs with no Lean in the loop (plan 8.6.11).
- **Reusing the kernel's `whnf` and `defeq` for elaboration**: they have no
  metavariables or transparency levels, and bending them would put
  front-end needs into trusted code (D6).
- **Building kernel terms directly from postfix words, elaborating as they
  are read**: reading order would decide elaboration order, and the terms
  would differ from Lean's (Context, "Evidence that order matters").
- **A Lean-like infix grammar as the canonical form**: AGENTS.md makes Forth
  tokens canonical; an infix notation layer may translate to LeanForth
  (plan 8.6.7).
- **Reading `.lean` files** (meaning C): needs an evaluator for Lean code;
  not planned (D12).
- **Running Mathlib's Lean extensions in an interpreter**: needs Lean's
  compiler, runtime and its whole `Meta` interface as primitives; larger
  than the front end itself (D11).
- **Error recovery with `sorry`**: could let a text with an open goal look
  finished (D3).
- **An LLM as the front end**: not deterministic; AI tools stay untrusted
  clients that write LeanForth text, as AGENTS.md says.
- **Tactic words with Lean's plain names**: they would hide Lean constants
  and hypotheses of the same name (`rfl`, `funext`, `congr`, `trivial`) and
  break rule R1; kept as the alternative in question 3.

## What the gate review will need for FE1

[parser]: the natural words, numerals, default instances, operator words
and elaboration data, with FE1's comparison of the elaborated statement
and term with pinned Lean's. [bypass]: D1–D3 shown by tests — a planted
front-end fault that hands over a wrong term is rejected by the kernel; a
metavariable is refused by the writer; an open goal stops the text. And the
owner's answers to questions 1–4.

## Reproduction

The Lean runs: `.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean
-DwarningAsError=true FILE.lean` (never an elan proxy) on the theorem of the
Context with `set_option pp.explicit true` and `pp.universes true`; sizes:
the script in [the design's appendix](../design/FRONT_END.md#appendix-measurement-commands).

## Amendment 1 (2026-11-12, late night): `sorry` as in Lean, with a conditional report

Approval status: proposed; the owner decided it on 2026-11-12 (late night), [OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md) section "Kernel fixes, the kernel refactor and `sorry` (2026-11-12, late night)"; the code's [parser] and [format] gates are owed when it is built

This replaces the first sentence of D3 ("There is no `sorry` word"); the rest of D3 stands (no error recovery: a
failed tactic or elaboration still stops the text, and LeanForth never fills a failure with `sorryAx` by itself).

- **`sorry` exactly as Lean has it.** The explicit word `sorry` (a term or a tactic, as in Lean) closes a goal with
  `sorryAx`, as Lean 4.35.0 does. The kernel checks everything else in the declaration. The verdict is Lean's (the
  declaration is accepted with its axioms), and LeanForth reports it **NOT PROVED**, with `sorryAx` named, as it
  already does for exported declarations that use it; it is never counted as proved.
- **A report for proof development** (the owner: "it needs to report the other parts of a check are good somehow for
  development … so proof is called valid if sorry section is true"). For a declaration with open parts the report
  says, in plain words: everything except the open parts was checked by the kernel; the statement holds **if** each
  open part is true; and it lists each open part with its statement (the goal `sorry` closed, in the three forms),
  its source position, and the declarations that depend on it. It never says "proved". The exact wording and the JSON
  fields are a [format] decision when the code is built.
- Owner's reason: their example "a theorem that has two subparts … force one to be true to check the other" is
  Lean's own `sorry`, and LeanForth behaves exactly as Lean by default.

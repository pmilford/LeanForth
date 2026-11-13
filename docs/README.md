# LeanForth documentation

LeanForth does not yet have a working proof checker or program verifier;
see [project progress](project/PROJECT_PROGRESS.md). Documents marked
*proposal* or *design* describe plans, not implemented behavior.

## Where to start

| You are… | Read first |
| --- | --- |
| New to the project or to Lean terms | The [user guide](user/USER_GUIDE.md) (what LeanForth is and is not, and a reading path for each audience), [reading a Lean proof](user/READING_A_LEAN_PROOF.md), [terms for new readers](user/TERMS_FOR_NEW_READERS.md), then [concepts in three forms](user/CONCEPTS.md) |
| Installing and running the tests | [Project README](../README.md#installing-the-pinned-tools-and-running-the-tests), [WSL setup](user/SETUP_WSL.md), [running the checks](user/RUNNING_THE_CHECKS.md) |
| Following progress or plans | [Project progress](project/PROJECT_PROGRESS.md), [development roadmap](project/DEVELOPMENT_ROADMAP.md), [front-end design](design/FRONT_END.md) |
| Writing or reviewing code (human or agent) | [AGENTS.md](../AGENTS.md), [architecture](development/ARCHITECTURE.md), [source layout](../src/README.md), [testing strategy](development/TESTING_STRATEGY.md), [Forth reviewer guide](development/FORTH_REVIEWER.md), [done checker](development/DONE_CHECKER.md) |
| An AI tool, or writing one | [For AI tools](user/AI_TOOLS.md) |

## `user/` — end-user documentation

- [USER_GUIDE.md](user/USER_GUIDE.md) — start here: what LeanForth is and is not, trust boundaries, what you can do today, reading paths for Forth users and developers, Lean users, mathematicians and AI tools.
- [READING_A_LEAN_PROOF.md](user/READING_A_LEAN_PROOF.md) — for readers new to Lean and logic notation: every symbol; composition, "A and B implies B and A" and `2 + 2 = 4` read as textbook proofs; positional encoding and de Bruijn indices; each theorem as Lean source, `#print`, explicit form, kernel nodes, NDJSON, Forth words and printer output; where tactics fit (Lean and Forth examples checked by `make check` and `make test`).
- [CONCEPTS.md](user/CONCEPTS.md) — level, `Sort`, `Prop`/`Type`, term, binder, de Bruijn index, constant, declaration, theorem and definition, kernel, outcomes: each as mathematics, LeanForth Forth (run on Gforth 1.0 and 0.7.3) and Lean (checked with pinned Lean).
- [COMMAND_LINE.md](user/COMMAND_LINE.md) — the command line `bin/leanforth` (version 0): `check` a Lean export with the first checker (`--record` writes its run record), `replay`, `count`, `reexport`, `version`, `capabilities`; what it prints, exit statuses 0–5, manifests, and its limit to small exports; every example run by `make test` and `make check`.
- [FIRST_CHECK.md](user/FIRST_CHECK.md) — the first checker (not through its review gate): `composition` read from its NDJSON export, checked and accepted, and a broken copy rejected, in mathematics, LeanForth Forth and Lean.
- [WORKFLOWS.md](user/WORKFLOWS.md) — diagrams of checking a theorem and verifying a Forth program, marking what exists and what is planned.
- [RUNNING_THE_CHECKS.md](user/RUNNING_THE_CHECKS.md) — the `make` targets and tools, what a pass shows and what it does not.
- [AI_TOOLS.md](user/AI_TOOLS.md) — rules, today's command-line and Forth interfaces, determinism, and where the JSON interface will come.
- [TERMS_FOR_NEW_READERS.md](user/TERMS_FOR_NEW_READERS.md) — plain-language glossary: level, `Sort`, theorem, kernel.
- [SETUP_WSL.md](user/SETUP_WSL.md) — Windows / WSL2 development setup.
- [TERM_PRINTER.md](user/TERM_PRINTER.md) — printing terms readably in Lean notation, ASCII and LaTeX (Markdown math); binder names without capture; the presentation side table.
- [LEANFORTH_SYNTAX.md](user/LEANFORTH_SYNTAX.md) — writing theorems and proofs as LeanForth's own Forth words ([ADR 0017](adr/0017-leanforth-syntax.md); implemented, [parser] gate open), with notes that stay with the proof; six checked examples in three forms, printing back as words, errors with line and column, limits.
- [PROOF_OUTLINE.md](user/PROOF_OUTLINE.md) — readable proofs (implemented, untrusted presentation): the proof outline of `composition` in mathematics, LeanForth words and Lean, printed from the checker's derivation log with every line naming its checker steps; `make print`, `--detail`, when no outline is printed, what is checked and what is template.
- [DEMOS.md](user/DEMOS.md) — five small well-known proofs (Gauss's sum, the odd numbers, commutativity of addition, Cantor's theorem, the irrationality of √2), each in mathematical notation, Lean and LeanForth words, proved by pinned Lean, accepted by LeanForth and shown with a wrong twin it rejects; built from golden outputs by `make test-demos`, rechecked with Lean by `make reference-demos`.
- [ONE_SYMBOL_THREE_PLACES.md](user/ONE_SYMBOL_THREE_PLACES.md) — the three meanings of `+` (Forth's wrapping `+`, the program track's model `c.wrap (a + b)`, Lean's mathematical `HAdd.hAdd`), each in mathematics, LeanForth and Lean, with the bridge theorem `wrap_of_fits` and why no word is shared (ADR 0017 §16).
- [READABLE_PROOFS_SKETCH.md](user/READABLE_PROOFS_SKETCH.md) — the design sketch the proof outline was built from (superseded): the proof of `composition` as the planned proof-outline printer would show it, in mathematics, LeanForth Forth and Lean, and which parts of it are checked and which are only explanation.

The user guide is a start: manuals for each audience grow with the
features they describe.

## `programming/` — writing proofs and verified Forth programs

- [INTERFACE_CONTRACTS.md](programming/INTERFACE_CONTRACTS.md) — proposed JSON API, proof-step records and program receipts (design, not implemented).
- [SECTIONED_FILES.md](programming/SECTIONED_FILES.md) — the container format of `src/lib/sections.fs` (header, section table, SHA-256s, outcomes).
- [PROGRAM_CONTRACTS.md](programming/PROGRAM_CONTRACTS.md) — Lean reference model for program contracts.
- [PROGRAM_EXAMPLE.md](programming/PROGRAM_EXAMPLE.md) — proposed first verified program: bounded clamp.
- [PROGRAM_EXAMPLES.md](programming/PROGRAM_EXAMPLES.md) — the executable Forth examples and their tests.
- [PROGRAM_EXAMPLES_REFERENCE.md](programming/PROGRAM_EXAMPLES_REFERENCE.md) — independent Lean references for those examples.
- [PROGRAM_IR.md](programming/PROGRAM_IR.md) — program IR 0.1: its text form, its Lean semantics, the reader from Forth source, and the proofs that the six example words' IR equals their reference models (implemented, untrusted, checked by Lean).
- [DERIVATION_LOG.md](programming/DERIVATION_LOG.md) — the derivation log (ADR 0013; implemented, [kernel] path with the no-behaviour-change review): records, references and copies, the rule catalogue, where each rule records, the Forth interface, the test preset, and the evidence that it changes no answer.
- [DIAGNOSTICS.md](programming/DIAGNOSTICS.md) — why a check failed: the first failure's reason code, site and numbers, recorded per checker context; the code catalogue (implemented, first form, untrusted).
- [LEANFORTH_WORDS.md](programming/LEANFORTH_WORDS.md) — the LeanForth authoring words (`src/author/`) and the printer's Forth mode: modules, every word and its stack effect, the Forth interface, the error catalogue, limits and tests (implemented, untrusted, [parser] gate open).
- [ELABORATION_DATA.md](programming/ELABORATION_DATA.md) — Lean's instances, default instances, reducibility and eliminators for the front end (plan row FE1d, ADR 0021 D10): `scripts/export-elab.sh`, the format and its schema, `leanforth check --elab-data`, the reader's checks and Forth interface, the comparison with pinned Lean on `Init` (integrated, untrusted; nothing uses the data yet).
- [CHECKED_ENVIRONMENT.md](programming/CHECKED_ENVIRONMENT.md) — the checked environment v0 (ADR 0012): the input, slots, snapshots and handles, finding constants, the publisher, axiom sets; interface, a three-form example, measured limits (implemented, [kernel] code not through the review gate; the type check that fills it is task 2.2.3).
- [INDUCTIVE_BLOCKS.md](programming/INDUCTIVE_BLOCKS.md) — the first data types LeanForth checks (plan task 5.2.1a, ADR 0015): a block of one non-recursive inductive type checked in Lean's order, its recursor built and compared with the file's, the block published together; a three-form example, the steps and their outcomes, limits and evidence (implemented, [kernel][import] code, gate open).
- [PROGRAM_IR_RUN.md](programming/PROGRAM_IR_RUN.md) — the program IR interpreter in Forth and the three-way comparison of the interpreter, the host words and Lean's evaluation of the model (implemented, untrusted; testing, not proof).
- [PROGRAM_RECEIPTS.md](programming/PROGRAM_RECEIPTS.md) — program receipt schema 0.3 (0.2 without the check label, owner 2026-11-12; 0.2 still read, the draft 0.1 refused): separate CHECK, VERIFY and RUN statuses, who settled an obligation, assumptions, per-theorem axioms, and the standard-library validator (implemented; the clamp receipt is generated and states LeanForth's verdict on Lean's proofs, plan 5.5.1).
- [PROGRAM_VC.md](programming/PROGRAM_VC.md) — verification-condition generator v0 and contract language: obligations and contract theorems proved by Lean, wrong contracts refuted; the clamp proofs exported with their closure and re-checked by LeanForth's checker, mutated programs, contracts and proofs rejected (plan 5.5.1), and the generated clamp receipt.
- [SHA256_SPEC.md](programming/SHA256_SPEC.md) — SHA-256 specified in Lean from FIPS 180-4 (flagship stage SHA-1): NIST vectors and the constants checked by Lean's kernel, lemmas for the later stages, what is and is not proved (implemented, checked by Lean, not by LeanForth; nothing yet about the Forth code).
- Lean reference models for individual programs: [checked addition](programming/CHECKED_ADD_REFERENCE.md), [factorial](programming/FACTORIAL_REFERENCE.md), [gcd](programming/GCD_REFERENCE.md), [stack and memory](programming/MEMORY_PROGRAM_REFERENCE.md), [memory copy](programming/MEMORY_COPY_REFERENCE.md), [memory swap](programming/MEMORY_SWAP_REFERENCE.md).

## `design/` — designs of components not built yet

- [FRONT_END.md](design/FRONT_END.md) — LeanForth's front end (design, nothing built): what Lean's elaborator, unification, type classes, coercions, tactics, pattern matching, recursion, generated definitions, `simp`, Mathlib's tactics and evaluation do, each measured in Lean 4.35.0's sources; the planned untrusted Forth architecture re-checked by the kernel; what "full Lean" means; milestones FE1–FE12 with FE1 ($0 + n = n$ by induction) specified in full; questions for the owner.
- [SNAPSHOT_COMPATIBILITY.md](design/SNAPSHOT_COMPATIBILITY.md) — reading snapshots saved by the two previous format and verdict versions (plan 6.2.5c; designed, the owner's four questions answered; code gates owed): optional sections, the reach table of each verdict-version step, results carried or checked again, upgrading a snapshot, tests, costs and questions for the owner.
- [FE1E_APPLICATIONS.md](design/FE1E_APPLICATIONS.md) — plan row FE1e (design, nothing built): how pinned Lean elaborates `0 + n = n` step by step (the acceptance trace), the faithful subset of application elaboration, numerals, `binop%`/`binrel%`, pending metavariables and default instances, tabled instance search with the elaboration data's discrimination-tree keys and Lean's candidate order, the instance-class check (fe1d M1), modules, tests, sub-steps and one owner question (answered 2026-11-12: LeanForth's own fuel).

## `development/` — contributing, testing and tooling

- [ARCHITECTURE.md](development/ARCHITECTURE.md) — diagrams of the layers and trust boundary, tasks and contexts with the shared environment, the principal records, and one stored term.
- [TESTING_STRATEGY.md](development/TESTING_STRATEGY.md) — test layers, harness and CI; the pinned-Lean comparisons that replaced the retired tests of superseded code.
- [FORTH_STYLE.md](development/FORTH_STYLE.md) — the project's Forth style rules: short words, the stack over globals, structures, one error convention.
- [FORTH_REVIEWER.md](development/FORTH_REVIEWER.md) — checklist for reviewing Forth changes.
- [DONE_CHECKER.md](development/DONE_CHECKER.md) — the independent check that work called done is integrated and works end to end; status stages.
- [forth-reviews/](development/forth-reviews/LOG.md) — the Forth review log and every review report (required for each Forth change).
- [done-checks/](development/done-checks/2026-11-12-audit.md) — done-checker reports, starting with the first audit of 2026-11-12.
- [process-audits/](development/process-audits/2026-11-12-agents-md.md) — audits of the AGENTS.md rules against practice.
- [ci-results.log](development/ci-results.log) — every push's local CI results with the Gforth and Lean versions (written by `scripts/push.sh`).
- [FORTH_LIBRARY.md](development/FORTH_LIBRARY.md) — inventory of reusable Forth facilities and what is still missing.
- [TEST_COVERAGE_REVIEW.md](development/TEST_COVERAGE_REVIEW.md) — 2026-11-02 coverage review: findings and their status.
- [INSTALLATION_LOG.md](development/INSTALLATION_LOG.md) — every install and verification command actually run.
- [VERSIONS.md](development/VERSIONS.md) — observed tool versions and pinned download hashes.
- [PROFILING.md](development/PROFILING.md) — opt-in time and memory measurement; results in [measurements/](development/measurements/).
- [Lean kernel profile](development/measurements/lean-kernel-profile-2026-11-02/README.md) — where Lean 4.35.0's kernel spends its time on `Init`, `Std` and a Mathlib slice (by function family, measured with perf), per-declaration times and the slowest declarations, and a nanoda comparison (2026-11-02).
- [Two-mode program words prototype](development/measurements/two-mode-prototype-2026-11-03/README.md) — throwaway evidence for ADR 0019: the real example sources, run by Forth's interpreter with a LeanForth vocabulary, give byte-identical IR on Gforth 1.0.0 and 0.7.3; run mode, replayed reader tests, hostile inputs, an IR round trip, planted faults, a symbolic demo, the mode shift (a third interpreter state, on both Gforths) and defining words and loops in both designs (2026-11-03).
- [KERNEL_START.md](development/KERNEL_START.md) — prerequisites for starting the trusted kernel.
- [ARENA_PROTOTYPE.md](development/ARENA_PROTOTYPE.md) — notes and limits of the experimental term storage.
- [NDJSON_PREVIEW.md](development/NDJSON_PREVIEW.md) — the development-only Lean NDJSON preview.
- [NDJSON_READER.md](development/NDJSON_READER.md) — the Forth reader of Lean NDJSON exports: use, checks, limits, differential evidence and measured speed on all of Mathlib.

## `project/` — status, plans and decisions

- [PROJECT_PROGRESS.md](project/PROJECT_PROGRESS.md) — current status of both product tracks.
- [DEVELOPMENT_ROADMAP.md](project/DEVELOPMENT_ROADMAP.md) — milestones, acceptance criteria (the near-term queue was deleted on 2026-11-12; see "Now, next, later" in PROJECT_PROGRESS.md).
- [PLAN_DRAFT.md](project/PLAN_DRAFT.md) — draft next-level plan (nine phases, about 130 tasks, library gaps, readable-proof mock-ups, owner questions); not approved.
- [SCALE_ASSESSMENT.md](project/SCALE_ASSESSMENT.md) — memory and CPU needed to check all of Mathlib, what in today's design would not scale, and the recommended data structures (2026-11-02 assessment); its last section says where Lean's kernel spends its time and what LeanForth should do about it.
- [IR 0.2 probes](development/measurements/ir-0.2-probes-2026-11-04/README.md) — evidence for ADR 0019 Amendment 1: what Gforth 1.0.0 and 0.7.3 do with redefinitions, output words, shifts and number forms, and two Lean checks (a clamp with `dup .` and ROTR on 32-bit values) (2026-11-04).
- [Mathlib export measurements](development/measurements/mathlib-2026-11-02/README.md) — the pinned Mathlib for Lean 4.35.0 exported and counted on this machine: 729,263 constants, 105.9 M expression nodes, up to 30 universe arguments (2026-11-02).
- [Re-export measurements](development/measurements/reexport-2026-11-03/README.md) — LeanForth re-exports `Init`, `Std` and all of Mathlib byte for byte in Lean's own NDJSON format and reads the copies back to the same dumps (2026-11-03).
- [Compact-store measurements](development/measurements/compact-store-2026-11-02/README.md) — a prototype of ADR 0016 loaded all of `Init`, `Std` and Mathlib into 16-byte hash-consed nodes, verified by re-emission: 2.94 GB for Mathlib's input, 4.2 GB peak (2026-11-02).
- [OWNER_DECISIONS.md](project/OWNER_DECISIONS.md) — the owner's plain-language policy decisions.
- [MINIFORTH_REVIEW.md](development/MINIFORTH_REVIEW.md) — review of MiniForth, a Forth written in Lean (related work, plan W9): what to adopt and what not; no code copied (no licence).
- [BEYOND_LEAN.md](project/BEYOND_LEAN.md) — places where Lean's kernel rejects or cannot decide something true, recorded for a later opt-in improved mode; compatibility mode is unaffected.
- [DECISIONS.md](project/DECISIONS.md) — running decision log with rejected alternatives.
- [IMPLEMENTATION_PLAN.md](project/IMPLEMENTATION_PLAN.md) — staged implementation plan.
- [CODEX_HANDOFF.md](project/CODEX_HANDOFF.md) — the original project brief.
- [RESEARCH_NOTES.md](project/RESEARCH_NOTES.md) — initial research outcomes and open questions.

## `adr/` — architecture decision records

None is approved for trusted implementation. The owner accepted ADRs 0008
and 0009, and approved the rules of ADR 0011 and of ADR 0003's Amendment 1
and the design of ADR 0012 before their code, which needs its own gate
approval; the others are proposals.
[0001](adr/0001-core-fragment.md) core fragment ·
[0002](adr/0002-core-rules.md) typing rules ·
[0003](adr/0003-conversion.md) conservative conversion, with Amendment 1 on binders whose domains differ (rule accepted) ·
[0004](adr/0004-symbolic-universes.md) symbolic universes ·
[0005](adr/0005-structured-names.md) structured names ·
[0006](adr/0006-constant-environments.md) constant environments ·
[0007](adr/0007-sort-representation-boundary.md) Sort representation boundary ·
[0008](adr/0008-outcome-vocabulary.md) one outcome vocabulary (accepted) ·
[0009](adr/0009-reentrant-state-and-parallel-checking.md) re-entrant state and parallel checking (accepted) ·
[0010](adr/0010-wordlists.md) wordlists and module boundaries (proposed; piloted on `src/lib`) ·
[0011](adr/0011-definite-rejection.md) definite rejection and the first checker's scope (rules accepted) ·
[0012](adr/0012-checked-environment.md) the checked environment's implementation (design accepted) ·
[0013](adr/0013-derivation-log.md) the derivation log and the proof outline (proposed) ·
[0014](adr/0014-definitional-equality.md) definitional equality as Lean's kernel decides it: unfolding with hints and lazy delta, theorems unfold last, eta, proof irrelevance, `let`, caches (proposed; Lean-checked table in `make check`) ·
[0015](adr/0015-inductive-types.md) inductive types, constructors and recursors as Lean's kernel checks them; structures, projections, quotients, literals, and the `Nat.add_zero` target (proposed; 100 Lean-checked cases) ·
[0016](adr/0016-compact-store.md) the compact store for Mathlib-scale input: 16-byte nodes, a shared input tier, hash tables (proposed) ·
[0017](adr/0017-leanforth-syntax.md) LeanForth Forth syntax for theorems and proofs (accepted as the design basis) ·
[0018](adr/0018-exceptions.md) when to use `CATCH` and `THROW` (proposed; piloted on level substitution) ·
[0019](adr/0019-program-words-two-modes.md) program words in two modes: the same source loaded with a LeanForth vocabulary that emits IR, or with ordinary Forth to run it (accepted in direction; mode shift or alias still open; [prototype](development/measurements/two-mode-prototype-2026-11-03/README.md)) ·
[0020](adr/0020-checked-snapshot.md) the checked-environment snapshot: a library checked once, saved position-independently with format and verdict versions, reloaded to check a dependent library with exactly a fresh check's verdicts, labelled as saved results (accepted 2026-11-12; plan task 6.2.5) ·
[0021](adr/0021-front-end.md) the front end: an untrusted elaborator and tactic engine in Forth whose every result the kernel re-checks; natural LeanForth as postfix words that build a Lean-shaped syntax tree; Lean's behaviour by default (proposed 2026-11-12; plan FE1–FE12).

## `reviews/` — review packets and records

- [KERNEL_REVIEW.md](reviews/KERNEL_REVIEW.md) — review packet for the first kernel fragment (ADRs 0002 and 0003).
- [CHECKED_ENVIRONMENT_REVIEW.md](reviews/CHECKED_ENVIRONMENT_REVIEW.md) — review packet for ADR 0006.
- [FIRST_CHECKER_GATE.md](reviews/FIRST_CHECKER_GATE.md) — draft plain-language gate summary and owner questions for the first checker (ADR 0011), and a second set for binder comparison (ADR 0003, Amendment 1) and the checked environment (ADR 0012).
- [FIRST_CHECKER_EXPECTED.md](reviews/FIRST_CHECKER_EXPECTED.md) — expected results: Lean's verdict and LeanForth's required outcome for the five fixtures, 53 variants and 27 source copies.
- Dated files (`reviews/YYYY-MM-DD-*.md`) record individual AI and human reviews. They are historical: their text, including file paths, is kept exactly as written.

## Paths before 2026-11-02

Until 2026-11-02 every document lived directly in `docs/`. Dated review
records and `prompts/FIRST_CODEX_TASK.md` still use those old paths. Old
`docs/<name>.md` is now at:

| Folder | Documents |
| --- | --- |
| `docs/user/` | `TERMS_FOR_NEW_READERS`, `SETUP_WSL` |
| `docs/programming/` | `INTERFACE_CONTRACTS`, `PROGRAM_CONTRACTS`, `PROGRAM_EXAMPLE`, `PROGRAM_EXAMPLES`, `PROGRAM_EXAMPLES_REFERENCE`, `CHECKED_ADD_REFERENCE`, `FACTORIAL_REFERENCE`, `GCD_REFERENCE`, `MEMORY_COPY_REFERENCE`, `MEMORY_PROGRAM_REFERENCE`, `MEMORY_SWAP_REFERENCE` |
| `docs/development/` | `TESTING_STRATEGY`, `FORTH_REVIEWER`, `DONE_CHECKER`, `INSTALLATION_LOG`, `VERSIONS`, `PROFILING`, `ARENA_PROTOTYPE`, `KERNEL_START`, `NDJSON_PREVIEW`, `NDJSON_READER`, and `measurements/` |
| `docs/project/` | `PROJECT_PROGRESS`, `DEVELOPMENT_ROADMAP`, `IMPLEMENTATION_PLAN`, `CODEX_HANDOFF`, `OWNER_DECISIONS`, `DECISIONS`, `RESEARCH_NOTES` |
| `docs/reviews/` | `KERNEL_REVIEW`, `CHECKED_ENVIRONMENT_REVIEW` |

ADR 0007 (Sort representation boundary) was numbered 0005 until 2026-11-02.
`make test` runs `scripts/check-doc-links.py`, which fails on any broken
link or `docs/` path outside the historical records, and `scripts/check-adr-status.py`, which fails when an
ADR or an ADR amendment lacks its "Approval status:" line (proposed, accepted with date, gate and
`OWNER_DECISIONS.md`, superseded, or "status unclear (no owner decision found)"), and
`scripts/check-agent-sync.py`, which fails when `.claude/agents/*.md` and `.codex/agents/*.toml` stop defining the
same agents with the same key instructions.

# LeanForth documentation

LeanForth does not yet have a working proof checker or program verifier;
see [project progress](project/PROJECT_PROGRESS.md). Documents marked
*proposal* or *design* describe plans, not implemented behavior.

## Where to start

| You are… | Read first |
| --- | --- |
| New to the project or to Lean terms | [Terms for new readers](user/TERMS_FOR_NEW_READERS.md), then the [project README](../README.md) |
| Installing and running the tests | [Project README](../README.md#installing-the-pinned-tools-and-running-the-tests), [WSL setup](user/SETUP_WSL.md) |
| Following progress or plans | [Project progress](project/PROJECT_PROGRESS.md), [development roadmap](project/DEVELOPMENT_ROADMAP.md) |
| Writing or reviewing code (human or agent) | [AGENTS.md](../AGENTS.md), [source layout](../src/README.md), [testing strategy](development/TESTING_STRATEGY.md), [Forth reviewer guide](development/FORTH_REVIEWER.md) |

## `user/` — end-user documentation

- [TERMS_FOR_NEW_READERS.md](user/TERMS_FOR_NEW_READERS.md) — plain-language glossary: level, `Sort`, theorem, kernel.
- [SETUP_WSL.md](user/SETUP_WSL.md) — Windows / WSL2 development setup.

Full user manuals for Forth users, Lean users, mathematicians and AI tools
are planned and do not exist yet.

## `programming/` — writing proofs and verified Forth programs

- [INTERFACE_CONTRACTS.md](programming/INTERFACE_CONTRACTS.md) — proposed JSON API, proof-step records and program receipts (design, not implemented).
- [PROGRAM_CONTRACTS.md](programming/PROGRAM_CONTRACTS.md) — Lean reference model for program contracts.
- [PROGRAM_EXAMPLE.md](programming/PROGRAM_EXAMPLE.md) — proposed first verified program: bounded clamp.
- [PROGRAM_EXAMPLES.md](programming/PROGRAM_EXAMPLES.md) — the executable Forth examples and their tests.
- [PROGRAM_EXAMPLES_REFERENCE.md](programming/PROGRAM_EXAMPLES_REFERENCE.md) — independent Lean references for those examples.
- Lean reference models for individual programs: [checked addition](programming/CHECKED_ADD_REFERENCE.md), [factorial](programming/FACTORIAL_REFERENCE.md), [gcd](programming/GCD_REFERENCE.md), [stack and memory](programming/MEMORY_PROGRAM_REFERENCE.md), [memory copy](programming/MEMORY_COPY_REFERENCE.md), [memory swap](programming/MEMORY_SWAP_REFERENCE.md).

## `development/` — contributing, testing and tooling

- [TESTING_STRATEGY.md](development/TESTING_STRATEGY.md) — test layers, harness and CI; the pinned-Lean comparisons that replaced the retired tests of superseded code.
- [FORTH_STYLE.md](development/FORTH_STYLE.md) — the project's Forth style rules: short words, the stack over globals, structures, one error convention.
- [FORTH_REVIEWER.md](development/FORTH_REVIEWER.md) — checklist for reviewing Forth changes.
- [FORTH_LIBRARY.md](development/FORTH_LIBRARY.md) — inventory of reusable Forth facilities and what is still missing.
- [TEST_COVERAGE_REVIEW.md](development/TEST_COVERAGE_REVIEW.md) — 2026-11-02 coverage review: findings and their status.
- [INSTALLATION_LOG.md](development/INSTALLATION_LOG.md) — every install and verification command actually run.
- [VERSIONS.md](development/VERSIONS.md) — observed tool versions and pinned download hashes.
- [PROFILING.md](development/PROFILING.md) — opt-in time and memory measurement; results in [measurements/](development/measurements/).
- [KERNEL_START.md](development/KERNEL_START.md) — prerequisites for starting the trusted kernel.
- [ARENA_PROTOTYPE.md](development/ARENA_PROTOTYPE.md) — notes and limits of the experimental term storage.
- [NDJSON_PREVIEW.md](development/NDJSON_PREVIEW.md) — the development-only Lean NDJSON preview.

## `project/` — status, plans and decisions

- [PROJECT_PROGRESS.md](project/PROJECT_PROGRESS.md) — current status of both product tracks.
- [DEVELOPMENT_ROADMAP.md](project/DEVELOPMENT_ROADMAP.md) — milestones, acceptance criteria and the near-term queue.
- [PLAN_DRAFT.md](project/PLAN_DRAFT.md) — draft next-level plan (nine phases, about 130 tasks, library gaps, readable-proof mock-ups, owner questions); not approved.
- [SCALE_ASSESSMENT.md](project/SCALE_ASSESSMENT.md) — memory and CPU needed to check all of Mathlib, what in today's design would not scale, and the recommended data structures (2026-11-02 assessment).
- [Mathlib export measurements](development/measurements/mathlib-2026-11-02/README.md) — the pinned Mathlib for Lean 4.35.0 exported and counted on this machine: 729,263 constants, 105.9 M expression nodes, up to 30 universe arguments (2026-11-02).
- [OWNER_DECISIONS.md](project/OWNER_DECISIONS.md) — the owner's plain-language policy decisions.
- [DECISIONS.md](project/DECISIONS.md) — running decision log with rejected alternatives.
- [IMPLEMENTATION_PLAN.md](project/IMPLEMENTATION_PLAN.md) — staged implementation plan.
- [CODEX_HANDOFF.md](project/CODEX_HANDOFF.md) — the original project brief.
- [RESEARCH_NOTES.md](project/RESEARCH_NOTES.md) — initial research outcomes and open questions.

## `adr/` — architecture decision records

All are proposals; none is approved for trusted implementation.
[0001](adr/0001-core-fragment.md) core fragment ·
[0002](adr/0002-core-rules.md) typing rules ·
[0003](adr/0003-conversion.md) conservative conversion, with Amendment 1 on binders whose domains differ (proposed) ·
[0004](adr/0004-symbolic-universes.md) symbolic universes ·
[0005](adr/0005-structured-names.md) structured names ·
[0006](adr/0006-constant-environments.md) constant environments ·
[0007](adr/0007-sort-representation-boundary.md) Sort representation boundary ·
[0008](adr/0008-outcome-vocabulary.md) one outcome vocabulary (proposed) ·
[0009](adr/0009-reentrant-state-and-parallel-checking.md) re-entrant state and parallel checking (proposed) ·
[0011](adr/0011-definite-rejection.md) definite rejection and the first checker's scope (proposed) ·
[0012](adr/0012-checked-environment.md) the checked environment's implementation (proposed).

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
| `docs/development/` | `TESTING_STRATEGY`, `FORTH_REVIEWER`, `INSTALLATION_LOG`, `VERSIONS`, `PROFILING`, `ARENA_PROTOTYPE`, `KERNEL_START`, `NDJSON_PREVIEW`, and `measurements/` |
| `docs/project/` | `PROJECT_PROGRESS`, `DEVELOPMENT_ROADMAP`, `IMPLEMENTATION_PLAN`, `CODEX_HANDOFF`, `OWNER_DECISIONS`, `DECISIONS`, `RESEARCH_NOTES` |
| `docs/reviews/` | `KERNEL_REVIEW`, `CHECKED_ENVIRONMENT_REVIEW` |

ADR 0007 (Sort representation boundary) was numbered 0005 until 2026-11-02.
`make test` runs `scripts/check-doc-links.py`, which fails on any broken
link or `docs/` path outside the historical records.

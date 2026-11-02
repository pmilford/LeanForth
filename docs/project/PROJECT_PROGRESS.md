# LeanForth project progress

Snapshot: 2026-11-01, with CI, infrastructure, source-layout and legacy-retirement notes updated 2026-11-02.
These are milestones, not estimates of percentage complete.
Prototype success is not theorem acceptance. Update this report after each
meaningful milestone, with the inventory from `python3 scripts/code-inventory.py`.
The two paths share the eventual checked proof infrastructure.

The intended deliverable is a finished, usable LeanForth system, including
Lean/Mathlib-compatible theorem proving, use of the full Mathlib library, and verification of executable Forth
programs. The experimental work reported below is an interim development
stage, not the project's final scope or quality target.

## Subtask status

Each count refers to the numbered acceptance tasks in the
[development roadmap](DEVELOPMENT_ROADMAP.md), not a percentage of effort.
**Done** means every stated acceptance criterion and review gate is met;
**in progress** means evidence exists but the criterion is incomplete;
**not started** means no qualifying implementation or evidence has been
identified. Counts are conservative assessments, not schedules. A Lean
reference model is a mathematical model checked by Lean; it is not yet a
LeanForth proof or proof that the real Forth runtime follows the model.

| Milestone | Done | In progress | Not started |
| --- | ---: | ---: | ---: |
| T1 foundation | 0 | 4 | 0 |
| T2 terms, names, levels | 0 | 4 | 0 |
| T3 scope and substitution | 0 | 3 | 0 |
| T4 equality | 0 | 3 | 0 |
| T5 checker | 0 | 3 | 1 |
| T6 NDJSON | 0 | 3 | 1 |
| T7 Lean corpus | 0 | 3 | 1 |
| T8 declarations | 0 | 2 | 2 |
| T9 full Mathlib | 0 | 0 | 5 |
| T10 native authoring | 0 | 1 | 3 |
| P1 contracts | 0 | 3 | 0 |
| P2 Forth examples | 0 | 3 | 0 |
| P3 execution model | 0 | 3 | 0 |
| P4 model/runtime comparisons | 0 | 3 | 0 |
| P5 shared kernel | 0 | 1 | 2 |
| P6 program representation | 0 | 3 | 0 |
| P7 verification conditions | 0 | 2 | 1 |
| P8 user verifier | 0 | 0 | 3 |
| P9 execution and compilation | 0 | 1 | 3 |
| P10 larger programs | 0 | 0 | 4 |

The high number of in-progress tasks reflects broad acceptance criteria, not
completion of their component work. Split tasks further when an individual
change can be reviewed and accepted independently; do not mark a broad task
done because a test fixture or untrusted diagnostic works.
The nearer-term [execution queue](DEVELOPMENT_ROADMAP.md#near-term-execution-queue-first-checked-declaration)
tracks smaller preparation tasks; the [checked environment review packet](../reviews/CHECKED_ENVIRONMENT_REVIEW.md)
sets out open human-review decisions.

## Import coverage and CI

- **Full NDJSON importer task completion: 0% (0 of 4 T6 acceptance tasks
  done).** Three have work in progress. This is a task-count measure, not an
  estimate of effort remaining or a percentage of all exporter records that
  can be parsed; the complete schema denominator has not been established.
- **Full Mathlib acceptance-task completion: 0% (0 of 5 T9 tasks done).**
  Independently checked Mathlib declaration coverage is also **0%**: none
  have been independently accepted by a LeanForth checker. Denominator,
  pinned 2026-11-02: **0 of 729,263 constants** in the full export of
  Mathlib `v4.35.0` (commit `56a0058`) with its dependencies, sha256
  `18448e5d…59c6` ([measurements](../development/measurements/mathlib-2026-11-02/README.md)).
  Library modules share the Lean kernel and importer primitives; track the
  entire library and later module-level coverage, rather than inventing three
  independent compatibility percentages without defined sections.
- On 2026-11-01, 15 consecutive GitHub Smoke runs failed; the
  [last failing run](https://github.com/pmilford/LeanForth/actions/runs/41354899009)
  failed in the constant fixture's whitespace assertion on distribution
  Gforth. The corrected assertion passed in [run 41379263819](https://github.com/pmilford/LeanForth/actions/runs/41379263819)
  for commit `3bcc348`. That run reported a separate `actions/checkout@v4`
  Node.js 20 deprecation warning. Check the latest run again after each push.
- On 2026-11-02 the last Codex-era commit `1db530d` (tag `pre-claude`) passed
  [run 41476841907](https://github.com/pmilford/LeanForth/actions/runs/41476841907).
  The workflow was then replaced by `.github/workflows/ci.yml`: `make test` on
  distribution Gforth, plus `make check` — including every pinned-Lean
  comparison, previously never run in CI — on pinned Gforth 1.0.0 and Lean
  4.35.0, with checkout upgraded to v7. Locally, `make check` passed with the
  pinned tools on 2026-11-02. The first run of the new workflow,
  [run 41504003139](https://github.com/pmilford/LeanForth/actions/runs/41504003139)
  for commit `1c9b75a`, passed both jobs: distribution Gforth in 29 s, and
  the pinned full suite in 6 min 31 s including building Gforth and
  downloading Lean with empty caches.
- [Run 41505351525](https://github.com/pmilford/LeanForth/actions/runs/41505351525)
  for commit `2b76f35` (documentation reorganisation) failed in both jobs:
  the new documentation link check flagged two placeholder paths that were
  not checked locally because the files were not yet committed. Commit
  `844a829` fixed the text and made the checker include new files;
  [run 41505559829](https://github.com/pmilford/LeanForth/actions/runs/41505559829)
  passed both jobs, the pinned full suite in 3 min 53 s.
- Infrastructure: roadmap task Q9 (consolidate the three successive
  experimental variants, plain, `tagged-` and `mixed-`, of several
  operations) is **done** as of 2026-11-02. Every test and pinned-Lean
  comparison of the superseded variants was first rebuilt on the current
  `mixed-*` code; then the 28 superseded modules, their 91 test files and
  their Make targets were deleted with the owner's approval, leaving one
  variant per operation.

## Lean-compatible theorem proving and Mathlib

| Milestone | Status and evidence / remaining work |
| --- | --- |
| 1. Development foundation | In progress: repository, MIT license, Lean 4.35.0 pin, Gforth, tests and CI skeleton. Installation and portability need further work. |
| 2. Terms, names and universes | In progress: untrusted bounded arenas, symbolic universes and mixed constant-term validation; handle checks reject replaced references. Typing integration and human review remain open. |
| 3. Scope and substitutions | In progress: untrusted scope, shifting and substitution diagnostics exist. A mixed universe substitution also reaches constant arguments and agrees with Lean on 27 finite evaluated cases under a shared-session constraint; general context handling and trusted integration remain incomplete. |
| 4. Definitional equality | In progress: an untrusted mixed-term beta conversion diagnostic agrees with Lean on seven finite cases and compares constant names and universe arguments conservatively. Definition unfolding and many Lean equivalences remain unknown; human review remains outstanding. |
| 5. Small trusted checker | In progress: an untrusted mixed-term diagnostic checks exported `fixturePoly` and `fixtureUse` type/value pairs conditional on an assumed `fixtureId` signature. A Lean oracle checks corresponding cases; 21 finite inference observations cover three universes. No theorem is created; human review remains required. |
| 6. Lean NDJSON importer | Bounded preview preserves constants and definitions; a test-only bridge stages 19 fixture nodes and conditionally diagnoses three type/value pairs in order, stopping on unknown or failure. Signatures remain untrusted assumptions; theorem proposition checks, full import and trusted checking remain. |
| 7. Lean checker compatibility corpus | Selected differential cases exist. Direct Lean kernel reference cases now cover constant lookup and universe arguments; LeanForth cannot yet compare those cases. The official checker corpus has not been demonstrated to pass. |
| 8. Lean declaration features | An untrusted index can specialize assumed candidate signatures containing constants; a nonallocating preflight audits all staged signatures before future inference. A separate Lean oracle checks a declaration with a nested constant in its type, but LeanForth cannot yet check that declaration. General inference, checked declarations, inductives, recursors and quotients remain absent. |
| 9. Full Mathlib | Goal: use all of Mathlib, including its dependencies, as a usable and independently checked theorem and rules base under a reviewed, explicit axiom policy. It is not imported or independently checked; full Lean compatibility, dependency handling, access and practical capacity remain. |
| 10. Native proof authoring | Forth-native term building, elaboration, unification, tactics and rewriting are not started. |

The unsafe symbolic inference draft, in which concrete universe values and
symbolic level indices shared an unprotected representation, was retired on
2026-11-02 with the other superseded code; current checker passes accept only
symbolic Sorts, which have their own tag.

## Provably correct executable Forth

| Milestone | Status and evidence / remaining work |
| --- | --- |
| 1. Contract and assumptions | In progress: Lean models cover clamp, checked addition, absolute value, interval membership, factorial and gcd without proving Forth correspondence. |
| 2. Tested Forth example | Host Forth clamp and five additional examples have finite tests run by `make test-program`; tests alone do not prove them correct. |
| 3. Formal execution model | A Lean reference model proves clamp and successful stack-frame composition properties; a modeled clamp followed by `DROP` is one example. The handwritten model is an assumption when relating it to Forth. |
| 4. Model/runtime comparisons | Finite comparisons cover stack, arithmetic and bounded-memory cases; a test-only copy-then-swap fixture agrees with the Lean model on 1,296 cases including aliases and failures. They do not establish all executions or a verified compiler. |
| 5. Shared proof kernel | Depends on theorem milestone 5; no trusted LeanForth proof checker exists yet. |
| 6. Forth program representation | A Lean reference language models a small stack plus abstract memory, with read-after-write, frame and failure proofs. Copy, swap and composed operations have bounds, aliasing, frame and failure proofs; a copy result is preserved by a continuation satisfying a stated disjoint-write contract. It is not connected to the Forth interpreter; general Forth semantics and effects remain. |
| 7. Verification conditions | A Lean reference proves weakest-precondition, stack-depth and sequential failure rules; an untrusted Forth depth diagnostic matches 1,093 finite cases. A general generator and checked certificates remain unimplemented. |
| 8. User-facing verifier | A general workflow to specify, prove and check Forth programs is not implemented. |
| 9. Verified execution/compilation | Source-to-runtime correspondence and compilation assurance remain; runtime and machine assumptions must be explicit. |
| 10. Larger executable programs | Broader examples, typed memory/tensor contracts and CPU execution remain future work. |

## NDJSON and documentation

We cannot fully import or interpret Lean's NDJSON output. The Python preview
recognizes a bounded selection of names, levels, expressions and theorem
records; selected test-only bridges transfer fixtures to experimental Forth
representations. Many declarations and expressions are unsupported. Parsing a
record or passing a fixture is not independent theorem verification.

Documentation is maintained manually alongside development, including setup,
testing, decisions, API plans, prototype limits and the program example. It is
not automatically generated, and complete user manuals remain to be written.
Future features must include their corresponding documentation and manuals.
[Terms for new readers](../user/TERMS_FOR_NEW_READERS.md) explains the core vocabulary;
the full audience-specific manuals and reviewed diagrams remain planned.

An [opt-in profiling wrapper](../development/PROFILING.md) measures elapsed time and process
peak RSS for an existing finite Lean/Forth substitution workload. It does not
measure checker performance, internal allocation or verified programs; more
granular profiling and fair comparisons remain roadmap work.

## Inventory and testing

Run `python3 scripts/code-inventory.py` for current counts of tracked and
untracked, non-ignored files. Counts are physical lines, including comments and
blank lines, and are not a coverage percentage. Forth source is counted per
`src/` folder ([layout](../../src/README.md)); none of it is a trusted checker.
The superseded `legacy/` folder (28 files, 2,676 lines) and its 91 test files
were retired on 2026-11-02 (roadmap Q9). Generated and ignored toolchains are
excluded. See `docs/development/TESTING_STRATEGY.md` for the testing approach and limitations.

Inventory on 2026-11-02 after the legacy retirement (`python3 scripts/code-inventory.py`):

| Category | Files | Physical lines |
| --- | ---: | ---: |
| Forth source, `src/lib/` | 10 | 667 |
| Forth source, `src/core/` | 10 | 851 |
| Forth source, `src/kernel/` | 13 | 1,799 |
| Forth source, `src/import/` | 1 | 67 |
| Forth source, `src/program/` | 3 | 124 |
| Forth source, `src/main.fs` | 1 | 45 |
| Forth tests and support | 95 | 8,327 |
| Other test code and support (Python, shell) | 45 | 4,030 |
| Lean references and tests | 80 | 4,239 |
| NDJSON fixtures | 5 | 138 |
| Markdown documentation | 74 | 9,059 |
| Other project files | 31 | 1,806 |

# LeanForth project progress

Snapshot: 2026-11-01. These are milestones, not estimates of percentage complete.
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

## Import coverage and CI

- **Full NDJSON importer task completion: 0% (0 of 4 T6 acceptance tasks
  done).** Three have work in progress. This is a task-count measure, not an
  estimate of effort remaining or a percentage of all exporter records that
  can be parsed; the complete schema denominator has not been established.
- **Full Mathlib acceptance-task completion: 0% (0 of 5 T9 tasks done).**
  Independently checked Mathlib declaration coverage is also **0%**: none
  have been independently accepted by a LeanForth checker. The total corpus
  has not been pinned, so a numerical declaration denominator is unavailable.
  Library modules share the Lean kernel and importer primitives; track the
  entire library and later module-level coverage, rather than inventing three
  independent compatibility percentages without defined sections.
- On 2026-11-01, 15 consecutive GitHub Smoke runs failed; the
  [last failing run](https://github.com/pmilford/LeanForth/actions/runs/41354899009)
  failed in the constant fixture's whitespace assertion on distribution
  Gforth. The corrected assertion passed in [run 41379263819](https://github.com/pmilford/LeanForth/actions/runs/41379263819)
  for commit `3bcc348`. That run reported a separate `actions/checkout@v4`
  Node.js 20 deprecation warning. Check the latest run again after each push.

## Lean-compatible theorem proving and Mathlib

| Milestone | Status and evidence / remaining work |
| --- | --- |
| 1. Development foundation | In progress: repository, MIT license, Lean 4.35.0 pin, Gforth, tests and CI skeleton. Installation and portability need further work. |
| 2. Terms, names and universes | In progress: untrusted bounded arenas, symbolic universes and mixed constant-term validation; handle checks reject replaced references. Typing integration and human review remain open. |
| 3. Scope and substitutions | In progress: untrusted context-domain and mixed constant-term scope diagnostics exist. Experimental mixed shifting and single-binder instantiation agree with Lean on 45 and 30 finite syntax cases, respectively; mixed conversion and general context validation remain incomplete. |
| 4. Definitional equality | In progress: untrusted mixed-term weak-head reduction agrees with Lean on seven finite cases; conservative mixed syntax comparison handles constants and ordered universe arguments. General mixed conversion and many Lean equivalences remain unknown; human review remains outstanding. |
| 5. Small trusted checker | In progress: an untrusted tagged diagnostic checks a symbolic polymorphic identity type/value pair, but creates no theorem; application inference passes 18 finite Lean comparisons. Human review remains required. |
| 6. Lean NDJSON importer | Bounded preview preserves constants and definitions; a test-only bridge stages all 19 nodes of one constant-containing fixture and checks the scope of its definition and theorem roots, including an escaping-binder rejection. Dependency validity, full import and trusted checking remain. |
| 7. Lean checker compatibility corpus | Selected differential cases exist. Direct Lean kernel reference cases now cover constant lookup and universe arguments; LeanForth cannot yet compare those cases. The official checker corpus has not been demonstrated to pass. |
| 8. Lean declaration features | An untrusted diagnostic compares an exported definition's type and value, and another applies its candidate signature to open arguments. No declaration is registered as checked; general inference, inductives, recursors and quotients remain absent. |
| 9. Full Mathlib | Goal: use all of Mathlib, including its dependencies, as a usable and independently checked theorem and rules base under a reviewed, explicit axiom policy. It is not imported or independently checked; full Lean compatibility, dependency handling, access and practical capacity remain. |
| 10. Native proof authoring | Forth-native term building, elaboration, unification, tactics and rewriting are not started. |

The symbolic inference draft is excluded from the normal suite: concrete
universe values and symbolic level indices share an unprotected representation.
Do not use it until the representations are isolated and reviewed.

## Provably correct executable Forth

| Milestone | Status and evidence / remaining work |
| --- | --- |
| 1. Contract and assumptions | In progress: Lean models cover clamp, checked addition, absolute value, interval membership, factorial and gcd without proving Forth correspondence. |
| 2. Tested Forth example | Host Forth clamp and five additional examples have finite tests run by `make test-program`; tests alone do not prove them correct. |
| 3. Formal execution model | A Lean reference model proves clamp properties and frame preservation for successful modeled programs; the handwritten model is an assumption when relating it to Forth. |
| 4. Model/runtime comparisons | Finite comparisons cover stack instructions, arithmetic and 28 bounded-memory cases against Lean models; they do not establish all executions or a verified compiler. |
| 5. Shared proof kernel | Depends on theorem milestone 5; no trusted LeanForth proof checker exists yet. |
| 6. Forth program representation | A Lean reference language models a small stack plus abstract memory, with read-after-write, frame and failure proofs. Composed memory-copy, swap and copy-then-swap programs have bounds, aliasing, frame and failure proofs in that model. It is not connected to the Forth interpreter; general Forth semantics and effects remain. |
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

An [opt-in profiling wrapper](PROFILING.md) measures elapsed time and process
peak RSS for an existing finite Lean/Forth substitution workload. It does not
measure checker performance, internal allocation or verified programs; more
granular profiling and fair comparisons remain roadmap work.

## Inventory and testing

Run `python3 scripts/code-inventory.py` for current counts of tracked and
untracked, non-ignored files. Counts are physical lines, including comments and
blank lines, and are not a coverage percentage. Experimental Forth is counted
as source but is not a production checker. Generated and ignored toolchains are
excluded. See `TESTING_STRATEGY.md` for the testing approach and limitations.

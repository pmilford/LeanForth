# LeanForth project progress

Snapshot: 2026-10-31. These are milestones, not estimates of percentage complete.
Prototype success is not theorem acceptance. Update this report after each
meaningful milestone, with the inventory from `python3 scripts/code-inventory.py`.
The two paths share the eventual checked proof infrastructure.

The intended deliverable is a finished, usable LeanForth system, including
Lean/Mathlib-compatible theorem proving, use of the full Mathlib library, and verification of executable Forth
programs. The experimental work reported below is an interim development
stage, not the project's final scope or quality target.

## Lean-compatible theorem proving and Mathlib

| Milestone | Status and evidence / remaining work |
| --- | --- |
| 1. Development foundation | Established in part: repository, MIT license, Lean 4.35.0 pin, Gforth, tests and CI skeleton. Installation and portability need further work. |
| 2. Terms, names and universes | Partial untrusted bounded Forth arenas and symbolic universe experiments; handle-based checks reject replaced referenced levels, while raw consumers and human review remain open. |
| 3. Scope and substitutions | Partial experimental operations include tagged term substitution and simultaneous universe substitution in levels and terms; 48 finite cases of each agree with Lean. These tests do not prove general correctness. |
| 4. Definitional equality | Partial beta-aware conversion with selected symbolic universe identities; many Lean equivalences remain unknown. Independent review found no demonstrated false equality; human review remains outstanding. |
| 5. Small trusted checker | Not complete: an untrusted tagged diagnostic checks a symbolic polymorphic identity type/value pair, but creates no theorem; application inference passes 18 finite Lean comparisons. Human review remains required. |
| 6. Lean NDJSON importer | Bounded preview preserves constants and definitions and reports local dependency/order/arity observations; dependency validity remains unchecked. Full import and trusted checking remain. |
| 7. Lean checker compatibility corpus | Selected differential cases exist. Direct Lean kernel reference cases now cover constant lookup and universe arguments; LeanForth cannot yet compare those cases. The official checker corpus has not been demonstrated to pass. |
| 8. Lean declaration features | A bounded untrusted candidate-signature index and a draft constant-environment ADR exist. They do not check scope, types, dependencies, proofs or declarations. Full constants, definitions, inductives, recursors, quotients, polymorphic checking and other core features remain. |
| 9. Full Mathlib | Goal: use all of Mathlib, including its dependencies, as a usable and independently checked theorem and rules base under a reviewed, explicit axiom policy. It is not imported or independently checked; full Lean compatibility, dependency handling, access and practical capacity remain. |
| 10. Native proof authoring | Forth-native term building, elaboration, unification, tactics and rewriting remain to be developed. |

The symbolic inference draft is excluded from the normal suite: concrete
universe values and symbolic level indices share an unprotected representation.
Do not use it until the representations are isolated and reviewed.

## Provably correct executable Forth

| Milestone | Status and evidence / remaining work |
| --- | --- |
| 1. Contract and assumptions | Partial: the clamp example documents a mathematical contract and runtime assumptions. |
| 2. Tested Forth example | A host Forth clamp and finite tests exist; tests alone do not prove it correct. |
| 3. Formal execution model | A Lean reference model proves clamp properties and frame preservation for successful modeled programs; the handwritten model is an assumption when relating it to Forth. |
| 4. Model/runtime comparisons | Finite differential examples compare the reference model and Forth execution; host tests include 1,470 nested-clamp and 784 monotonicity cases, not all executions or a verified compiler. |
| 5. Shared proof kernel | Depends on theorem milestone 5; no trusted LeanForth proof checker exists yet. |
| 6. Forth program representation | A small Lean reference language models push, duplicate and addition; an exact static stack-depth bound is proved for that model. A separate abstract bounded-memory model has read, write and copy properties, but is not connected to the Forth interpreter. General Forth semantics and effects remain. |
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

## Inventory and testing

Run `python3 scripts/code-inventory.py` for current counts of tracked and
untracked, non-ignored files. Counts are physical lines, including comments and
blank lines, and are not a coverage percentage. Experimental Forth is counted
as source but is not a production checker. Generated and ignored toolchains are
excluded. See `TESTING_STRATEGY.md` for the testing approach and limitations.

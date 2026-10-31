# LeanForth project progress

Snapshot: 2026-10-31. These are milestones, not estimates of percentage complete.
Prototype success is not theorem acceptance. Update this report after each
meaningful milestone, with the inventory from `python3 scripts/code-inventory.py`.
The two paths share the eventual checked proof infrastructure.

The intended deliverable is a finished, usable LeanForth system, including
Lean/Mathlib-compatible theorem proving and verification of executable Forth
programs. The experimental work reported below is an interim development
stage, not the project's final scope or quality target.

## Lean-compatible theorem proving and Mathlib

| Milestone | Status and evidence / remaining work |
| --- | --- |
| 1. Development foundation | Established in part: repository, MIT license, Lean 4.35.0 pin, Gforth, tests and CI skeleton. Installation and portability need further work. |
| 2. Terms, names and universes | Partial untrusted bounded Forth arenas and symbolic universe experiments; ADR 0005 proposes a boundary, with an isolated tagged-syntax validator under test. Human review remains required. |
| 3. Scope and substitutions | Partial experimental operations with selected differential comparisons to Lean, not a proof of correctness. |
| 4. Definitional equality | Partial conservative comparison and reductions; significant Lean rules remain unsupported. |
| 5. Small trusted checker | Not complete: inference and declaration probes are experiments, not a trusted kernel or theorem handles. Human review remains required. |
| 6. Lean NDJSON importer | Bounded development preview and selected fixture bridges only; full declaration import and checking remain. See `NDJSON_PREVIEW.md`. |
| 7. Lean checker compatibility corpus | Selected differential cases exist; the official checker corpus has not been demonstrated to pass. |
| 8. Lean declaration features | Full constants, definitions, inductives, recursors, quotients, polymorphic checking and other core features remain. |
| 9. Mathlib | Not imported or independently checked; requires substantially more Lean compatibility and practical capacity. |
| 10. Native proof authoring | Forth-native term building, elaboration, unification, tactics and rewriting remain to be developed. |

The symbolic inference draft is excluded from the normal suite: concrete
universe values and symbolic level indices share an unprotected representation.
Do not use it until the representations are isolated and reviewed.

## Provably correct executable Forth

| Milestone | Status and evidence / remaining work |
| --- | --- |
| 1. Contract and assumptions | Partial: the clamp example documents a mathematical contract and runtime assumptions. |
| 2. Tested Forth example | A host Forth clamp and finite tests exist; tests alone do not prove it correct. |
| 3. Formal execution model | A separate Lean reference model proves properties of a small stack-machine clamp, including idempotence for ordered bounds and failure for every data stack shorter than three cells; the handwritten model is an assumption when relating it to Forth. |
| 4. Model/runtime comparisons | Finite differential examples compare the reference model and Forth execution, not all executions or a verified compiler. |
| 5. Shared proof kernel | Depends on theorem milestone 5; no trusted LeanForth proof checker exists yet. |
| 6. Forth program representation | A general formal representation, semantics and stack/effect contracts are still needed. |
| 7. Verification conditions | General generation of proof obligations and checked certificates is not implemented; depends on the shared kernel. |
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

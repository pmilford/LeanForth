# LeanForth development roadmap

Planning baseline: 2026-11-01, using the 2026-10-31 [progress snapshot](PROJECT_PROGRESS.md), [implementation plan](IMPLEMENTATION_PLAN.md), [handoff](CODEX_HANDOFF.md), [interface contracts](../programming/INTERFACE_CONTRACTS.md), repository inventory and local worktree. This is an actionable proposal, not a claim that future gates have passed. Milestone numbers match the two progress tracks; they are dependency labels, not dates or percentages. Each numbered item below is a separately reviewable issue with its own acceptance evidence. Existing experimental code is untrusted until explicitly reviewed and incorporated into a checker.

## Sequence and shared rules

1. In parallel, stabilize **T1–T3** and **P1–P4**; prepare importer fixtures and checker oracle cases without importing declarations as trusted. Design program semantics and certificate interfaces alongside the kernel.
2. Complete **T4–T5** before any theorem or program receipt can say kernel-accepted; develop **P6–P7** against the reference model in parallel, but gate checked VCs and **P5** on T5. T6–T8 and T7 advance iteratively: importer and corpus work can start early, while each declaration feature requires its own reviewed checker rules.
3. Deliver a narrow end-to-end proof and verified-source workflow through **T5, T10, P5–P8**. Expand declaration support and corpus coverage through **T6–T9** concurrently with runtime correspondence and larger programs in **P9–P10**. No cyclic dependency: a first closed-term checker and bounded pure program subset precede general declarations, full Mathlib and general Forth.
4. Each issue records commands, tool versions, corpus/input hashes, platform, actual CI run and outcomes; distinguishes unsupported, resource exhaustion and invalid input; updates progress, decisions, user/contributor/testing/interface docs and public Forth stack effects as applicable. Add positive, negative and malformed/resource tests before implementation. Tests and differential agreement are evidence, not proofs of general correctness.
5. Kernel semantics changes require an ADR, positive and negative tests, comparison to pinned Lean 4.35.0 where available, and explicit human review before merge. Human review also gates declaration import, certificate formats, axiom policy, verifier bypasses, compiler/FFI assumptions and mathematical parser semantics. LLM review cannot replace it. New runtime/network dependencies require user approval; preserve the audited axiom allowlist, rejecting unapproved axioms.
6. CHECK checks without arbitrary execution; VERIFY requires kernel-checked obligations and records assumptions; RUN reports the actual backend and its separate validation status. Fail closed; never promote parser, tactic, solver, explanation or runtime success into proof acceptance. Canonical source remains ordinary Forth; typed mathematical ASTs and external notation adapters remain separate.

## Cross-cutting work: profiling and research validation

These are planned tasks, not claims that the current experimental checker can
run the examples or that performance data has already been collected.

### Very long term: concurrent proof work

**Current state:** most arenas, sessions, indexes and scratch variables are
global and documented as non-reentrant. Do not run concurrent proof jobs in
the same image or claim Gforth multitasking support today. Direction, as a
proposal: [ADR 0009](../adr/0009-reentrant-state-and-parallel-checking.md)
(per-check state in records, one context per worker, an append-only checked
environment, processes first and Gforth 1.0 native tasks second). The term,
level and name stores and the four lowest walkers already keep their state
in records (2026-11-02).

- **C1 — investigate** (in progress: Gforth 1.0's pthread multitasker gave
  about 6× on 12 CPU-bound tasks on the development machine; Gforth 0.7.3 has
  only cooperative tasks; see ADR 0009): Document the actual Gforth multitasking and task-local
  facilities on supported hosts, distinguishing cooperative tasks, operating
  system threads and separate processes. Inventory all shared Forth state,
  allocators, I/O, exceptions and foreign interfaces in the eventual checker.
- **C2 — isolate:** Design explicit per-job sessions, arenas, scratch, resource
  budgets and ownership/lifetime rules. Define how any shared immutable checked
  environment is published and protected; no job may observe another job's
  partial declarations, scratch, assumptions or proof results. Review changes
  to the trusted boundary and serialization before implementation.
- **C3 — validate:** Test repeated interleavings, cancellation, exhaustion,
  stale handles, independent axiom policies and adversarial inputs. Compare
  results with isolated serial runs and run actual tests on each claimed host.
  Separate processes may be an interim isolation strategy, not evidence that a
  shared Forth image is reentrant.
- **C4 — measure:** Benchmark throughput, memory and scheduling overhead on
  representative proof and program-verification workloads; document supported
  concurrency and limits. Never let parallelism bypass proof checking.

## Near-term execution queue: first checked declaration

The earlier roadmap has useful acceptance goals but its items combine many
changes and review gates, so a count of finished broad tasks conceals progress
and makes the next step hard to see. This queue splits the current critical
path into smaller deliverables. The first two are completed **experimental
preparation**, not completed trusted-kernel milestones.

| Task | Status | Acceptance evidence or next step |
| --- | --- | --- |
| Q1. Mixed syntax and scope | Done, untrusted | Constant-bearing source graphs and binder scope are audited with negative and resource tests. |
| Q2. Candidate signature preflight | Done, untrusted | All staged candidate roots are audited before later allocations; identity reuse and malformed metadata are tested. |
| Q3. Mixed inference transaction | Done, untrusted | Closed mixed-term inference preaudits source and signature snapshots, bounds fuel, and rolls back all arenas on failure. Tests include stale later signatures, exhaustion and generated references. No theorem is accepted. |
| Q4. Real exported fixture | Done, untrusted | The pinned `fixturePoly` and `fixtureUse` exports are staged and their values inferred using `fixtureId` as an unchecked assumption. Wrong arguments return inconclusive and fail closed; stale candidate signatures are rejected in diagnostic tests. |
| Q5. Lean comparison | In progress | Direct Lean kernel checks cover both fixture-shaped values; a 21-case finite comparison checks independently constructed expected types, nested binders and three concrete universes. The Forth converter participates in its own expected-type check; Lean failure reasons are not inspected. Broaden symbolic-universe, malformed-input and resource cases before calling this complete. |
| Q6. Checked environment design | In progress | Design done: the owner accepted [ADR 0011](../adr/0011-definite-rejection.md) (rejection rules, gate answers G1–G4), [ADR 0003 Amendment 1](../adr/0003-conversion.md) (binder domains, G6) and [ADR 0012](../adr/0012-checked-environment.md) (the checked environment: slots published once after full success, snapshots and handles, transitive axiom sets, a single publisher; G8–G11) on 2026-11-02. Implemented as v0 (plan task 2.2.2, [CHECKED_ENVIRONMENT.md](../programming/CHECKED_ENVIRONMENT.md)), awaiting its independent review and the owner's gate; next `check-declaration` (2.2.3) and the failure-path suite (2.2.4), and pass the review gate in `AGENTS.md` before any result is called checked. |
| Q7. First independently checked declaration | Not started | A test-only chain can diagnose three fixture pairs and stage conditional signatures in order, but does not check dependencies or accept declarations. After Q3–Q6 and the kernel review gate, check a real closed definition and a theorem against the prior checked environment, reject mutations and unapproved assumptions, and preserve replayable evidence. |
| Q8. Parallel program path | In progress | Owner goal (2026-11-02): most of Forth-2012 Core, in five stages (plan, program-track goal). Done: IR 0.1 for a small Forth subset with Lean semantics and proofs (`tests/reference/program-ir.lean`), receipt schema 0.1, and a reader from Forth source to IR. The reader and schema were fixed after their independent review (names found ignoring ASCII case as Gforth finds them; nothing in the source is ever run). In progress: an IR interpreter compared three ways, verification conditions and a first receipt for the clamp example. The reader and schema need the owner's [parser] and [format] gates before a receipt is relied on. |
| Q9. Consolidate experiments | Done 2026-11-02 | The variant each later step builds on was identified and the source tree reorganised to match ([source layout](../../src/README.md)): the current `mixed-*` path and the modules it uses are in `src/core/` (data model) and `src/kernel/` (checker under development). Every test and pinned-Lean comparison that used a superseded module was rebuilt on current code (11 ported comparison tables, `tests/core/lean-differential.py`), and then, with the owner's approval, the 28 superseded modules (plain and `tagged-` shift, instantiate, beta, compare, convert and infer, the `raw-*` signature index, the `constant-*`/`context-*` probes, `arena.fs` and the unsafe `symbolic-infer.fs` draft), their 91 test files and their Make targets (`test-legacy`, `test-legacy-differential`, `test-symbolic-infer-draft` and 18 Lean comparisons) were deleted. The capabilities only that code had are recorded with the owner's answers in [decisions](DECISIONS.md) ("Legacy retired — 2026-11-02"): theorem mode returns in phase 2, open terms under a supplied context wait for a Lean-style local context. The profiling workload moved to the current universe substitution. |
| Q10. Refactor core to the Forth style guide | Done | Owner direction 2026-11-02: rework `src/core/` and `src/kernel/` from the lowest layer up to the [style guide](../development/FORTH_STYLE.md) without changing behavior; `make forth-metrics` tracks progress (baseline for `src/core/` plus `src/kernel/`: 218 words, 23% over ten lines, 225 globals). Done 2026-11-02: `src/lib` (portability, range checks, `store:`, tagged nodes, outcomes, `walk:`, paired `walk2:`, `frames:`, contexts, the job pool), every core and kernel module, the loader and the program examples rebuilt on it (687 words, none over ten lines), each with a randomized differential against the previous code and an independent review; every module `require`s its direct dependencies and loads alone (`make smoke`); *exhausted* (out of fuel) split from *full* (out of room); superseded variants retired. Every module's state is in the per-task context ([ADR 0009](../adr/0009-reentrant-state-and-parallel-checking.md) step 3), with a per-context diagnostic record. Follow-ups: one recursion pattern; the loader, program reader and NDJSON counter state. |

Run focused tests while developing. Group roughly two coherent increments
before the full regression suite and commit when feasible; checkpoint earlier
for risk, CI failure or a review boundary. Larger batches do not waive negative
tests, independent review, human approval of trusted changes, or CI checks.

### Documentation and diagrams

- **D1 — audiences:** Develop and keep current separate entry points for Forth
  developers, Forth users, Lean users, mathematicians familiar with Lean,
  mathematicians new to Lean, and AI tools. Explain level, Sort, theorem,
  kernel and trust boundaries in plain language with examples. Show each
  example as a concrete, slightly non-trivial instance in three forms:
  mathematical notation, LeanForth Forth syntax and Lean (owner, 2026-11-02).
  Give each
  audience a path to the reference manual, setup, supported features and limits.
- **D2 — diagrams:** Use a diagram tool to create readable, correctly rendered
  flowcharts for using and understanding theorem proving and program
  verification, and diagrams of principal data structures and ownership.
  Review every arrow, label, direction and trust boundary against current code;
  check rendered output and update diagrams with implementation changes.
  Label future workflows as planned, not existing functionality.
- **D3 — limits:** Document actual supported constructs and observed limits on
  input size, term/dependency depth, resource budgets, compute and memory for
  both paths, with tool versions and reproduction commands. Distinguish fixed
  bounds, configurable limits, measured capacities and untested ranges.

### Near term: low-friction time and memory profiling

- **M1 — measurement interface:** Provide an opt-in command or flag for
  elapsed time and memory with concise default output, scriptable structured
  results and a detailed mode. Normal tests and use should not require a
  profiler or suffer significant overhead; measure and report that overhead.
  Profiling must not affect proof decisions or depend on GPU/network services.
- **M2 — useful attribution:** Measure end-to-end operations and selected
  lower-level stages, including decoding/staging, checking, normalization,
  substitution, allocation and program verification/execution as those stages
  become available. Track allocation counts and arena high-water marks where
  practical, alongside process peak memory. Define each metric and distinguish
  Forth-managed counts from process RSS; unsupported metrics must be reported
  as unavailable, not zero. Avoid instrumenting every inner operation by
  default; verify that disabled profiling leaves behavior unchanged.
- **M3 — repeatable Lean comparisons:** Select equivalent inputs and clearly
  comparable work; record exact Lean and LeanForth versions, input and corpus
  hashes, hardware, OS, warm/cold cache conditions, setup, repetitions and
  timing/memory collection method. Separate startup, parsing, elaboration,
  checking and execution where possible. Report mismatches in supported work,
  unverified assumptions and measurement limitations rather than presenting
  different workloads as a speed comparison. Start with currently runnable
  matched operations and report experimental diagnostics as such; establish
  checker and full-workflow baselines as those operations become available.
- **M4 — replaceable hot paths:** Document stable contracts and identify
  measured costs before optimizing. Factor storage, traversal and execution
  boundaries so a slower implementation can be replaced behind the same
  interface and rechecked against regression, differential and trust-boundary
  tests. Do not trade correctness or review for speed. Record prerequisites
  and obtain approval before adding any new runtime/network dependency.

### Long term: reproduce published work and investigate open problems

- **R1 — several substantial results:** Find several published Lean results
  whose statements and proofs span several pages. Record source links, exact
  versions, licenses, dependencies, theorem statements and assumptions.
  Translate each *problem statement* into canonical LeanForth; construct or
  import the corresponding proof as supported, run the checker, and compare
  statements, assumptions, outcomes and reproducible measurements with Lean.
  Do not present a parsed statement or a hand-written proof narrative as a
  checked result. This depends on the needed T5–T10 features and library.
- **R2 — longer recent theorem:** Select a longer, recent but tractable
  published Lean-proved theorem with accessible sources. Record selection date,
  exact source and dependencies; translate its problem statement, run
  LeanForth and Lean, and compare verified results, assumptions and metrics.
  Clearly report omissions or unsupported features. This extends R1; it does
  not imply that one example demonstrates complete Mathlib compatibility.
- **R3 — open-problem investigation:** After substantial verified examples,
  identify a plausibly approachable unsolved mathematical problem, verify its
  status against dated primary sources, record the precise statement and
  assumptions, and express it in LeanForth. Attempt a solution with the
  assistant guiding exploration, preserving failed attempts and partial results.
  Report a solution only with a kernel-checked proof of the exact statement and
  explicit axioms; otherwise identify it as open or unresolved. An inability to
  select or solve an open problem is not evidence of a LeanForth defect.

## Track T: Lean-compatible theorem proving and full Mathlib

### T1. Development foundation — partial

Evidence: repository, MIT license, pinned Lean and local Gforth exist. [Versions](../development/VERSIONS.md) records Ubuntu/WSL and a 2026-10-30 smoke CI run for commit `44ca571`; it does not establish current CI status. Clean installation and portability remain open.

- **T1.1:** Record a fresh read-only `scripts/check-env.sh` inventory and tool/fixture hashes; identify missing tools. Accept when another developer can reproduce the recorded commands without credentials or hidden setup.
- **T1.2:** Make clean Ubuntu/WSL setup reproducible, pin and authenticate artifacts where feasible, document prerequisites and missing tools. Accept only after a clean-environment run; report any unavailable host separately.
- **T1.3:** Run actual smoke, negative harness and representative suites in CI with explicit tool versions; document exact run/commit and failures. Add other hosts only after real execution, and resolve the documented CI dependency warning.
- **T1.4:** Define the Forth-2012 host boundary and test stack/error behavior on supported Gforth versions. Accept with a portability matrix, limitations and documented public words.

### T2. Terms, names and universes — partial, untrusted

Evidence: bounded arenas, names, symbolic universes and generation handles exist; raw consumers and review remain open. Depends on T1 host boundary.

- **T2.1:** Specify representation invariants, ownership, bounds, lifetime/generation and rollback in an ADR; enumerate raw consumers. Accept after human kernel review and tests for stale/replaced handles and overflow.
- **T2.2:** Separate concrete universe values from symbolic indices; keep the unsafe symbolic inference draft excluded until isolation and review. Accept with cross-representation rejection and regression tests.
- **T2.3:** Implement canonical names, levels and term DAGs with validated references and portable deterministic serialization. Accept with round trips, corruption, invalid references, depth and resource-limit tests across supported hosts.
- **T2.4:** Compare representative level/name operations with pinned Lean, including universe parameters and boundary cases; record unsupported forms and discrepancies. Human review precedes trusted use.

### T3. Scope and substitutions — partial, untrusted

Evidence: finite tagged term and simultaneous universe substitution comparisons include 48 cases each; this is not a correctness proof. Depends on T2 invariants.

- **T3.1:** Specify binder indices, scope, capture avoidance and term/universe substitution, including error and allocation behavior. Review the rules and identify supported fragments.
- **T3.2:** Test open terms, nested binders, shadowing, malformed graphs, budget exhaustion and rollback; add generated differential comparisons with pinned Lean and reproducible seeds.
- **T3.3:** Integrate reviewed operations with validated handles and serialization; accept only when invariants and negative tests hold and human review approves the kernel boundary.

### T4. Definitional equality — partial, untrusted

Evidence: beta-aware conversion and selected symbolic universe identities exist; many Lean equivalences are unknown. Depends on T2–T3.

- **T4.1:** Specify normalization and conversion rules for the first fragment, including universe equality, termination/resource behavior and an explicit unknown result; compare rules with Lean.
- **T4.2:** Add beta, binder and universe cases plus deliberately unequal, malformed and exhausted examples; require no unsupported or unknown case to return equality.
- **T4.3:** Differential-test against pinned Lean on reproducible closed and open examples; investigate each mismatch and obtain human review before inclusion in the checker. Extend eta, proof irrelevance and declaration reduction only under later reviewed rules.

### T5. Small trusted checker — not complete

Evidence: a tagged diagnostic checks a polymorphic identity pair without creating a theorem; application inference has 18 finite Lean comparisons. Depends on T2–T4; this is the shared proof gate for P5.

- **T5.1:** Approve an ADR for the minimal Lean-compatible sorts/variables/Pi/lambda/application fragment, environment and trusted boundary; specify assumptions, explicit empty or reviewed axiom policy and failure states.
- **T5.2:** Before enabling acceptance, add a constructed valid identity proof and invalid application/type/scope tests, malformed encodings, resource exhaustion and pinned Lean comparisons.
- **T5.3:** Implement and human-review the small checker; only a successful complete check emits kernel-accepted, with proof/type identity and assumptions. Unsupported constructs and failed checks cannot register declarations.
- **T5.4:** Independently replay a durable proof artifact and its negative mutations; document trusted code, limitations and commands. T5 acceptance is this fragment only, not full Lean compatibility.

### T6. Lean NDJSON importer — preview only

Evidence: bounded Python preview retains some constants/definitions and reports local dependency/order/arity observations; dependencies and proofs are not validated. Fixture preparation can precede T5; checked import depends on T5 and the relevant T8 rules.

- **T6.1:** Pin exporter/schema, Lean version, source and fixture hashes; enumerate every supported/unsupported record and field. Test truncation, duplicates, malformed JSON, limits and version mismatch.
- **T6.2:** Build an untrusted streaming decoder into architecture-independent validated term candidates; test invalid references, cycles, ordering, oversized input and deterministic diagnostics.
- **T6.3:** Feed supported candidates to the checker in dependency order, checking types, bodies, universe arity and axiom policy; transactionally reject invalid or unsupported declarations. Human review of importer and certificates is required.
- **T6.4:** Re-export or stably serialize supported fixtures and compare declaration types, assumptions and verdicts with pinned Lean; report supported counts and every unsupported reason. Parsing alone never means acceptance.

### T7. Lean checker compatibility corpus — selected cases only

Evidence: selected differential tests and direct Lean constant/universe oracles exist; LeanForth does not yet compare those constant cases and no official corpus pass is demonstrated. Harness preparation depends on T1; checker comparisons depend on T5–T6 and relevant T8 features.

- **T7.1:** Pin Lean revision, official checker corpus and export artifacts; make a reproducible manifest of expected valid, invalid and unsupported cases and their hashes.
- **T7.2:** Automate independent verdict, type and axiom comparisons, including mutated invalid inputs; fail CI on false acceptance and classify unknown, unsupported, mismatch and resource failure separately.
- **T7.3:** Add constant/universe oracle comparisons as implementation permits; triage every discrepancy and expand coverage feature by feature without masking unsupported cases.
- **T7.4:** Run the complete pinned corpus with reproducible resource metrics; publish denominators and results. A corpus claim requires an actual recorded run, not extrapolation from samples.

### T8. Lean declaration features — candidate index only

Evidence: untrusted signature index and draft constant-environment ADR do not check declaration validity. Depends on T5 and T6; T7 supplies differential evidence throughout.

- **T8.1:** Review environment, names, universe instantiation and dependency rules; implement constants and definitions with checked types/bodies and controlled reduction. Test missing, cyclic, duplicate and ill-typed declarations against Lean.
- **T8.2:** Add reviewed polymorphism, normalization and Lean conversion behavior incrementally; test arity, constraints, eta and proof irrelevance, with explicit unsupported results until implemented.
- **T8.3:** Specify and review inductive declarations, positivity, constructors and recursors; test valid and malformed/mutated declarations and eliminations against Lean before accepting them.
- **T8.4:** Add quotients and all remaining pinned Lean kernel declaration/expression features needed by the complete corpus; audit axiom dependencies and review each trust expansion. Maintain a feature-gap ledger rather than treating examples as complete coverage.

### T9. Full Mathlib — not imported or independently checked

Evidence: no full-library import/check or usable library exists. Depends on T6–T8; corpus and scalability work should begin earlier. The target is all Mathlib and transitive Lean/Std dependencies, not a curated slice or a single frozen release.

- **T9.1:** Pin a complete Mathlib release, Lean/Std, exporter and transitive dependencies; manifest every declaration, source, hash and required axiom. Obtain human approval for the exact audited allowlist; reject others.
- **T9.2:** Import in dependency order and independently check every declaration; report total/checked/rejected/unsupported/resource-failed and diagnose all gaps, including dependency failures. Never replace a missing proof with an axiom.
- **T9.3:** Make the complete checked library practically usable: indexed name/type search, dependency and assumption inspection, application from proof authoring and Forth verification, with repeatable representative workflows.
- **T9.4:** Measure complete-corpus time, memory and storage on recorded hardware; address streaming, sharing and caching without weakening checks. Accept a release only after a full reproducible check, no unexplained omissions or false acceptances, reviewed assumptions and documented capacity.
- **T9.5:** Establish repeatable upgrade/recheck procedures for subsequent Lean/Mathlib releases and changed dependencies; compatibility with a pinned snapshot is evidence toward the continuing full-library goal.

### T10. Native proof authoring — future

Evidence: term building, elaboration and tactics are not yet a user workflow. Basic work may follow T5; library-assisted work depends on T8–T9.

- **T10.1:** Provide documented Forth words to build typed terms and submit them to CHECK; demonstrate accepted identity and rejected invalid proof with source IDs and durable references.
- **T10.2:** Add versioned local NDJSON/JSON-RPC schemas, deterministic structured errors and replayable CLI examples; validate malformed requests and ensure only checker-derived statuses claim acceptance.
- **T10.3:** Implement untrusted metavariables, unification, elaboration, tactics and rewriting incrementally; every generated term returns through the checker, with adversarial invalid-output tests.
- **T10.4:** Render proof steps with derivation references and clearly tagged reconstructed/LLM explanations; external notation adapters require semantic review and ambiguity tests. Publish user and LLM manuals.

## Track P: provably correct executable Forth

### P1. Contracts and assumptions — partial

Evidence: clamp has a mathematical contract and runtime assumptions. May proceed alongside T1–T3.

- **P1.1:** Specify CHECK/VERIFY/RUN status and receipt semantics, stack effects, pre/postconditions, integer domain and failure behavior; distinguish source, host and compiler assumptions.
- **P1.2:** Define typed contract/IR and versioned artifact schemas with source IDs; include memory, effects and overflow as explicit unsupported cases until modeled. Human review certificate formats.
- **P1.3:** Write positive and violated-contract examples, machine-readable diagnostics and user documentation; require assumptions and model version in each proposed verification result.

### P2. Tested Forth example — partial

Evidence: host clamp plus five additional host-cell examples have finite tests; these tests do not prove the words correct. Depends on P1 for a formal contract.

- **P2.1:** Make clamp's stack effect, bounds behavior, integer representation and host assumptions explicit; test boundary, reversed-bound and stack-error cases.
- **P2.2:** Run reproducible finite tests on supported hosts and publish versioned inputs and results; distinguish runtime testing from proof.
- **P2.3:** Give the additional examples formal contracts and select at least one as an acceptance target for the shared checker and future verifier; reject a violated contract.

### P3. Formal execution model — partial

Evidence: Lean reference proves clamp properties and successful modeled frame preservation; its relation to actual Forth is an assumption. Depends on P1–P2.

- **P3.1:** Specify a small pure Forth subset, stack, cells, overflow, failure and termination semantics; document excluded words and host assumptions.
- **P3.2:** Formalize transition and contract semantics in the pinned Lean reference; prove clamp and composition properties including failure/frame conditions.
- **P3.3:** Review the reference model against documented Forth behavior and maintain a mapping from each supported word to implementation and tests; do not claim general Forth semantics.

### P4. Model/runtime comparisons — finite evidence

Evidence: finite model/host comparisons, including 1,470 nested-clamp and 784 monotonicity cases, do not establish runtime equivalence. Depends on P2–P3.

- **P4.1:** Define observable stack, errors and memory for comparisons, including numeric boundary and host-width assumptions.
- **P4.2:** Run pinned model versus actual Forth over exhaustive small domains and reproducible generated cases; test mismatches, invalid input and multiple supported hosts.
- **P4.3:** Record disagreements and untested domains; use results to refine P3 with review, without describing testing as a proof of the host.

### P5. Shared proof kernel — blocked on T5

Evidence: no trusted LeanForth checker exists and no source program has a LeanForth-checked correctness proof.

- **P5.1:** Map program propositions and semantics into T5 terms; specify how a certificate binds program, specification, semantics version and assumptions. Review the encoding and certificate format.
- **P5.2:** Construct a real proof for the smallest supported pure program and check it with T5; reject mutated programs, specifications, proofs and unapproved assumptions.
- **P5.3:** Replay the artifact independently and report source verification separately from execution/backend validation; publish a reproducible end-to-end example. Larger logic features may require T8.

### P6. Forth program representation — partial reference model

Evidence: a small Lean push/duplicate/add language has a proved stack-depth bound; an abstract bounded-memory model is separate from the interpreter. Depends on P1 and P3; checked claims depend on P5.

- **P6.1:** Define a versioned typed IR and translation for a bounded pure subset, including word identity, stack types, failure and source locations; reject unsupported or dynamic Forth explicitly.
- **P6.2:** Connect the IR to reference semantics and compare model and host on positive, underflow, overflow and malformed programs; use P4 methodology.
- **P6.3:** Add control flow, then bounded memory and frame/alias effects in reviewed increments; prove model properties and test interpreter correspondence for each increment.

### P7. Verification conditions — partial reference only

Evidence: Lean reference proofs cover weakest preconditions, stack depth and sequential failure; an untrusted Forth depth diagnostic matches 1,093 finite cases. Depends on P3/P6; acceptance of generated proofs depends on P5.

- **P7.1:** Specify VC rules and their soundness statement against the versioned semantics, including termination, error paths and assumptions; review bypass and certificate boundaries.
- **P7.2:** Implement an untrusted generator for straight-line pure IR, emitting explicit obligations and proof references; compare with the reference and test missing, invalid and unsolved obligations.
- **P7.3:** Submit every obligation and generator soundness connection to the shared kernel; reject partial proofs. Add branching, invariants and bounded memory only with corresponding reviewed rules and negative tests.

### P8. User-facing verifier — not implemented

Evidence: no general specify/prove/check workflow exists. Depends on P5–P7 and T10.2.

- **P8.1:** Deliver scriptable specification, CHECK and VERIFY commands and versioned schemas with stable error codes; validate malformed requests and unsupported features.
- **P8.2:** Provide a real end-to-end pure example with checked source proof, replayable receipt, source IDs and explicit assumptions; reject a broken contract and a tampered artifact.
- **P8.3:** Document supported words, semantics, manuals and limitations; integrate proof steps and honest RUN results without suggesting backend verification.

### P9. Verified execution and compilation — future

Evidence: source-to-runtime correspondence and compiler assurance are absent. Depends on P3–P8; runtime tests can start with P4.

- **P9.1:** Define execution and code-generation mappings for the supported IR and identify host, integer, I/O and runtime assumptions; review compiler/FFI boundary.
- **P9.2:** Execute checked source examples on Gforth with optional runtime assertions; compare model, interpreter and generated code on valid and invalid inputs. Receipts identify runtime-tested versus unvalidated backends.
- **P9.3:** Develop and review a proof of correspondence or translation validation for a precisely bounded subset; test adversarial compiler outputs. Until established, compiled behavior remains an explicit assumption.
- **P9.4:** Extend supported effects and platforms only with specified semantics, evidence and documentation; do not imply arbitrary Forth or native code is verified.

### P10. Larger executable programs — future

Evidence: general programs, connected memory, tensor contracts and CPU execution remain open. Depends on P6–P9; tensor contract design can run in parallel.

- **P10.1:** Verify a nontrivial bounded array operation against explicit pre/postconditions, memory ownership, frame and alias rules; test bounds and failure cases and document runtime assumptions.
- **P10.2:** Specify tensor dtype, shape, stride, layout, ownership/lifetime, aliasing, placement, effects and numeric semantics; implement a portable tiny CPU reference and mismatch/edge-case tests.
- **P10.3:** After user approval of any new runtime dependency, add a CPU provider with reviewed FFI contracts and fallback; compare to an independent oracle across layouts, zero sizes, overflow, NaNs and documented tolerances.
- **P10.4:** Benchmark reproducibly with hardware, library versions and seeds; report floating-point error and external backend assumptions. Consider optional accelerators only after CPU evidence; GPU and numerical libraries remain outside the trusted kernel.

## Current evidence and reporting discipline

The local inventory command `python3 scripts/code-inventory.py` on 2026-11-01 reported 32 Forth source/experimental files (3,041 physical lines), 74 Forth test/support files (4,936), 43 Lean reference/test files (1,732), 44 Markdown files (2,782), five NDJSON fixtures (138), seven other project files (245), and 39 other test/support files (2,734). Counts include untracked non-ignored files and include comments/blank lines; they are not coverage or proof of completion. The inventory was taken before this roadmap was created.

This roadmap review ran no test suites, no environment inventory and no CI query. The last documented CI result and tool versions are historical, as noted in T1. Full NDJSON import, official corpus acceptance, full Mathlib, a trusted checker, a checked verifier and source-to-runtime correspondence remain unestablished. At each subsequent meaningful implementation milestone update [project progress](PROJECT_PROGRESS.md) with both ten-milestone tracks, their shared kernel overlap, NDJSON state, fresh inventory, actual checks and limitations.

# LeanForth project progress

Snapshot: 2026-11-02, at commit `fc558cc` on `main` (previous full
snapshot 2026-11-01). These are milestones, not estimates of percentage
complete. Prototype success is not theorem acceptance. Update this report
after each meaningful milestone, with the inventory from
`python3 scripts/code-inventory.py`. The two paths share the eventual
checked proof infrastructure.

The intended deliverable is a finished, usable LeanForth system, including
Lean/Mathlib-compatible theorem proving, use of the full Mathlib library,
and verification of executable Forth programs. The experimental work
reported below is an interim development stage, not the project's final
scope or quality target.

**In one paragraph.** LeanForth still has **no proof checker**: it has
never accepted or rejected a declaration. On 2026-11-02 the code base was
rebuilt on a small Forth library (all modules on named records, one outcome
vocabulary, the superseded variants retired, each module loading its own
dependencies); a Forth reader now decodes **all** of the pinned Mathlib
export; per-task contexts and a worker pool exist for parallel checking;
the owner approved the **rules** of the first checker (ADRs 0011, 0003
Amendment 1 and 0012), whose code is not written; the program track gained
a receipt format, a program IR whose Lean model proves the six example
words' IR equal to their reference models, and a Forth-to-IR reader; and a
term printer prints terms as Lean does. A [user guide](../user/USER_GUIDE.md)
with three-form examples and diagrams was started.

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
| T1 foundation | 1 | 3 | 0 |
| T2 terms, names, levels | 0 | 4 | 0 |
| T3 scope and substitution | 0 | 3 | 0 |
| T4 equality | 1 | 2 | 0 |
| T5 checker | 1 | 2 | 1 |
| T6 NDJSON | 0 | 3 | 1 |
| T7 Lean corpus | 0 | 3 | 1 |
| T8 declarations | 0 | 2 | 2 |
| T9 full Mathlib | 0 | 2 | 3 |
| T10 native authoring | 0 | 1 | 3 |
| **Theorem track, 39 tasks** | **3** | **25** | **11** |
| P1 contracts | 0 | 3 | 0 |
| P2 Forth examples | 0 | 3 | 0 |
| P3 execution model | 2 | 1 | 0 |
| P4 model/runtime comparisons | 0 | 3 | 0 |
| P5 shared kernel | 0 | 1 | 2 |
| P6 program representation | 0 | 3 | 0 |
| P7 verification conditions | 0 | 2 | 1 |
| P8 user verifier | 0 | 0 | 3 |
| P9 execution and compilation | 0 | 1 | 3 |
| P10 larger programs | 0 | 0 | 4 |
| **Program track, 32 tasks** | **2** | **17** | **13** |

The high number of in-progress tasks reflects broad acceptance criteria, not
completion of their component work. Split tasks further when an individual
change can be reviewed and accepted independently; do not mark a broad task
done because a test fixture or untrusted diagnostic works.

**Status changes in this snapshot**, each judged against the task's own
acceptance text:

| Task | Now | Evidence |
| --- | --- | --- |
| T1.3 CI suites | done | CI runs `make test` (smoke, the negative test harness and every unit suite) on Ubuntu's Gforth 0.7.3 and `make check` on pinned Gforth 1.0.0 and Lean 4.35.0 with the versions printed; runs are recorded below; the Node.js 20 warning of `actions/checkout@v4` went with the move to pinned v7.0.1, and the latest runs show no warning |
| T4.1 conversion rules for the first fragment | done | [ADR 0011](../adr/0011-definite-rejection.md) (cautious equality, universe equality by identity, values or a witness, explicit *unknown*, fuel and room outcomes, each rule cited to Lean 4.35.0's kernel source) and [ADR 0003 Amendment 1](../adr/0003-conversion.md) (binders whose domains differ), both approved by the owner on 2026-11-02 (gate answers G1–G7); Lean's answers checked by `make reference-first-checker` and `make reference-binder-domains` |
| T5.1 ADR for the minimal fragment | done | ADR 0011's scope, failure states and empty axiom list, and [ADR 0012](../adr/0012-checked-environment.md)'s checked environment, approved by the owner (G1–G11); the code needs its own gate approval with test results |
| T9.1 pin Mathlib | in progress | Mathlib `v4.35.0` (commit `56a0058`), its dependencies' revisions, the export's SHA-256 and the denominator of 729,263 constants recorded; per-declaration manifest and the exact allowlist statements remain |
| T9.4 Mathlib time and memory | in progress | Export measured (6 min 33.5 s, 13.8 GB peak); the Forth reader decodes it in 1 min 49 s and 17 MB; [scale assessment](SCALE_ASSESSMENT.md); no checking yet |
| P3.1 small Forth subset | done | [Program IR 0.1](../programming/PROGRAM_IR.md): straight-line words, `IF`/`ELSE`/`THEN`, `EXIT`, fuel-bounded `BEGIN`/`WHILE`/`REPEAT`, 38 primitives over wrapping signed cells of any width, explicit failures and fuel; excluded words and host assumptions listed |
| P3.2 Lean transition and contract semantics | done | `tests/reference/program-ir.lean` defines the IR's semantics and proves the six words' IR equal to their reference models for every cell width and every stack below the inputs, reaches every failure and refutes two wrong programs; clamp contract, composition and frame properties in the earlier references |

These five *done* tasks are the first in the report; the owner may wish to
confirm the readings of T4.1, T5.1, P3.1 and P3.2, which rest on approved
designs and Lean proofs rather than on LeanForth code.

## Near-term queue and plan phase 1

| Item | State |
| --- | --- |
| Q1–Q4 | Done earlier, untrusted experimental preparation |
| Q5 Lean comparison | In progress: Lean's verdicts on 60 kernel cases and 27 broken source copies are pinned ([expected results](../reviews/FIRST_CHECKER_EXPECTED.md)); LeanForth's answers wait for the checker |
| Q6 checked environment design | Design approved (ADR 0012, G8–G11); implementation not started |
| Q7 first independently checked declaration | Not started: rules approved, code not written |
| Q8 parallel program path | In progress: receipt schema 0.1, IR 0.1 with its Lean model and reader (plan 2.5.1–2.5.3), the IR interpreter's three-way comparison (2.5.4), the verification-condition generator v0 (2.5.5) and the first clamp receipt (2.5.6) are done; the reader ([parser]) and receipt format ([format]) await the owner's approval |
| Q9 consolidate experiments | Done 2026-11-02: 28 superseded modules and 91 test files retired with the owner's approval |
| Q10 refactor onto `src/lib` | Done (2026-11-02): every core and kernel module keeps its state in the per-task checker context (34 context members: stores, walk records, frames and module records; no global state left) and returns the shared outcomes (the 49 per-module status aliases are gone); cross-module field writes became stack interfaces; every module `require`s its direct dependencies; *exhausted* (out of fuel) and *full* (out of room) are separate; `src/core/` plus `src/kernel/` have about 690 words, none over ten lines (`make forth-metrics`), against a baseline of 218 words, 23% over ten lines and 225 globals. Randomized differentials against the previous code show no difference. Follow-ups: choose one of the three recursion patterns; convert the loader, the program reader and the NDJSON counter's state |

## Theorem proving and Mathlib

| Milestone | Status and evidence / remaining work |
| --- | --- |
| 1. Development foundation | 1 of 4 done (T1.3). Pinned Gforth 1.0.0 and Lean 4.35.0, CI on two Gforth versions, timeouts, `sorry`-proof Lean checks, documentation link and portability checks. Clean-machine reproduction (T1.1, T1.2) and a portability matrix (T1.4) remain. |
| 2. Terms, names and universes | In progress: bounded 64-entry stores on the library's `store:` records, handles that detect stale references, symbolic Sorts kept apart from concrete ones, which no checker pass accepts (ADR 0007; the unsafe draft that mixed them was retired), structured names. Human review of the representation and serialization remain. |
| 3. Scope and substitutions | In progress: shift, instantiation and universe substitution passes compared with Lean on finite tables (80, 25 and 48 cases and others). General specification and review remain. |
| 4. Definitional equality | 1 of 3 done (T4.1, rules approved). The experimental conversion compares after beta reduction and answers *unknown* where it cannot decide; unfolding, eta and proof irrelevance are later phases. No pass answers *rejected* yet. |
| 5. Small trusted checker | 1 of 4 done (T5.1, rules and design approved). Expected results: 60 cases (14 must be accepted, 28 rejected, 1 invalid, 9 unknown, 8 unsupported) checked against Lean. The checker code, its failure-path suite, replay and the code gate are not started. |
| 6. Lean NDJSON importer | In progress: the Forth reader decodes every record kind of lean4export 3.1.0 and all of Mathlib (below). Staging into the stores, feeding the checker and comparing verdicts remain. |
| 7. Lean checker compatibility corpus | In progress: selected differential tables and the first checker's expected-results table; no official corpus run. |
| 8. Lean declaration features | In progress: the checked environment is designed (ADR 0012, per-declaration universe scope); candidate signatures remain unchecked assumptions; inductive types, recursors and quotients are decoded by the reader but not checked. |
| 9. Full Mathlib | In progress (T9.1, T9.4): denominator pinned, export and reading measured; nothing imported into stores or checked. |
| 10. Native proof authoring | In progress (T10.1 only in part): terms can be built with internal Forth words and printed as Lean prints them — the term printer and its side table (plan 2.4.2–2.4.3) agree with Lean's own printing on 50 cases and the five fixtures ([printing terms](../user/TERM_PRINTER.md)); no user syntax, elaboration, tactics or proof outlines. |

## Provably correct executable Forth

| Milestone | Status and evidence / remaining work |
| --- | --- |
| 1. Contract and assumptions | In progress: [receipt schema 0.1](../programming/PROGRAM_RECEIPTS.md) keeps CHECK, VERIFY and RUN apart and requires runtime, cell, Lean, reader and floating-point assumptions; three valid and four invalid examples and 30 mutations are tested; the format awaits the owner's *[format]* approval. |
| 2. Tested Forth example | In progress: six example words with finite tests; formal contracts for the five words other than clamp remain (plan 1.5.3). |
| 3. Formal execution model | 2 of 3 done (P3.1, P3.2): IR 0.1 and its Lean semantics. Remaining: review the model against documented Forth behaviour (P3.3). |
| 4. Model/runtime comparisons | In progress: finite comparisons of the words with Lean models (686 clamp triples, 1,296 memory cases and others); the IR interpreter (`src/program/ir-run.fs`) agrees with the host words and with Lean's evaluation of the model on 5,152 cases (5,092 also run on the host) and 300 random IR programs (2.5.4); testing is not proof. |
| 5. Shared proof kernel | In progress only through the theorem track's rules; no LeanForth checker exists. The first program fact checked by LeanForth arrives with data types (phase 5, owner answer OQ-5). |
| 6. Forth program representation | In progress: the IR is versioned and the reader translates the example words with source locations, refusing anything outside IR 0.1; stack types, host comparison and memory remain. |
| 7. Verification conditions | In progress: Lean references for weakest preconditions and stack depth; generator v0 (`scripts/program_vc.py`, untrusted) turns IR plus a contract into Lean obligations: clamp, checked add, checked abs and in-range discharged by Lean, three wrong contracts refuted, gcd and factorial unsupported until loop invariants (4.4.1). The first receipt (clamp) says *checked by the Lean reference, not by LeanForth*. |
| 8. User-facing verifier | Not started. |
| 9. Verified execution/compilation | In progress only for runtime testing; no source-to-runtime correspondence. |
| 10. Larger executable programs | Not started. The track's destination is now most of the Forth-2012 Core word set, in five stages ([owner decision](OWNER_DECISIONS.md#program-track-goal-most-of-forth-2012-core-2026-11-02-night)). |

## Where the two tracks overlap

- **One checker.** Program proofs are to be checked by the same LeanForth
  checker as theorems (P5 depends on T5); until then program proofs are
  checked by Lean and receipts say *checked by the Lean reference, not by
  LeanForth*.
- **One outcome vocabulary and library.** The IR reader, the NDJSON reader,
  the printer and the checking passes all report `src/lib/outcome.fs`
  outcomes and use the same records.
- **One axiom policy.** Receipts accept only `propext`, `Classical.choice`
  and `Quot.sound` for Lean-checked proofs; the first checker accepts none.
- **One parallel machinery.** Contexts and the job pool serve both.

## NDJSON support

| Measure | Value | Denominator |
| --- | --- | --- |
| Record kinds of lean4export format 3.1.0 decoded by the Forth reader | 24 of 24 (100%), plus the 3 element kinds of inductive blocks | the format's record kinds ([reader guide](../development/NDJSON_READER.md)) |
| Records of the pinned Mathlib export decoded and checked for shape and references | 110,895,826 of 110,895,826 (100%), field for field equal to Python's `json` module | lines of export SHA-256 `18448e5d…59c6` |
| Expression nodes staged into LeanForth's stores | 0% of Mathlib's 105,894,257; only test fixtures, through a test-only Python bridge | stores hold 64 entries |
| Declarations checked by LeanForth | **0 of 729,263 (0%)** | constants of the pinned Mathlib export with its dependencies |
| Share of Mathlib the first checker could accept | **unknown** | not measured; nearly every declaration depends on inductive types, which the first checker reports as *unsupported* |
| T6 importer acceptance tasks done | 0 of 4 | roadmap T6 |

Reading is not checking: a decoded record is input for the checker, never
a checked declaration. The reader is untrusted and fail-closed; it reads
the whole export in 1 min 49 s and 17 MB with `gforth-fast` (1 min 43 s
before the fixes of its independent review, which found eight issues, all
fixed; its fuzzer then found no discrepancy in 12,000 files). A binary
quick-import is not built: reading is small next to exporting (6.5 min) and
checking (estimated hours). The Python preview remains as a second reader
for tests. Open: the reader and the preview classify a few malformed and
limit cases differently; plan item 3.2.1 settles one classification
through the import review gate.

## Full Mathlib

- **Acceptance-task completion: 0 of 5 T9 tasks done** (2 in progress).
- **Independently checked declarations: 0 of 729,263** in the full export
  of Mathlib `v4.35.0` (commit `56a0058`) with its dependencies, sha256
  `18448e5d…59c6` ([measurements](../development/measurements/mathlib-2026-11-02/README.md)):
  184,355 definitions, 517,916 theorems, 2,913 opaque declarations, 4
  axioms, 4 quotient declarations, 7,046 inductive types, 9,863
  constructors and 7,162 recursors; 105.9 million expression nodes; up to 30
  universe arguments; expression depth up to 1,221.
- No local reference-checker baseline exists (nanoda stopped at the 16 GB
  memory limit set to protect the machine).

## Parallel checking groundwork

- **Done in the library** ([ADR 0009](../adr/0009-reentrant-state-and-parallel-checking.md),
  accepted): per-task contexts (`src/lib/context.fs`) that modules declare
  their state into, with owners — a context belongs to one job until it is
  waited for; a worker pool (`src/lib/task.fs`) on Gforth 1.0's threads,
  Gforth 0.7.3's cooperative tasker or a serial path, with stack-overflow
  detection, compared with serial runs for 1, 2 and all workers.
- **Measured** (Gforth 1.0, Ryzen 5 7600X, 12 threads, WSL2): 12 workers
  ran 12 test jobs 5.7–6.3 times faster than one task (2 workers
  1.9–2.0×, 6 workers 4.4–5.0×); over 39,984 jobs the process stayed at
  about 9.5 MB. These are test jobs, not checker workloads.
- **Done in the checker** (ADR 0009 step 3, 2026-11-02): all 24 core and
  kernel modules keep their state in the context; 2 and 8 contexts
  interleaved step by step, and checker trials run as jobs (14,400 on
  Gforth 1.0 threads, 2,400 each on 0.7.3's cooperative tasker and the
  serial path), give the serial results. Reaching state through the
  context costs about 13% (`gforth`) and 23% (`gforth-fast`) on a fixed
  workload; a faster member accessor is proposed. Each context also holds
  a diagnostic record of why a check failed (reason code, site, two
  numbers; first failure wins), documented in
  [DIAGNOSTICS.md](../programming/DIAGNOSTICS.md).
- **Not done:** the scheduler, the single publisher and the shared
  environment (ADR 0012; implementation in progress). The input stores are
  per context today; ADR 0012 wants one shared read-only input (plan task
  7.2.1). Roadmap C1 and C2 are in progress, C3 and C4 partly.

## Documentation

New this snapshot: a [user guide](../user/USER_GUIDE.md) (what LeanForth is
and is not, trust boundaries, reading paths for each audience),
[concepts in three forms](../user/CONCEPTS.md) (eleven concepts, each as
mathematics, LeanForth Forth that was run on Gforth 1.0 and 0.7.3, and Lean
checked with the pinned Lean), [workflow diagrams](../user/WORKFLOWS.md)
for checking a theorem and verifying a program,
[running the checks](../user/RUNNING_THE_CHECKS.md),
[a page for AI tools](../user/AI_TOOLS.md), and the
[architecture](../development/ARCHITECTURE.md) with diagrams of the layers,
tasks and contexts, the principal records and one stored term. The six
Mermaid diagrams were rendered with the Mermaid command-line tool already
installed on the development machine (no install); their rendering on
GitHub is still to be looked at. The examples are not run by `make test`
yet. Planned: manuals per audience as the features arrive, a limits
document (roadmap D3), and diagrams of outcome flow and parallel checking.

An [opt-in profiling wrapper](../development/PROFILING.md) measures elapsed
time and process peak RSS for an existing finite workload; it does not
measure checker performance.

## Inventory and testing

Run `python3 scripts/code-inventory.py` for current counts of tracked and
untracked, non-ignored files. Counts are physical lines, including comments
and blank lines, and are not a coverage percentage. Forth source is counted
per `src/` folder ([layout](../../src/README.md)); none of it is a trusted
checker. See the [testing strategy](../development/TESTING_STRATEGY.md).

Inventory at this snapshot (`python3 scripts/code-inventory.py`):

| Category | Files | Physical lines |
| --- | ---: | ---: |
| Forth source, `src/lib/` | 12 | 1,760 |
| Forth source, `src/core/` | 10 | 882 |
| Forth source, `src/kernel/` | 14 | 1,933 |
| Forth source, `src/import/` | 3 | 1,048 |
| Forth source, `src/program/` | 4 | 549 |
| Forth source, `src/present/` | 8 | 1,185 |
| Forth source, `src/main.fs` | 1 | 29 |
| Forth tests and support | 108 | 10,430 |
| Other test code and support (Python, shell) | 55 | 6,100 |
| Lean references and tests | 83 | 5,950 |
| NDJSON fixtures | 5 | 138 |
| Markdown documentation | 85 | 13,008 |
| Other project files (Makefile, scripts, schemas, workflow, measurement data) | 44 | 3,378 |

All Forth source together: 52 files, 7,386 lines, of which `src/core/` and
`src/kernel/` — the data model and the checker under development — are
882 + 1,933 = 2,815 lines.

## Verification and CI

Run for this snapshot, in an isolated worktree at `fc558cc` plus these
documentation changes, all passing: `make test` with Gforth 1.0.0 (7.3 s)
and with Gforth 0.7.3; `make check` with pinned Gforth 1.0.0 and Lean
4.35.0 (87 s at `6f5bfb9`, 100 s at `fc558cc`); the 11 Forth examples of the
[concepts page](../user/CONCEPTS.md) on both Gforth versions and its 10
Lean examples with the pinned Lean, each output compared with the page.

CI on `main` (`.github/workflows/ci.yml`: `make test` on Ubuntu's Gforth
0.7.3, `make check` on the pinned tools): the last runs listed when this
snapshot was written all passed — [41555705430](https://github.com/pmilford/LeanForth/actions/runs/41555705430)
for `6f5bfb9` (term printer), [41555267483](https://github.com/pmilford/LeanForth/actions/runs/41555267483)
(fuel-first rule), [41555019582](https://github.com/pmilford/LeanForth/actions/runs/41555019582)
(program-track goal), [41553978053](https://github.com/pmilford/LeanForth/actions/runs/41553978053)
(receipts, IR and its reader) and [41553540427](https://github.com/pmilford/LeanForth/actions/runs/41553540427)
(worker pool), each in about 2.5 minutes; no run of `fc558cc` (the reader's
review fixes) was listed yet. History: 15 consecutive Smoke
runs failed on 2026-11-01 until [41379263819](https://github.com/pmilford/LeanForth/actions/runs/41379263819);
the Codex-era tag `pre-claude` passed [41476841907](https://github.com/pmilford/LeanForth/actions/runs/41476841907);
the current workflow's first run, [41504003139](https://github.com/pmilford/LeanForth/actions/runs/41504003139),
was the first CI run of the pinned-Lean comparisons.

## Limitations

- No LeanForth checker: nothing has been accepted or rejected, and every
  "ok" in the experiments is an untrusted diagnostic. When the checker
  exists, every accepted result will be labelled *experimental — not
  independently audited* until an outside Lean expert audits it.
- Stores hold 64 entries and constants at most 8 universe arguments;
  Mathlib needs millions of entries and 30 arguments. The rebuild passes
  recurse on the host's return stack (about 1,200 cells at worst today).
- The program track's proofs are about the IR's Lean semantics, checked by
  Lean; that Gforth runs the words as the IR says, and that the reader
  translates faithfully, are tested, not proved.
- Only Lean 4.35.0 exports in format 3.1.0 are read; only Linux/WSL with
  Gforth 1.0.0 and 0.7.3 is tested.

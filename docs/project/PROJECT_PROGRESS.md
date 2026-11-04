# LeanForth project progress

Snapshot: **2026-11-03**, at commit `d6233af` on `main` (previous snapshot
2026-11-02 at `fc558cc`). These are milestones, not estimates of percentage
complete. Prototype success is not theorem acceptance. Update this report
after each meaningful milestone, with the inventory from
`python3 scripts/code-inventory.py`. The two paths share the eventual
checked proof infrastructure.

The intended deliverable is a finished, usable LeanForth system, including
Lean/Mathlib-compatible theorem proving, use of the full Mathlib library,
and verification of executable Forth programs. The experimental work
reported below is an interim development stage, not the project's final
scope or quality target. The owner's rule since 2026-11-03: LeanForth must
give **exactly Lean 4.35.0's verdicts** — an *unknown* where Lean decides
is a gap to close, never a feature — and match or beat Lean's one-thread
speed before parallelism adds more.

## Where things stand, in plain words

**LeanForth can now check its first declarations, experimentally.** Given
a small definition or theorem — built from universes, variables, functions,
"for all" and earlier checked declarations — it decides *accepted*,
*rejected*, *unknown*, *unsupported* or *invalid*, in the same order and for
the same reasons as Lean's kernel. On the 62 test cases of its table
(the five pinned examples plus deliberately broken or out-of-scope copies,
each checked by pinned Lean) it gives Lean's answer every time: 14
accepted, 28 rejected with Lean's kind of error, 11 unknown, 8 unsupported,
1 invalid. Nothing it says is trusted yet: the declaration check and the
checked environment it publishes into are still in their review gates, and
every acceptance is labelled *experimental — not independently audited*.

**What it cannot do yet.** It cannot check anything that needs a definition
unfolded, a data type (natural numbers, lists, equality), a number literal
or a structure — which is nearly all of real Lean code and all of Mathlib.
Its working memory holds only 64 terms per store, so only small examples
fit. There is no command-line tool yet; everything runs through tests.

**What you can do with Mathlib today** (the owner asked):

| You can | You cannot yet |
| --- | --- |
| Read and validate the whole Mathlib export in Forth: all 110,895,826 records (6.3 GB) in about 1 min 49 s with `gforth-fast`, in 17 MB of memory; every record's shape and every reference to an earlier record is checked, and the result equals the independent Python reader's field for field | Keep what was read: the checker's stores hold 64 entries, so nothing read from Mathlib is stored for the checker |
| Count every kind of record and declaration (184,355 definitions, 517,916 theorems, 7,046 inductive types, …) | Look up a Mathlib theorem by name, print it, or check it |
| In a measurement prototype (not the product): load all of Mathlib into the compact store design (2.94 GB, 4.16 GB peak), look up all 729,263 names (0.69 s), walk every declaration, and re-emit every record from memory equal to the reader's dump, line for line | Re-export Mathlib byte for byte in Lean's own format and compare it with Lean's file — planned (task 3.2.4, now with the checksum manifest) |

**What "the contents" of an imported library are** (the stored data, not
just the 16-byte node links of [ADR 0016](../adr/0016-compact-store.md)):
every *name* (4.24 million, such as `Nat.add_comm`) is a 16-byte record
pointing at its text in a byte pool, stored once; every *universe level*
and list of universe arguments; every *expression* node (106 million: a
kind, two links and an extra field, such as which variable or which
constant); *number and string literals* in a byte pool; and every
*declaration* (729,263) as a 32-byte record: its kind (definition, theorem,
inductive type, constructor, recursor, …), name, universe parameters, type,
value or proof, unfolding hint, recursor rules and inductive-type data.
That layout is accepted (ADR 0016) and measured on all of Mathlib, but only
the 32-bit access words exist in `src/`; building it is plan tasks
6.2.0–6.2.3.

### Review gates

| Part | Gate | State |
| --- | --- | --- |
| Rejection rules in comparison and inference (plan 2.2.1) | [kernel] | **approved** 2026-11-03 |
| NDJSON reader (Lean export files) | [import] | **approved** 2026-11-03, with a checksum manifest to add |
| Design records ADR 0010, 0013, 0016, 0017, 0018 | design | **accepted** (0017 on 2026-11-02; the rest 2026-11-03) |
| Checked environment v0 (2.2.2) | [kernel] | fourth review's fixes merged; short re-review running, then the owner |
| Declaration check (2.2.3) | [kernel], [bypass] | merged 2026-11-03; independent review running, then the owner |
| Program reader (Forth to program IR, 2.5.3) | [parser] | final review: nothing blocking; three small items being fixed, then the owner |
| LeanForth syntax words (8.1.2) | [parser] | merged 2026-11-03; independent review running, then the owner |
| Program receipt schema 0.1 (2.5.1) | [format] | waiting for the owner, together with the program reader |
| Big-number library (`lib/bignum.fs`, for literals) | [forth-review] | review found one serious memory bug in printing; fix running |

### Next major milestones

Each milestone ends with something you can see, and with its gates passed.
The order follows the plan's phases ([plan](PLAN_DRAFT.md#3-the-plan-on-one-page));
sizes are relative and dates are not estimated.

1. **First checked declaration (finish phase 2).** Close the four open
   gates above (environment, declaration check, program reader, syntax);
   add Lean's rejection of a "for all" whose body is not a type (ADR 0011
   amendment, owner rule "identical to Lean"); the failure-path suite
   (2.2.4: every check reaches every outcome, nothing failing ever
   stored as accepted); replay (2.2.5: a run record with the input's
   SHA-256 and byte-identical verdicts on replay); and the first readable
   proof of `composition` from the derivation log (ADR 0013, plan
   2.4.1 and 2.4.4). *You will see:* the five pinned examples print
   *accepted (experimental, not independently audited); axioms: none*,
   every broken copy prints *rejected* or *unsupported*, and
   `composition` prints as a short readable proof.
2. **Lean files in, a command-line tool out — release 0.1 (phase 3).**
   Stage the reader's records into stores built on the compact design
   (ADR 0016; plan 1.1.5, 3.2.1, 3.3.1, 6.2.0); feed declarations to the
   checker in file order (3.2.2); re-export byte for byte and compare with
   Lean's file (3.2.4); the checksum manifest checked by default and an
   upgrade test for new Lean and Mathlib versions (owner, 2026-11-03);
   `leanforth check FILE.ndjson`, `leanforth print` and exit codes
   (3.4); the JSON API v0 for AI tools with schemas and golden examples
   (3.5); authoring in its own process (8.2.1). *You will see:* one
   command checks a Lean export with only Forth installed.
3. **Definitions that compute (phase 4).** Unfolding with Lean's
   reducibility hints and lazy strategy, universe-level normalisation,
   eta, proof irrelevance, `let`, and the caches — the part where Lean's
   kernel spends most of its time (substitution about 40%, allocation and
   reference counting 21–23%, hash tables 21–25%;
   [profile](../development/measurements/lean-kernel-profile-2026-11-02/README.md)),
   so it is designed against the speed goal. *You will see:* the
   *unknown* answers of the table turn into Lean's answers, with the rate
   measured.
4. **Data types and the first real Lean code — release 0.2 (phase 5).**
   Inductive types, recursors, structures and projections, number and
   string literals (the big-number library is ready), quotients, the axiom
   allowlist (`propext`, `Classical.choice`, `Quot.sound`). *You will
   see:* `n + 0 = n` and `0 + n = n` (by induction) checked from real Lean
   output with every declaration they depend on, printed readably; and on
   the program track, the first program fact (the clamp contract) checked
   by LeanForth itself rather than by Lean.
5. **Scale to all of Mathlib (phase 6),** in stages with a denominator
   each: all of `Init`, then `Std`, a Mathlib slice chosen with the owner,
   then all 729,263 Mathlib declarations; a corpus comparison with Lean's
   verdict for every declaration, plus mutated copies that must be
   rejected; zero false acceptances; measured time and memory against
   Lean's one-thread time.
6. **Parallel checking (phase 7).** The groundwork exists (contexts, worker
   pool, single publisher); `--jobs 12` must give exactly the `--jobs 1`
   verdicts, faster. Later, investigate GPU offloading of untrusted bulk
   work (owner, 2026-11-03), never in the trusted kernel.
7. **Writing proofs and programs in LeanForth (phase 8)** — started: the
   syntax words exist; next come elaboration helpers and tactics (all
   untrusted, every result re-checked), `leanforth verify` for Forth words
   with contracts, and LaTeX as a second printer mode.
8. **Validation, outside audit, release 1.0 (phase 9):** reproduce
   published Lean results, an outside Lean-expert audit, the upgrade
   procedure, and a second Forth host.

**When will all of Mathlib be checked?** Not soon, and no date is
estimated: milestones 2–5 must all be built, and milestone 4 alone covers
the features (data types, recursors, literals, structures, quotients) that
nearly every Mathlib declaration uses. Reading Mathlib is done; storing it
is designed and measured; checking it is the work of phases 3–6. Each
stage will report an exact count of checked declarations out of 729,263.

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

**Status changes since the 2026-11-02 snapshot.** No acceptance task
changed state: the work of 2026-11-03 completed parts *inside* tasks
already in progress (T5.2–T5.3 the checker, T6.1–T6.2 the reader, T10.1
the syntax words), and none of them is done until its gate passes. The
2026-11-02 snapshot's five *done* tasks stand (T1.3, T4.1, T5.1, P3.1,
P3.2). Changes of state within the tasks:

| Task | Change | Evidence |
| --- | --- | --- |
| T5.3 checker | rejection rules approved; declaration check merged | owner's [kernel] approval of plan 2.2.1; the declaration check gives Lean's answer on all 62 table rows, 22 binder-domain rows (three capacity failures of the 64-node store, none accepted) and 17 universe rows |
| T6.1 export pinned and tested | reader approved | owner's [import] approval; remaining: detection of a file cut off between lines (the checksum manifest) |
| T10.1 Forth words that build terms | syntax words merged | 15 example files and 50 printer cases round-trip; 42 `#print` lines from 14 fixtures equal pinned Lean's; the authoring program does not yet hand terms to the checker (8.2.1) |
| T9.4 Mathlib time and memory | storage design accepted | ADR 0016: 2.94 GB stored, 4.16 GB peak, measured |

## Near-term queue and plan phase 1

| Item | State |
| --- | --- |
| Q1–Q4 | Done earlier, untrusted experimental preparation |
| Q5 Lean comparison | In progress: Lean's verdicts on 62 kernel cases and 27 broken source copies are pinned ([expected results](../reviews/FIRST_CHECKER_EXPECTED.md)); the declaration check gives Lean's answer on all 62 |
| Q6 checked environment design | Design approved (ADR 0012, G8–G11); v0 implemented (plan task 2.2.2, with the store marks of task 1.1.3): write-once slots published only after full success, snapshots and handles, name rules N1/N2/K5, transitive axiom sets, a single publisher; 237 assertions, 34 planted faults caught, interleaved checks equal to serial ones. Four review rounds; the fourth round's fixes (a check can no longer claim or free a context) merged 2026-11-03; a short re-review, then the owner's [kernel] gate |
| Q7 first independently checked declaration | In progress: the declaration check (plan 2.2.3) is merged and agrees with Lean on the whole table; its review and gate, the failure-path suite and replay remain |
| Q8 parallel program path | In progress: receipt schema 0.1, IR 0.1 with its Lean model and reader (plan 2.5.1–2.5.3), the IR interpreter's three-way comparison (2.5.4), the verification-condition generator v0 (2.5.5) and the first clamp receipt (2.5.6) are done; the reader's final review found nothing blocking (three small items being fixed); the reader ([parser]) and the receipt format ([format]) then go to the owner |
| Q9 consolidate experiments | Done 2026-11-02: 28 superseded modules and 91 test files retired with the owner's approval |
| Q10 refactor onto `src/lib` | Done (2026-11-02): every core and kernel module keeps its state in the per-task checker context (34 context members: stores, walk records, frames and module records; no global state left) and returns the shared outcomes (the 49 per-module status aliases are gone); cross-module field writes became stack interfaces; every module `require`s its direct dependencies; *exhausted* (out of fuel) and *full* (out of room) are separate; `src/core/` plus `src/kernel/` have about 690 words, none over ten lines (`make forth-metrics`), against a baseline of 218 words, 23% over ten lines and 225 globals. Randomized differentials against the previous code show no difference. Follow-ups: choose one of the three recursion patterns |

## Theorem proving and Mathlib

| Milestone | Status and evidence / remaining work |
| --- | --- |
| 1. Development foundation | 1 of 4 done (T1.3). Pinned Gforth 1.0.0 and Lean 4.35.0, CI on two Gforth versions, timeouts, `sorry`-proof Lean checks, documentation link and portability checks. Clean-machine reproduction (T1.1, T1.2) and a portability matrix (T1.4) remain. |
| 2. Terms, names and universes | In progress: bounded 64-entry stores on the library's `store:` records, handles that detect stale references, symbolic Sorts kept apart from concrete ones, which no checker pass accepts (ADR 0007; the unsafe draft that mixed them was retired), structured names. Human review of the representation and serialization remain. |
| 3. Scope and substitutions | In progress: shift, instantiation and universe substitution passes compared with Lean on finite tables (80, 25 and 48 cases and others). General specification and review remain. |
| 4. Definitional equality | 1 of 3 done (T4.1, rules approved). Conversion compares after beta reduction, answers *rejected* where ADR 0011's approved rules say Lean certainly rejects, and *unknown* elsewhere; unfolding, eta and proof irrelevance are phase 4. |
| 5. Small trusted checker | 1 of 4 done (T5.1, rules and design approved). Expected results: 62 cases (14 must be accepted, 28 rejected, 1 invalid, 11 unknown, 8 unsupported) checked against Lean. The rejection rules in comparison and inference (plan 2.2.1) were **approved by the owner on 2026-11-03** ([kernel] gate). The checked environment v0 (2.2.2) awaits its last review fixes and gate. The declaration check (2.2.3) is implemented and merged (2026-11-03): end to end, it gives Lean's answer on all 62 rows; its independent review and gate are next. Next: Lean's rule for a "for all" whose body is not a type (ADR 0011 amendment), the failure-path suite (2.2.4) and replay (2.2.5). |
| 6. Lean NDJSON importer | In progress: the Forth reader (gate approved 2026-11-03) decodes every record kind of lean4export 3.1.0 and all of Mathlib (below); the declaration check reads four pinned fixture exports end to end. Staging Mathlib-size input into stores, the checksum manifest and byte-for-byte re-export remain. |
| 7. Lean checker compatibility corpus | In progress: selected differential tables and the first checker's expected-results table; no official corpus run. |
| 8. Lean declaration features | In progress: the checked environment is designed (ADR 0012, per-declaration universe scope); candidate signatures remain unchecked assumptions; inductive types, recursors and quotients are decoded by the reader but not checked. |
| 9. Full Mathlib | In progress (T9.1, T9.4): denominator pinned, export and reading measured, storage design accepted and measured (ADR 0016); nothing imported into the checker's stores or checked. |
| 10. Native proof authoring | In progress (T10.1 in part): theorems and proofs are written as LeanForth words run by Forth's own interpreter ([syntax](../user/LEANFORTH_SYNTAX.md), [ADR 0017](../adr/0017-leanforth-syntax.md) approved; plan 8.1.2 merged 2026-11-03, under the [parser] gate): binder words, `fun`, `forall`, `->`, `$`, `^`, `theorem … := … end`, namespaces, labels and notes; 53 error codes with line and column; 42 `#print` lines from 14 fixtures equal Lean's. The term printer matches Lean's printing on 50 cases. Not yet: handing terms to the checker in a separate process, literals, `let`, tactics, readable proof outlines. |

## Provably correct executable Forth

| Milestone | Status and evidence / remaining work |
| --- | --- |
| 1. Contract and assumptions | In progress: [receipt schema 0.1](../programming/PROGRAM_RECEIPTS.md) keeps CHECK, VERIFY and RUN apart and requires runtime, cell, Lean, reader and floating-point assumptions; three valid and four invalid examples and 30 mutations are tested; the format awaits the owner's *[format]* approval. |
| 2. Tested Forth example | In progress: six example words with finite tests; formal contracts for the five words other than clamp remain (plan 1.5.3). |
| 3. Formal execution model | 2 of 3 done (P3.1, P3.2): IR 0.1 and its Lean semantics. Remaining: review the model against documented Forth behaviour (P3.3). |
| 4. Model/runtime comparisons | In progress: finite comparisons of the words with Lean models (686 clamp triples, 1,296 memory cases and others); the IR interpreter (`src/program/ir-run.fs`) agrees with the host words and with Lean's evaluation of the model on 5,152 cases (5,092 also run on the host) and 300 random IR programs (2.5.4); testing is not proof. |
| 5. Shared proof kernel | In progress only through the theorem track: the experimental declaration check exists, but program facts need data types (natural numbers, comparisons), so the first program fact checked by LeanForth arrives with phase 5 (owner answer OQ-5). |
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
- **Storage:** the compact store (ADR 0016, accepted 2026-11-03) holds all
  of Mathlib in 2.94 GB (4.16 GB peak while loading) in a measurement
  prototype; it is not yet the checker's store.
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
  serial path), give the serial results; the loader, the program reader,
  the IR interpreter and the NDJSON counter's tally are context members
  too, and a test checks that no loaded module's dictionary data changes
  while checks run. Reaching state through the context costs about 9%
  (`gforth`) and 15% (`gforth-fast`) on a fixed workload, after member
  words were compiled as a fixed offset from the context pointer (13% and
  23% before). Each context also holds
  a diagnostic record of why a check failed (reason code, site, two
  numbers; first failure wins), documented in
  [DIAGNOSTICS.md](../programming/DIAGNOSTICS.md).
- **Since then:** the single publisher and the shared checked environment
  (ADR 0012) are implemented and in their last review; the job pool's
  crash on Gforth 1.0 (workers sharing exception memory) is fixed.
- **Not done:** the scheduler that runs a whole file's declarations as jobs. The input stores are
  per context today; ADR 0012 wants one shared read-only input (plan task
  7.2.1). Roadmap C1 and C2 are in progress, C3 and C4 partly.

## Documentation

New since the last snapshot: [reading a Lean proof](../user/READING_A_LEAN_PROOF.md)
(every symbol and both ways variables are written, three proofs read
step by step), [LeanForth syntax](../user/LEANFORTH_SYNTAX.md) with checked
examples and its [word reference](../programming/LEANFORTH_WORDS.md), the
[checked environment](../programming/CHECKED_ENVIRONMENT.md) with its threat
model, [readable proofs sketch](../user/READABLE_PROOFS_SKETCH.md), the
measurements of the [compact store](../development/measurements/compact-store-2026-11-02/README.md)
and [Lean's kernel profile](../development/measurements/lean-kernel-profile-2026-11-02/README.md),
and ADRs 0010, 0013, 0016, 0017 and 0018. `make test` now runs the Forth
examples of five user pages and `make check` their Lean examples
(`scripts/check-doc-examples.py`).

From the 2026-11-02 snapshot: a [user guide](../user/USER_GUIDE.md) (what LeanForth is
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
GitHub is still to be looked at. Planned: manuals per audience as the features arrive, a limits
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

Inventory at this snapshot (`python3 scripts/code-inventory.py`, 2026-11-03):

| Category | Files | Physical lines |
| --- | ---: | ---: |
| Forth source, `src/lib/` | 15 | 3,294 |
| Forth source, `src/core/` | 14 | 1,455 |
| Forth source, `src/kernel/` | 19 | 3,793 |
| Forth source, `src/import/` | 3 | 1,228 |
| Forth source, `src/program/` | 5 | 1,553 |
| Forth source, `src/present/` | 10 | 1,748 |
| Forth source, `src/author/` | 10 | 1,476 |
| Forth source, `src/main.fs` | 1 | 36 |
| Forth tests and support | 141 | 17,717 |
| Other test code and support (Python, shell) | 64 | 8,737 |
| Lean references and tests | 102 | 7,990 |
| NDJSON fixtures | 11 | 309 |
| Markdown documentation | 102 | 22,648 |
| Other project files (Makefile, scripts, schemas, workflow, measurement data) | 119 | 9,542 |

All Forth source together: 77 files, 14,583 lines (2026-11-02: 52 files,
7,386 lines), of which `src/core/` and `src/kernel/` — the data model and
the checker under development — are 1,455 + 3,793 = 5,248 lines.

## Verification and CI

Run for this snapshot at `d6233af` (all passing): `make test` with Gforth
1.0.0 (17.4 s) and with Gforth 0.7.3; `make check` with pinned Gforth 1.0.0
and Lean 4.35.0 (about 2.5 minutes), at the merges of `a850a14` and
`492e63b`. CI on `main` (`.github/workflows/ci.yml`: `make test` on Ubuntu's
Gforth 0.7.3, `make check` on the pinned tools):
[41755412800](https://github.com/pmilford/LeanForth/actions/runs/41755412800)
passed for `9fc9258` (the declaration check and the JSON-writer fixes, 3 min
30 s) and [41581301184](https://github.com/pmilford/LeanForth/actions/runs/41581301184)
for `133ddb2`; the run for `d6233af` was in progress when this was written.
Earlier runs: [41555705430](https://github.com/pmilford/LeanForth/actions/runs/41555705430)
(term printer) and those of the 2026-11-02 snapshot. History: 15 consecutive Smoke
runs failed on 2026-11-01 until [41379263819](https://github.com/pmilford/LeanForth/actions/runs/41379263819);
the Codex-era tag `pre-claude` passed [41476841907](https://github.com/pmilford/LeanForth/actions/runs/41476841907);
the current workflow's first run, [41504003139](https://github.com/pmilford/LeanForth/actions/runs/41504003139),
was the first CI run of the pinned-Lean comparisons.

## Limitations

- The first checker is experimental and not yet through its gates: the
  declaration check and the checked environment await their reviews and
  the owner; every acceptance is labelled *experimental — not
  independently audited*, and no outside Lean expert has audited it.
- It covers only universes, variables, functions, "for all" and earlier
  checked declarations, without unfolding: data types, literals,
  structures, `let`, projections and quotients are *unsupported*.
- Stores hold 64 entries and constants at most 8 universe arguments (the
  compact store of [ADR 0016](../adr/0016-compact-store.md), accepted, held all
  of Mathlib in a 2.94 GB prototype, not yet in the checker);
  Mathlib needs millions of entries and 30 arguments. The rebuild passes
  recurse on the host's return stack (about 1,200 cells at worst today).
- The program track's proofs are about the IR's Lean semantics, checked by
  Lean; that Gforth runs the words as the IR says, and that the reader
  translates faithfully, are tested, not proved.
- Only Lean 4.35.0 exports in format 3.1.0 are read; a file cut off cleanly
  between two lines is not yet detected (checksum manifest planned); only
  Linux/WSL with Gforth 1.0.0 and 0.7.3 is tested.

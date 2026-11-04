# LeanForth project progress

Snapshot: **2026-11-04**, at commit `6266f70` on `main` (previous snapshot
2026-11-03 evening at `7ffbfff`; before that the same day at `d6233af` and
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
1 invalid. Its independent review found a serious defect (2026-11-03): it
*accepted* small declarations that Lean *rejects*, because it built and
compared universe levels differently from Lean. **Fixed the same day:**
LeanForth now ports Lean's own level code exactly, and all 49 universe
cases and 69 table cases give Lean's answers. Nothing it says is trusted yet: the declaration check and the
checked environment it publishes into are still in their review gates, and
every acceptance is labelled *experimental — not independently audited*.

**A design in progress, to be completed and compatible later (owner,
2026-11-04).** Everything LeanForth cannot do or does differently from Lean
today is a *temporary* gap in a design that is being built step by step
towards 100% Lean 4.35.0 compatibility, not a permanent difference. Each gap
below names the plan task that closes it. Where LeanForth is cautious today,
it refuses or says *unknown* and never accepts something Lean rejects. The
owner's rule: with no options, LeanForth's verdicts are Lean's; anything
stricter or different is an opt-in flag.

**Milestones since the 2026-11-03 evening snapshot.**

1. **The checker can be fed a real library.** Its working memory is no
   longer a fixed 64 entries: the stores live on the computer's heap and
   grow. All of Lean's `Init` library (59,349 declarations) is staged,
   handed to the checker in file order and checked, end to end.
2. **First data types.** LeanForth now checks a non-recursive data type
   (plan task 5.2.1a) as Lean's `add_inductive` does: it builds the
   recursor and its rules itself and compares them with the file's. With it,
   `Init` end to end gives **184 data types and 1,014 definitions and
   theorems accepted, and 0 wrongly rejected or invalid** (of 551 data-type
   blocks in scope, 90 are *unknown* and 277 *unsupported*, each waiting for
   unfolding, recursive types, literals or structures;
   [ADR 0015](../adr/0015-inductive-types.md)). This replaces the 37
   accepted declarations of the last snapshot.
3. **Init's feed and check are much faster** (agent KC's measurements):
   feed 96 s to 12 s, check 63 s to 9 s, with identical verdicts.
4. **Readable proofs.** `bin/leanforth print` prints a numbered proof
   outline from the derivation log of an accepted declaration (gate D5,
   approved).
5. **Free variables** (plan task 4.2.2a): inference enters binders one at a
   time as Lean does, the first step of unfolding (approved).
6. **Universe lists without a fixed limit** (plan 6.2.0 part a): universe
   arguments, parameters and the level context grow with memory; 100, 300 and
   1,000 universe parameters agree with pinned Lean (24 rows). Depth limits
   (part b) are in progress.
7. **Program words, run records and the IR 0.2 design approved** (see the
   gates table).
8. **A test-suite crash found and fixed.** Both the WSL crash and the Claude
   Code crash of 2026-11-04 were one bug: the new test wrapper
   `scripts/gforth-strict.sh` called itself, a fork bomb of about a thousand
   copies that exhausted 39 GB of memory and 16 GB of swap. Fixed in
   `e6a0a74` with self-reference and depth guards; no work was lost (the
   uncommitted work of the agents was saved as WIP commits).

**Held, by decision of the owner (2026-11-04): the checker on the large
store [kernel].** The owner asked whether the fixed limits of 64 (universe
arguments per reference, parameters per declaration, the level context's
parameter names, and the walk, frame and binder depths) are needed. Lean has
no such limits (Mathlib uses up to 30 universe parameters and terms nest to
depth 1,221). The gate is not asked again until these limits are dynamic,
bounded only by memory (plan 6.2.0, brought forward): the universe lists
are done (part a), the depth limits are in progress (part b).

**What it cannot do yet (all temporary).** It cannot check anything that
needs a definition unfolded (phase 4, tasks 4.2.2b-e), a recursive data
type such as the natural numbers or lists (task 5.2.1b), a structure
(5.2.2) or a number literal (5.2.3) — which is nearly all of real Lean code
and all of Mathlib. The command `bin/leanforth check` exists but keeps the
default small store sizes, so only exports the size of the test fixtures
fit; the large sizes are used by the tests and by the `Init` run (the
dynamic limits of plan 6.2.0 and the [kernel] gate come first).

**What you can do with Mathlib today** (the owner asked):

| You can | You cannot yet |
| --- | --- |
| Read and validate the whole Mathlib export in Forth: all 110,895,826 records (6.3 GB) in about 1 min 49 s with `gforth-fast`, in 17 MB of memory; every record's shape and every reference to an earlier record is checked, and the result equals the independent Python reader's field for field | Keep what was read: the checker's stores can now grow (`Init` fits), but Mathlib has not been fed to them and `bin/leanforth check` still uses small default sizes |
| Check Lean's whole `Init` library end to end in Forth (staged, fed in file order, checked): 184 data types and 1,014 definitions and theorems accepted, 0 rejected, most of the rest *unsupported* or *unknown* until phases 4 and 5 are built (feed 12 s, check 9 s) | Check a real Lean theorem such as `n + 0 = n`, which needs recursive types, structures, literals and unfolding (see the milestones) |
| Print a numbered, readable proof outline of an accepted declaration with `bin/leanforth print` | Print proofs that need unfolding or data-type steps not yet built |
| Count every kind of record and declaration (184,355 definitions, 517,916 theorems, 7,046 inductive types, …) | *(Since the importer stage was approved on 2026-11-03:)* stage all of Mathlib into the compact store and find every one of its 729,263 declarations by name. You still cannot print a Mathlib theorem or check it; for `Init` the checker answers as in the paragraph above |
| In a measurement prototype (not the product): load all of Mathlib into the compact store design (2.94 GB, 4.16 GB peak), look up all 729,263 names (0.69 s), walk every declaration, and re-emit every record from memory equal to the reader's dump, line for line | *(Since 2026-11-03, plan task 3.2.4:)* re-export `Init`, `Std` and all of Mathlib byte for byte in Lean's own NDJSON format — the copies' SHA-256 equal the originals', and reading them back gives the same records ([measurements](../development/measurements/reexport-2026-11-03/README.md); Mathlib in 5 min 29 s, 20 MB) |

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
| Importer stage (staging into the compact store; ADR 0016 C9 steps 1, 2, 5) | [import] | **approved** 2026-11-03 (late night); independent re-review clean, minor limits documented. **The importer stage gate is passed.** |
| Heap stores and the stage feed; the checker on the large store (ADR 0016 C9 step 3 in part; plan 1.1.5, 3.2.2) | [kernel] | merged; reviews done and their fixes merged; **held by the owner (2026-11-04)** until the fixed limits of 64 are dynamic (plan 6.2.0: universe lists done, depth limits in progress); the gate is then asked again |
| Data types, ADR 0015 (inductive types) | design | **accepted as a design** 2026-11-03; each implementation task has its own gate |
| Non-recursive data types (plan 5.2.1a) | [kernel], [import] | **approved** 2026-11-04 after three review rounds, the last clean. **Condition (owner):** its temporary differences from Lean close to 100% compatibility, any stricter behaviour only behind an opt-in flag: (1) a file using `T.rec` without declaring it gets LeanForth's own generated recursor, as in Lean; (2) a block rejected at the final comparison (B3) keeps its type and constructors usable afterwards, as in Lean's environment; (3) the guard on unit-like structures closes with task 5.2.2. **Condition met** 2026-11-04 after rounds 4–6: (1) and (2) done, an empty block now rejected as in Lean; every remaining gap temporary with its task ([decisions](OWNER_DECISIONS.md#data-types-first-step-condition-met-2026-11-04-late)) |
| Free variables and the local context (plan 4.2.2a) | [kernel] | **approved** 2026-11-04 after two review rounds; accepted cost: checking is 10-25% slower until the loose-variable range of ADR 0014 Q12 is built |
| Derivation log and proof outlines, `leanforth print` (plan 2.4.1, 2.4.4; ADR 0013) | gate D5 | **approved** 2026-11-04 after three review rounds; accepted memory: about 218 KB per context while the log is on, under 1 KB off |
| Run-record reading change: both passes and the recorded SHA-256 must agree, with or without the manifest (`src/import/checker-input.fs`) | [import] | **approved** 2026-11-04 after four review rounds, the last clean |
| IR 0.2 design (ADR 0019 Amendment 1: redefinition with Forth's early binding, output words as effects, SHA-2 additions `LSHIFT`, `-rot`, number prefixes, 32-bit literals) | [parser] design | **approved** 2026-11-04 as a design; not yet implemented; receipt schema 0.3 comes to the [format] gate with the first receipt that needs it |
| Design records ADR 0010, 0013, 0015, 0016, 0017, 0018 | design | **accepted** (0017 on 2026-11-02; the rest 2026-11-03; 0015 as a design, with a gate per task) |
| Checked environment v0 (2.2.2) | [kernel] | **approved** 2026-11-03 |
| Declaration check (2.2.3) and the level fix | [kernel], [bypass] | **approved** 2026-11-03 |
| Program reader (Forth to program IR, 2.5.3) | [parser] | replaced by the owner's two-mode design (ADR 0019, accepted in direction). The two-mode program words (verify mode emits the program IR, run mode executes as plain Forth; the portable mode shift is primary and the alias vocabulary is kept beside it; 287 inputs after the review fixes) are **approved** 2026-11-04 after three review rounds, with stated limits (source-to-IR is tested, not proved; a standard word redefined before the words load is not noticed). Next, IR 0.2 (row below) Today's text reader stays as a cross-check, then retires |
| LeanForth syntax words (8.1.2) | [parser] | **approved** 2026-11-03, after two clean review rounds (term-for-term equal to Lean on 67 declarations) |
| Program receipt schema 0.2 (2.5.1) | [format] | **approved** 2026-11-03 (schema pinned by hash; any change is a new version) |
| Run-record format 0.1 (environment identity, manifest-enforced field tied to the bytes read, both import passes compared, blank-looking names refused) | [format] | **approved** 2026-11-04 after three independent review rounds (`docs/programming/RUN_RECORDS.md`) |
| Axiom policy and defaults (owner, 2026-11-03) | policy | decided: `sorryAx` and any axiom outside the three standard ones get Lean's verdict, labelled **NOT PROVED** (the flag `--standard-axioms-only` refuses them); with no flags LeanForth is always Lean. Not implemented yet; the owner asked on 2026-11-04 to consider changing the rule (plan 5.3.3, options to be brought in plain words) |
| Big-number library (`lib/bignum.fs`, for literals) | [forth-review] | review found one serious memory bug in printing; fixed and merged 2026-11-03 (`ed4dab7`, merge `4c714f5`); its owner gate comes with literals (plan 5.2.3) |

### Test tooling (2026-11-03)

- `make mutants`: deliberate bugs kept in `tests/mutants/faults.toml`
  (424 entries at this snapshot; 134 at the last one), each planted in a
  temporary copy and run against the test meant to catch it. The caught,
  equivalent and known-gap counts were not re-run for this snapshot; at the
  last one, 123 of 134 were caught, 1 made no difference and 10 were known
  test gaps. `make check` fails if an entry no longer matches the code.
- `make coverage`: 96.6% of the 12,093 code blocks of `src/` run during
  `make test` (lowest: printing 93.4%, authoring 94.4%). Running code is
  not the same as checking it; that is what the planted faults measure.
- The failure-path suite (2.2.4, 1.4.6) — see milestone 1 below.
- **Strict Gforth wrapper (agent TS, 2026-11-04).** `scripts/gforth-strict.sh`
  makes a test that reports an error never pass, even when Gforth exits 0
  (merge `8ca3f77`). Its first version called itself and caused the crashes
  described above; the guards of `e6a0a74`, a bound on every FIFO reader and
  `gforth-fast` run through the wrapper followed. CI gives the `Init`
  staging test 1,500 s (`6266f70`).
- **Fast checks (agent TT, merged 2026-11-03; no owner gate, test tooling).**
  `make` now runs 8 jobs at a time by default (`JOBS=1` runs one at a time),
  and pinned Lean's deterministic verdicts are replayed from a shared cache
  (`scripts/lean-cache.py`) when every input of a call is unchanged. CI runs
  without the cache (`LEAN_CACHE=0`), so its pass is the record. `make
  test-changed` and `make check-changed` run only the targets that use files
  changed since `main`. Timings in the
  [testing strategy](../development/TESTING_STRATEGY.md): `make test` 7.9-8.5 s
  (36 s one at a time); `make check` 345 s before, now 43 s with a filled
  cache, 69 s with an empty one and 75 s without the cache (what CI runs).

### Next major milestones

Each milestone ends with something you can see, and with its gates passed.
The order follows the plan's phases ([plan](PLAN_DRAFT.md#3-the-plan-on-one-page));
sizes are relative and dates are not estimated.

1. **First checked declaration (finish phase 2).** Close the four open
   gates above (environment, declaration check, program reader, syntax);
   add Lean's rejection of a "for all" whose body is not a type (ADR 0011
   amendment, owner rule "identical to Lean"; **done 2026-11-03**, rule S4); the failure-path suite
   (2.2.4, **done 2026-11-03**: 4,493 runs with each allocation refused
   or thrown in turn and fuel swept from zero; nothing failing is ever
   accepted, published or printed as accepted); replay (2.2.5: a run record with the input's
   SHA-256 and byte-identical verdicts on replay); and the first readable
   proof of `composition` from the derivation log (ADR 0013, plan
   2.4.1 and 2.4.4). *You will see:* the five pinned examples print
   *accepted (experimental, not independently audited); axioms: none*,
   every broken copy prints *rejected* or *unsupported*, and
   `composition` prints as a short readable proof.
2. **Lean files in, a command-line tool out — release 0.1 (phase 3).**
   Stage the reader's records into stores built on the compact design
   (ADR 0016; plan 1.1.5, 3.2.1, 3.3.1, 6.2.0; staging is approved, and
   the checker's stores now grow, and the owner holds the [kernel] gate for
   the checker on the large store until the fixed limits of 64 are dynamic;
   6.2.0 is in progress, brought forward by the owner: universe parameter and
   argument lists and the level context have no fixed limit since
   2026-11-04, checked against Lean with 100, 300 and 1,000 parameters,
   and the depth limits, part (b), are in progress); feed
   declarations to the checker in file order (3.2.2; works for `Init`
   today, gate pending); re-export byte for byte and compare with
   Lean's file (3.2.4, **done 2026-11-03**); the checksum manifest checked by default and an
   upgrade test for new Lean and Mathlib versions (owner, 2026-11-03);
   `leanforth check FILE.ndjson` and exit codes (3.4; `leanforth print`,
   readable proof outlines from the command line, merged and **approved** by
   the owner 2026-11-04, gate D5); the JSON API v0 for AI tools with schemas and golden examples
   (3.5); authoring in its own process (8.2.1). *You will see:* one
   command checks a Lean export with only Forth installed. Today
   `bin/leanforth check` still has the small default sizes.
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
   allowlist (`propext`, `Classical.choice`, `Quot.sound`; the owner's
   rule: other axioms such as `sorryAx` get Lean's verdict labelled NOT
   PROVED, and `--standard-axioms-only` refuses them; the owner asked on
   2026-11-04 to consider changing this rule, plan 5.3.3). ADR 0015 is
   accepted as a design and its first step, task 5.2.1a (non-recursive
   inductive blocks), is **done and approved** (2026-11-04), ahead of phase
   4, with the owner's condition that its temporary differences close to
   100% Lean. **The first real Lean theorem, `n + 0 = n`** (`Nat.add_zero`),
   needs: 5.2.1b recursive types (`Nat`), 5.2.2 structures and projections,
   5.2.3 number literals, and from phase 4 the unfolding steps 4.2.2b-e
   (free variables, 4.2.2a, are done). *You will
   see:* `n + 0 = n` and `0 + n = n` (by induction) checked from real Lean
   output with every declaration they depend on, printed readably; and on
   the program track, the first program fact (the clamp contract) checked
   by LeanForth itself rather than by Lean.
5. **Scale to all of Mathlib (phase 6),** in stages with a denominator
   each: all of `Init`, then `Std`, a Mathlib slice chosen with the owner,
   then all 729,263 Mathlib declarations (plan 6.1.6, owner 2026-11-03:
   soon also a few small Lean libraries and the largest one); a corpus comparison with Lean's
   verdict for every declaration, plus mutated copies that must be
   rejected, and Lean's own test suites run through NDJSON exports (plan
   6.4.2, owner 2026-11-04); a resource report of fuel, memory and CPU for
   every check (6.5.2) and a study of how large proofs are split (6.5.3); zero false acceptances; measured time and memory against
   Lean's one-thread time. A first measured point exists: `Init` is staged,
   fed and checked (see the plain-words section), with 184 data types and
   1,014 definitions and theorems accepted and none wrongly rejected.
6. **Parallel checking (phase 7).** The groundwork exists (contexts, worker
   pool, single publisher); `--jobs 12` must give exactly the `--jobs 1`
   verdicts, faster; the worker count becomes a setting that defaults to the
   core count and is measured beyond it (plan 6.5.4, owner 2026-11-04). Later, investigate GPU offloading of untrusted bulk
   work (owner, 2026-11-03), never in the trusted kernel.
7. **Writing proofs and programs in LeanForth (phase 8)** — started: the
   syntax words exist; next come elaboration helpers and tactics (all
   untrusted, every result re-checked), `leanforth verify` for Forth words
   with contracts, and LaTeX as a second printer mode.
8. **Validation, outside audit, release 1.0 (phase 9):** reproduce
   published Lean results, an outside Lean-expert audit, the upgrade
   procedure, and a second Forth host.

**The program track runs beside these, without delaying them** (owner,
2026-11-03). Its flagship target is LeanForth's own SHA-256: a Lean
specification of FIPS 180-4 checked against the NIST vectors first, then
proofs that the Forth words compute it — the helper functions, the loops
of the block compression, then padding and buffers — as the program IR
gains loops and memory, and finally checked by LeanForth itself
([plan](PLAN_DRAFT.md#program-track-goal-most-of-forth-2012-core-owner-2026-11-02)).
Before that: contracts for the five other example words (done 2026-11-03) and
the owner's [parser] and [format] decisions on the program reader and
receipts (both **approved** 2026-11-04). Next on this track is the
implementation of IR 0.2 (approved as a design 2026-11-04): redefinition,
output words and the SHA-2 additions.

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
| T5.3 checker | rejection rules approved; declaration check merged | owner's [kernel] approval of plan 2.2.1; the declaration check gives Lean's answer on all 69 table rows, 22 binder-domain rows (three capacity failures of the 64-node store, none accepted) and 49 universe rows, after the level fix of 2026-11-03 |
| T6.1 export pinned and tested | reader approved | owner's [import] approval; remaining: detection of a file cut off between lines (the checksum manifest) |
| T10.1 Forth words that build terms | syntax words merged | 15 example files and 50 printer cases round-trip; 42 `#print` lines from 14 fixtures equal pinned Lean's; the authoring program does not yet hand terms to the checker (8.2.1) |
| T9.4 Mathlib time and memory | storage design accepted | ADR 0016: 2.94 GB stored, 4.16 GB peak, measured |
| T5.3 / T6 feeding the checker | `Init` fed end to end (plan 3.2.2, 1.1.5, in part) | 59,349 declarations fed; at the 2026-11-03 snapshot 37 accepted, 0 rejected, 59,025 unsupported at 100,000 fuel ([ADR 0016, step 3](../adr/0016-compact-store.md)); since task 5.2.1a, 184 data types and 1,014 definitions and theorems accepted, 0 rejected or invalid ([ADR 0015](../adr/0015-inductive-types.md)); reviews done, [kernel] gate held until the limits are dynamic |
| P6 program reader | two-mode program words approved [parser] 2026-11-04 | 273 inputs agree with the old reader, 4 intended differences, 287 after the review fixes ([program IR](../programming/PROGRAM_IR.md)); IR 0.2 design approved, not implemented |
| Plan tasks 5.2.1a, 4.2.2a, 2.4.1, 2.4.4 | merged and approved 2026-11-04 | see the gates table; the roadmap tasks they belong to (T5.3, T6, T10) stay in progress |
| Plan 6.2.0 part (a) | universe lists without a fixed limit | 100, 300 and 1,000 universe parameters agree with pinned Lean (24 rows); depth limits (part b) in progress |

**Plan tasks by state (2026-11-04).** IDs are those of
[PLAN_DRAFT.md](PLAN_DRAFT.md); every row of the first table is merged. The
roadmap counts above are unchanged: they count the roadmap's acceptance
tasks, not the plan's.

| Plan task | State |
| --- | --- |
| 2.4.1 derivation log, 2.4.4 proof-outline printer, `leanforth print` (agent RB) | **done, approved** (gate D5) |
| 4.2.2a free variables and local context (agent D2A) | **done, approved** [kernel] |
| 5.2.1a non-recursive inductive blocks (agent I21) | **done, approved** [kernel][import]; the owner's 100%-Lean condition **met** 2026-11-04 (review rvI21 rounds 4–6): 94 Lean-checked rows, 88 with Lean's verdict, 6 pending on 5.2.1b and 4.2.2 |
| 6.2.0 part (a) universe lists without a fixed limit (agent KC) | **done, merged**; covered by the held [kernel] gate |
| Program words (ADR 0019), run-record format 0.1, import-read change, IR 0.2 design | **approved** 2026-11-04 (see the gates table) |

| Plan task | State |
| --- | --- |
| 6.2.0 part (b) depth limits (walk, frame, binder depths up to 1,221) | **in progress**; the held [kernel] gate waits for it |
| 4.2.2b-e unfolding, the lazy strategy, eta, proof irrelevance, `let` | not started; next after the free variables |
| 5.2.1b recursive types, 5.2.1c indexed families, 5.2.2 structures and projections, 5.2.3 literals | not started; they close the temporary gaps of 5.2.1a and are on the way to `n + 0 = n` |
| 5.3.3 review of the axiom rule (owner, 2026-11-04) | planned; options to be brought in plain words |
| 6.1.6 other Lean libraries (a few small ones and the largest) | planned (owner, 2026-11-03: "soon", not yet) |
| 6.4.2 Lean's own test suites as NDJSON exports | planned (owner, 2026-11-04) |
| 6.5.2 resource report for every check: fuel, memory, CPU | planned (owner, 2026-11-04); run records get a new schema version under the [format] gate |
| 6.5.3 large proofs: limits and how Lean users split them | planned (owner, 2026-11-04) |
| 6.5.4 worker count as a setting; speed-up beyond the core count measured | planned (owner, 2026-11-04) |

## Near-term queue and plan phase 1

| Item | State |
| --- | --- |
| Q1–Q4 | Done earlier, untrusted experimental preparation |
| Q5 Lean comparison | In progress: Lean's verdicts on 62 kernel cases and 27 broken source copies are pinned ([expected results](../reviews/FIRST_CHECKER_EXPECTED.md)); the declaration check gives Lean's answer on all 62 |
| Q6 checked environment design | Design approved (ADR 0012, G8–G11); v0 implemented (plan task 2.2.2, with the store marks of task 1.1.3): write-once slots published only after full success, snapshots and handles, name rules N1/N2/K5, transitive axiom sets, a single publisher; 237 assertions, 34 planted faults caught, interleaved checks equal to serial ones. Four review rounds; the fourth round's fixes (a check can no longer claim or free a context) merged 2026-11-03; a short re-review, then the owner's [kernel] gate |
| Q7 first independently checked declaration | In progress: the declaration check (plan 2.2.3) is merged and agrees with Lean on the whole table; its review and gate, the failure-path suite and replay remain |
| Q8 parallel program path | In progress: receipt schema 0.2, IR 0.1 with its Lean model and reader (plan 2.5.1–2.5.3), the IR interpreter's three-way comparison (2.5.4), the verification-condition generator v0 (2.5.5) and the first clamp receipt (2.5.6) are done; the reader's final review found nothing blocking (three small items being fixed); the reader ([parser]) and the receipt format ([format]) then go to the owner |
| Q9 consolidate experiments | Done 2026-11-02: 28 superseded modules and 91 test files retired with the owner's approval |
| Q10 refactor onto `src/lib` | Done (2026-11-02): every core and kernel module keeps its state in the per-task checker context (34 context members: stores, walk records, frames and module records; no global state left) and returns the shared outcomes (the 49 per-module status aliases are gone); cross-module field writes became stack interfaces; every module `require`s its direct dependencies; *exhausted* (out of fuel) and *full* (out of room) are separate; `src/core/` plus `src/kernel/` have about 690 words, none over ten lines (`make forth-metrics`), against a baseline of 218 words, 23% over ten lines and 225 globals. Randomized differentials against the previous code show no difference. Follow-ups: choose one of the three recursion patterns |

## Theorem proving and Mathlib

| Milestone | Status and evidence / remaining work |
| --- | --- |
| 1. Development foundation | 1 of 4 done (T1.3). Pinned Gforth 1.0.0 and Lean 4.35.0, CI on two Gforth versions, timeouts, `sorry`-proof Lean checks, documentation link and portability checks. Clean-machine reproduction (T1.1, T1.2) and a portability matrix (T1.4) remain. |
| 2. Terms, names and universes | In progress: stores on the library's `store:` records that now grow on the heap up to a per-context capacity (default 64; universe arguments, parameters and the level context now have no fixed limit, plan 6.2.0 part a; depth limits, part b, in progress; the owner's [kernel] gate is held until they are dynamic), handles that detect stale references, symbolic Sorts kept apart from concrete ones, which no checker pass accepts (ADR 0007; the unsafe draft that mixed them was retired), structured names. Human review of the representation and serialization remain. |
| 3. Scope and substitutions | In progress: shift, instantiation and universe substitution passes compared with Lean on finite tables (80, 25 and 48 cases and others). General specification and review remain. |
| 4. Definitional equality | 1 of 3 done (T4.1, rules approved). Conversion compares after beta reduction, answers *rejected* where ADR 0011's approved rules say Lean certainly rejects, and *unknown* elsewhere; unfolding, eta and proof irrelevance are phase 4. |
| 5. Small trusted checker | 1 of 4 done (T5.1, rules and design approved). Expected results: 62 cases (14 must be accepted, 28 rejected, 1 invalid, 11 unknown, 8 unsupported) checked against Lean. The rejection rules in comparison and inference (plan 2.2.1) were **approved by the owner on 2026-11-03** ([kernel] gate). The checked environment v0 (2.2.2) awaits its last review fixes and gate. The declaration check (2.2.3) is implemented and merged (2026-11-03): end to end, it gives Lean's answer on all 62 rows; its independent review and gate are next. Next: Lean's rule for a "for all" whose body is not a type (ADR 0011 amendment), the failure-path suite (2.2.4) and replay (2.2.5). |
| 6. Lean NDJSON importer | In progress: the Forth reader (gate approved 2026-11-03) decodes every record kind of lean4export 3.1.0 and all of Mathlib (below); the importer stage (approved 2026-11-03) stages all of Mathlib and the byte-for-byte re-export is done; the checker is fed `Init` end to end (heap stores; gate held, see above). Feeding Mathlib, the checksum manifest check by default and other Lean libraries (plan 6.1.6) remain. |
| 7. Lean checker compatibility corpus | In progress: selected differential tables and the first checker's expected-results table; no official corpus run. |
| 8. Lean declaration features | In progress: the checked environment is designed (ADR 0012, per-declaration universe scope); candidate signatures remain unchecked assumptions; non-recursive inductive types and their recursors are checked (plan 5.2.1a, approved 2026-11-04); recursive and indexed types, structures, literals and quotients are decoded by the reader but not yet checked (plan 5.2.1b-c, 5.2.2, 5.2.3, phase 5). |
| 9. Full Mathlib | In progress (T9.1, T9.4): denominator pinned, export and reading measured, storage design accepted and measured (ADR 0016); nothing imported into the checker's stores or checked. |
| 10. Native proof authoring | In progress (T10.1 in part): theorems and proofs are written as LeanForth words run by Forth's own interpreter ([syntax](../user/LEANFORTH_SYNTAX.md), [ADR 0017](../adr/0017-leanforth-syntax.md) approved; plan 8.1.2 merged 2026-11-03, under the [parser] gate): binder words, `fun`, `forall`, `->`, `$`, `^`, `theorem … := … end`, namespaces, labels and notes; 53 error codes with line and column; 42 `#print` lines from 14 fixtures equal Lean's. The term printer matches Lean's printing on 50 cases. Readable proof outlines now come from the checker's derivation log (`leanforth print`, approved 2026-11-04). Not yet: handing terms to the checker in a separate process, literals, `let`, tactics. |

## Provably correct executable Forth

| Milestone | Status and evidence / remaining work |
| --- | --- |
| 1. Contract and assumptions | In progress: [receipt schema 0.2](../programming/PROGRAM_RECEIPTS.md) keeps CHECK, VERIFY and RUN apart, says whether Lean or LeanForth settled each obligation, lists axioms per theorem and requires runtime, cell, stack-capacity, two's-complement, Lean, reader, generator and floating-point assumptions; 29 tests with 114 mutations; the format awaits its re-check and the owner's *[format]* approval. |
| 2. Tested Forth example | In progress: six example words with finite tests; all six now have formal contracts (plan 1.5.3, done 2026-11-03): Lean proves each word's reference model and IR meet its contract for every cell width (gcd and factorial through loop invariants) and refutes deliberately wrong models and programs, 27 theorems using at most `propext`, `Classical.choice` and `Quot.sound`. Choosing one word as the acceptance target (P2.3) remains. |
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
| Expression nodes staged into the compact store | all of Mathlib's 105,894,257 (importer stage, approved) | nodes of the pinned export |
| Expression nodes fed into the checker's own stores | `Init` only: 6,099,054 nodes of its 59,349 declarations; none of Mathlib | the checker's stores grow, default 64 (the held [kernel] gate) |
| Declarations checked by LeanForth | **0 of 729,263 (0%)** of Mathlib; for `Init`, 184 data types and 1,014 definitions and theorems accepted (experimental, not independently audited), none rejected; the rest *unknown* or *unsupported* (counts per kind in [ADR 0015](../adr/0015-inductive-types.md)); the earlier 37 of 59,349 at 100,000 fuel is superseded | constants of the pinned Mathlib export with its dependencies; `Init`'s own count |
| Share of Mathlib the first checker could accept | **unknown** | not measured; most declarations depend on recursive types, structures or literals, which are *unsupported* until phase 5 |
| T6 importer acceptance tasks done | 0 of 4 | roadmap T6 |
| Other Lean libraries imported (plan 6.1.6) | 0 | planned: a few small ones and the largest |

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
  prototype and, since the importer stage was approved, in `src/import/`.
  The checker's own stores now grow on the heap and copy what they are fed
  (about 80 bytes per node); reading the staged input in place is still to
  come.
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

Inventory at this snapshot (`python3 scripts/code-inventory.py` at `6266f70`,
2026-11-04, tracked files only; the previous table was at `7ffbfff`):

| Category | Files | Physical lines |
| --- | ---: | ---: |
| Forth source, `src/lib/` | 25 | 5,472 |
| Forth source, `src/core/` | 21 | 3,882 |
| Forth source, `src/kernel/` | 26 | 6,558 |
| Forth source, `src/import/` | 11 | 4,626 |
| Forth source, `src/program/` | 10 | 2,583 |
| Forth source, `src/present/` | 13 | 2,931 |
| Forth source, `src/author/` | 11 | 1,677 |
| Forth source, `src/cli/` | 2 | 750 |
| Forth source, `src/main.fs` | 1 | 57 |
| Forth tests and support | 175 | 24,619 |
| Other test code and support (Python, shell) | 94 | 16,186 |
| Lean references and tests | 113 | 12,043 |
| NDJSON fixtures | 88 | 5,812 |
| Markdown documentation | 116 | 33,509 |
| Other project files (Makefile, scripts, schemas, workflow, measurement data) | 222 | 22,128 |

All Forth source together: 120 files, 28,536 lines (at `7ffbfff`: 109 files,
22,966 lines; 2026-11-03 morning: 77 files, 14,583 lines; 2026-11-02: 52
files, 7,386 lines), of which `src/core/` and `src/kernel/` — the data model
and the checker under development — are 3,882 + 6,558 = 10,440 lines.

## Verification and CI

The runs below are those of the earlier snapshots; this snapshot's runs
were not looked up (see the 2026-11-04 entry at the end).

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

Every gap below is **temporary**: LeanForth is an in-progress design that
will be completed and compatible with Lean 4.35.0 (owner, 2026-11-04), and
each item names the plan task that closes it. Where it differs today, it is
cautious (refuses or says *unknown*), never more permissive than Lean.

- The checker is experimental and the owner has approved its parts one by
  one (rejection rules, environment, declaration check, free variables, the
  first data types, the derivation log); the heap-store checker on the large
  store is held (below). Every acceptance is labelled *experimental — not
  independently audited*, and no outside Lean expert has audited it.
- Where Lean's own verdict depends on how its level objects share memory
  (rule K6, BEYOND_LEAN BL-3), LeanForth answers *unknown*.
- Without unfolding (phase 4, tasks 4.2.2b-e), recursive and indexed data
  types (5.2.1b-c), structures and projections (5.2.2), literals (5.2.3),
  `let` and quotients, those declarations are *unknown* or *unsupported*.
  The three temporary differences of the data-type step, which the owner
  asked to close to 100% Lean: a file that uses `T.rec` without declaring it
  is refused today (Lean uses its own generated recursor); a block rejected
  at the final comparison (B3) does not keep its type and constructors
  usable afterwards (Lean's environment does); and the guard on unit-like
  structures (P4) is cautious until task 5.2.2.
- **Fixed limits being made dynamic (plan 6.2.0; the owner's held gate).**
  Done: universe arguments, parameters and the level context have no fixed
  limit. In progress: the walk, frame and binder depths (Mathlib terms nest
  to 1,221). The stores' defaults are still 64 term nodes, 64 levels, 64
  names and 32 declarations, and `bin/leanforth check` keeps them, so it
  handles only fixture-size exports. The checker copies its input (about
  80 bytes per node) and, in an earlier `Init` run, peaked at 1.27 GB;
  Mathlib has not been fed to it. The rebuild passes recurse on the host's
  return stack (about 1,200 cells at worst today) and must move to explicit
  stacks first.
- **Speed.** Free variables make checking 10-25% slower until the
  loose-variable range (ADR 0014 Q12) is built (accepted by the owner).
  The move to heap stores first cost about 1.2 times on the 2,000 random
  checker trials (an early report of 2.2 times misread cumulative times,
  corrected by agent KC); after KC's speed work the trials take 5% fewer
  instructions than before the move, and `Init`'s feed and check are much
  faster (96 s to 12 s and 63 s to 9 s, KC's merge 87f0f79). Speed against Lean is not yet measured,
  and the owner's one-thread speed goal is open.
- The `Init` result (184 data types and 1,014 definitions and theorems
  accepted, none rejected) is dominated by *unknown* and *unsupported* for
  the features above.
- The owner's axiom policy (NOT PROVED labels, `--standard-axioms-only`) is
  decided but not implemented, and the owner has asked to consider changing
  it (plan 5.3.3).
- Not yet reported per check: fuel used, memory and CPU (plan 6.5.2); large
  proofs have no splitting guidance yet (6.5.3); the worker count is not yet
  a setting measured beyond the core count (6.5.4); Lean's own test suites
  and other Lean libraries are not yet run (6.4.2, 6.1.6).
- The program track's proofs are about the IR's Lean semantics, checked by
  Lean; that Gforth runs the words as the IR says, and that the reader
  translates faithfully, are tested, not proved. IR 0.2 (redefinition,
  output words) is approved as a design, not built; today's reader refuses
  redefinitions.
- Only Lean 4.35.0 exports in format 3.1.0 are read; a file cut off cleanly
  between two lines is not yet detected by default (checksum manifest
  planned); only Linux/WSL with Gforth 1.0.0 and 0.7.3 is tested.

## Update, 2026-11-03 evening (commit `7ffbfff`)

Since `6cd4e00`: fast parallel checks and the Lean cache (agent TT); the
two-mode program words (agent PW; [parser] gate pending); the run-record
fixes (agent RP; [format] gate pending a further fix); the owner's answers
on data types, axioms, the importer stage (now approved) and flags (the
default is always Lean); and the checker on heap stores with the stage feed
(agent KC; [kernel] gate pending), which lets `Init` be checked end to end
(37 of 59,349 accepted, the rest mostly *unsupported* until unfolding and
data types exist). Run for this documentation change: `make test` only, not
`make check`; the figures come from the cited documents and commit
messages. In progress: derivation log and proof outline (RB), non-recursive
inductive blocks (I21), free variables and local context for unfolding
(D2A). Next on the critical path: unfolding (phase 4) and inductive types
(phase 5), and clearing the pending gates.

## Update, 2026-11-04 (commit `6266f70`)

Since `7ffbfff`: the owner approved the program words, run-record format 0.1,
the import-read change, the derivation log and `leanforth print` (gate D5),
free variables (plan 4.2.2a), the first data types (plan 5.2.1a, with the
condition that its temporary differences close to 100% Lean) and the IR 0.2
design. The owner held the checker on the large store [kernel] until the
fixed limits of 64 are dynamic; universe lists are done (plan 6.2.0 part a)
and depth limits are in progress. `Init` end to end: 184 data types and 1,014
definitions and theorems accepted, 0 rejected or invalid; its feed and check
are 8 and 7 times faster (96 s to 12 s, 63 s to 9 s; agent KC's figures from
the merge message). The 2026-11-04 crashes were the strict test wrapper
calling itself; fixed. New plan items: 6.1.6, 6.4.2, 6.5.2, 6.5.3, 6.5.4 and
5.3.3. Every gap from Lean is temporary and has a plan task that closes it.
Run for this documentation change: `make test` only, not `make check`; the
figures come from the cited documents and commit messages, and the CI status
of `6266f70` was not looked up. Next on the critical path: depth limits
(6.2.0b), then unfolding (4.2.2b-e) and recursive types (5.2.1b), structures
(5.2.2) and literals (5.2.3) on the way to `n + 0 = n`.

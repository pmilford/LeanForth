# LeanForth project progress

Snapshot: **2026-11-12, afternoon**, at commit `700c4a1` on `main` (the
sections below the opening paragraph are mostly the 2026-11-04 late snapshot at
`bba87db`; previous
snapshot 2026-11-04 at `6266f70`; before that 2026-11-03 evening at
`7ffbfff`, the same day at `d6233af` and 2026-11-02 at `fc558cc`). These are milestones, not estimates of percentage
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

**What LeanForth is and is not (2026-11-12).** LeanForth today is only the checking half of Lean (the kernel): it re-checks proof terms that Lean produced and exported (NDJSON), including all of Lean's `Init`. It has none of Lean's front end, the larger half: no elaborator (implicit arguments, numerals, unification), no type classes or coercions, no tactics, no pattern matching or recursion compilation, no evaluation. So it cannot yet turn a written theorem into a proof; Lean does all of that before the export. LeanForth text is checked by the kernel since 2026-11-12 (plan 8.2.1a, c, d); there is no program verifier: for the clamp word LeanForth re-checks the proofs Lean wrote (plan 5.5.1, branch `program-551`). The front end is plan phase 8 ([PLAN_DRAFT.md](PLAN_DRAFT.md)), being re-planned from 2026-11-12.

## Now, next, later (updated 2026-11-13)

The single list of what is being worked on (owner, 2026-11-12; replaces the near-term queue of
[DEVELOPMENT_ROADMAP.md](DEVELOPMENT_ROADMAP.md), stale since 2026-11-03). `scripts/push.sh` refuses to push plan
status changes when this date is older than them. Stages are those of the
[done checker](../development/DONE_CHECKER.md).

**Now**
- LeanForth text checked by LeanForth's kernel, with Init imported for real (plan 8.2.1a, c, d): works end to end (done check docs/development/done-checks/2026-11-12-lf-files.md); owner gates [parser], [bypass], [import] approved by the owner 2026-11-12.
  `leanforth check [--env EXPORT] FILE.lf` checks hand-written kernel terms; no elaborator or tactics yet. 8.2.1b, e, f
  and g are not started.
- Fixes before tonight's run: the performance review's findings (rvPF1), the broken coverage tool and a coverage
  ratchet, the documentation the done-checker audit found overstated or stale, and real bugs from the Forth backlog
  reviews (the parallel scheduler's use after free when memory is full; a snapshot layer's full reported as invalid;
  Gforth-only words outside the portability layer).
- All of Mathlib on the night's build (`d789e45f`, verdict version 9, 2026-11-13): 729,263 of 729,263 accepted, snapshot saved; see the Mathlib line below.
- The front end, LeanForth's own elaborator and tactics (plan FE1-FE12, replacing 8.3.1-8.3.2; [design](../design/FRONT_END.md),
  [ADR 0021](../adr/0021-front-end.md) proposed, D1-D3, D5, D7 and Amendment 1 (`sorry` as in Lean) decided by the
  owner). FE1, the first theorem proved from LeanForth text ($0 + n = n$ by induction, no hand-written proof term, no
  Lean tool), is being built. On main (2026-11-13): FE1a (natural reader) integrated; FE1b (metavariables, with
  assignment marks) tested alone; FE1c (Lean's level unification and normalize, instantiate and head beta: 153 cases
  equal to pinned Lean) tested alone in part; FE1d (elaboration data) integrated; FE1f (the hand-over of an elaborated
  declaration to the kernel) tested alone, reached by no user command before FE1e; FE6a (casesOn, recOn and ctorIdx
  built as Lean builds them, compared over Init) tested alone; FE1c's environment view, whnfCore and first inferType cases tested alone; FE1g-2 (tactic proofs
  read; a well-formed one stops "not supported yet") tested alone; FE1g-1 (each goal's own local context, the goal
  list and `.goals` printed as Lean prints goals: 15 of 18 states equal) tested alone; the library `lib/runs.fs`; FE1i-4 (signed big integers, `lib/bigint.fs`)
  tested alone; FE1c's instantiateMVars beta and delayed steps and marks as serials tested alone (179 of 187 cases
  equal to pinned Lean). On main since 2026-11-13, approved by the owner: FE1e1 (elaboration data format 2,
  [import]/[format]) and the job pool failing closed when threads are refused ([runtime]). Library: `lib/sort.fs` (a stable sort the kernel's sorts can adopt, FRK C2) tested alone. Designed:
  FE1e, FE1g, FE1i, FE2. Nothing is proved by
  LeanForth yet. Natural statements (8.6.10) are FE2, `add_comm` natively (8.6.11) FE5.
- Program track, restarted 2026-11-12 after being parked since 2026-11-04: LeanForth re-checks Lean's proofs of
  the clamp word's obligations (plan 5.5.1): works end to end (done check docs/development/done-checks/2026-11-12-program-track.md); owner gates [bypass] and [runtime] approved 2026-11-12, merged.
  `python3 scripts/program_receipt.py export OUT.ndjson` has pinned Lean export the contract theorem and its two
  obligations with their closure (4,277 declarations); `bin/leanforth check` accepts them, and rejects an export whose
  program IR term, postcondition or proof term was changed after Lean proved it; the clamp receipt (schema 0.3, the result label removed by the
  owner's [format] decision of 2026-11-12) states LeanForth's verdict. Lean wrote the proofs: LeanForth has no
  tactics and wrote no proof. Nobody has proved SHA-256 as a whole; there is no `leanforth verify`. The SHA-256 helper words' proofs (sha-rotr, sha-ch, sha-maj, sha-big-sigma0) are re-checked the same
  way (2,890 declarations); their receipts wait for schema 0.4.

**Next**
- Less repeated testing of small work (plan 9.4.6, owner 2026-11-13): designed
  ([review](../development/TEST_WORKFLOW_REVIEW.md): `lib/sort.fs` took about 12 full-suite runs and 2-3 hours of
  machine time to reach GitHub; 3.6 hours of CI in six hours of pushes); decided by the owner 2026-11-13, rules in
  AGENTS.md, the scripts not started.
- The Forth refactoring batches of the three backlog reviews ([log](../development/forth-reviews/LOG.md), plan
  9.4.5), tests first, every verdict and fuel count identical.
- Program track: a user command `leanforth verify` (8.4.1): designed 2026-11-13 ([design](../design/VERIFY_COMMAND.md),
  sub-steps 8.4.1a–n, six owner questions); nothing built. Its first steps need no owner answer: the driver that runs
  5.5.1's pipeline for any IR 0.1 word (8.4.1b), the contract reader (8.4.1g) and receipt writer (8.4.1h) in Forth. The
  SHA-256 helper words' receipts (schema 0.4, IR 0.2, at the owner's [format] gate).
- A rule-by-rule audit of AGENTS.md against practice.
- Snapshots that read the two previous format and verdict versions (6.2.5c): designed, the owner's four questions
  answered 2026-11-12 ([design](../design/SNAPSHOT_COMPATIBILITY.md), ADR 0020 Amendment 5 proposed); steps c1 to c5
  written and tested alone on branch `snap-compat` (`edb5554`), the Forth review and its three re-checks not blocking,
  approved by the owner 2026-11-13; being merged with the kernel refactor.

**Later**
- Proof development (owner, 2026-11-12; long term, after strict Lean compatibility): research note
  [PROOF_DEVELOPMENT.md](../design/PROOF_DEVELOPMENT.md), plan rows PD1–PD15, all not started; PD1, Lean's `sorry`
  reported NOT PROVED with the conditional report, is decided (ADR 0021 Amendment 1) and fits with FE1g and FE5.
- Speed: the export reader and the remaining validity checks; Physlib; `print --snapshot` (8.6.9); term memory
  (6.5.9); a second Forth system and a 32-bit host (9.4.1); no Python requirement (9.4.3).

## Where things stand, in plain words

**Mathlib checked:** 729,263 of 729,263 declarations of the pinned Mathlib export (Mathlib `v4.35.0`, commit `56a0058`, export sha256 `18448e5d...59c6`; checked-declaration coverage, not estimated effort) accepted, run on build `d789e45f` (verdict version 9) on 2026-11-13, 02:16-04:38, with `--jobs 8 --fuel 250000000 --memory-per-check 8192`: 8,504 s wall, 58,130 s user, 22.6 GB peak, exit 0, its snapshot saved (2.30 GB); the machine was shared with other work, so the time is not a clean measurement (run record `.claude/work/overnight/full-d789e45f.txt`, with `run-v9.log` and `full-d789e45f.err`, untracked). The gates before it passed: the arena (84 bad inputs rejected, 124 good accepted, 4 good declined as expected) and all of `Init` (59,349 accepted). Earlier: the same count on build `b74a04d` (2026-11-12, 12,134 s, read by the audit [done-checks/2026-11-12-audit.md](../development/done-checks/2026-11-12-audit.md)). [Details](#full-mathlib).

**Plan row statuses (2026-11-12):** every status in [PLAN_DRAFT.md](PLAN_DRAFT.md) now uses the stage words of [DONE_CHECKER.md](../development/DONE_CHECKER.md) (`scripts/check-progress.py` checks all rows, dated or not). Earlier wording was mapped on each row's own evidence and kept in the row as `was "..."`; rows that said "done" without a done-checker report were lowered with "done check owed"; rows the [audit](../development/done-checks/2026-11-12-audit.md) ran are "works end to end".

**Current state, 2026-11-12 afternoon (main `700c4a1`, verdict version 9).**
Today LeanForth **re-checks proofs that Lean produced and exported** (NDJSON); it does
check LeanForth text only as hand-written kernel terms with no elaborator or tactics (plan 8.2.1a, c, d: works end to end (done check docs/development/done-checks/2026-11-12-lf-files.md); owner gates [parser], [bypass], [import] approved by the owner 2026-11-12; 8.2.1b, e, f and g not started). Re-checking Lean's export of all of
Mathlib gave Lean's verdict on every declaration: all **729,263 of
729,263 accepted** on build `b74a04d` (before K1 and PERF1; exit 0; one NOT PROVED,
`sorryAx` itself, as in Lean), on 8 workers with fuel 250,000,000,
`--memory-per-check 8192` and `--no-manifest`: 12,134 s
(3.37 h) wall, 92,220 CPU seconds, 29.4 GB peak, 27.1 billion fuel steps; checking
against the saved snapshot takes 425 s and 9.5 GB. The proofs were made by Lean. `Init`:
all 59,349 accepted (one NOT PROVED; `--resources --jobs 2` on this build, 532 s, 842 MB).
The **large Lean Kernel Arena tests** (std, con-leche, cslib, navier-stokes) were accepted
on `b74a04d` at fuel 250M, as the official checker does (at the default fuel cslib had 1
exhausted; in the small bundle 84/84 bad were rejected, 124/128 good accepted and 4 good
performance tests timed out at 120 s). Since that run:
the review fixes FXK and FXR, the nested passes' memo (MO), and on 2026-11-12
afternoon **K1** (plan 4.2.7d: typing aside follows Lean's infer-only mode and
rejects where it throws; this closed a soundness gap, small exports Lean rejects
had been accepted, none in Mathlib or the arena since Lean accepts all of those),
**L1/G1** (6.2.5b), and **readable mathematics** in `leanforth print` (notation
table, plan 4.4.3) with **five demos**: Lean proves each theorem and LeanForth re-checks the proof terms in
Lean's export ([DEMOS.md](../user/DEMOS.md), plan 8.6.6); the LeanForth words shown there
are the statement printed from that export, not runnable input. The Mathlib snapshot of `b74a04d`
(version 6) loads on this build only with `--snapshot-stale-ok`; a full Mathlib
run on version 9 is scheduled for the night of 2026-11-12. **Approved by the
owner on 2026-11-12:** S5/S5B, S7, IO, SN2-SN5, PF C1, SH, PF task 6, MB, R5, NS,
MO, K1, L1, G1 with their review fixes ([decisions](OWNER_DECISIONS.md)). **In
progress:** one speed and memory pass (PERF1) that keeps every verdict and fuel.
Details: [Limitations](#limitations), [Full Mathlib](#full-mathlib);
the sections below are the 2026-11-04 snapshot except where dated.

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
cases and 69 table cases give Lean's answers. The declaration check and the
checked environment it publishes into are still in their review gates.

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
   (part b) were finished the same day (milestone 9 below).
7. **Program words, run records and IR 0.2 approved** (see the gates
   table): IR 0.2's design and, on 2026-11-04, its [parser] implementation.
8. **A test-suite crash found and fixed.** Both the WSL crash and the Claude
   Code crash of 2026-11-04 were one bug: the new test wrapper
   `scripts/gforth-strict.sh` called itself, a fork bomb of about a thousand
   copies that exhausted 39 GB of memory and 16 GB of swap. Fixed in
   `e6a0a74` with self-reference and depth guards; no work was lost (the
   uncommitted work of the agents was saved as WIP commits).

**Milestones of 2026-11-04, late** (merged since `6266f70`; each gap named
is temporary and has its closing task):

9. **The checker on the large store, with no depth limit: approved**
   ([kernel], owner, plan 6.2.0 parts a and b, state **done**). Every pass
   keeps its pending work on explicit growable stacks in the heap, so no term
   is too deep: 2,000- and 10,000-deep chains agree with pinned Lean on every
   row. Independent re-review: nothing blocking. Temporary gaps: time grows
   with the square of a term's depth (plan 6.5.5, not started) and a few
   fixed capacities remain (6.2.0, 6.2.2, 6.2.4). **Resource refusals are not
   verdicts** (owner, rule BL-9): Lean's own depth and time-out refusals, like
   LeanForth's fuel (*exhausted*) and memory (*full*), say "ran out of a
   resource", never "wrong"; LeanForth does not copy Lean's counters.
10. **Recursive data types** (plan 5.2.1b, `Nat`, `List`, reflexive types;
    state **in progress**: merged, **gate not passed**). The inductive table
    has 198 cases against pinned Lean; tasks 5.2.1a-b give Lean's verdict on
    133 of 140 rows, 7 pending on unfolding. On `Init`, 261 of 604 data-type
    blocks are accepted (was 184), none rejected. Its independent review
    found **two wrong acceptances on hand-made files** (declarations Lean
    rejects); they are being fixed, and the owner's gate is asked only after
    a clean re-review. Until then nothing it accepts is trusted.
11. **Unfolding, first half** (plan 4.2.2b-c, state **in progress**: merged,
    gate review running). Lean's `whnf`, unfolding of definitions and
    theorems, and the quick check for definitional equality are built; 44 of
    50 comparison rows are decided and none contradicts Lean. 11% fewer steps
    on the trial workload. (Status on main at 408839a, 2026-11-10: the full
    lazy strategy, eta, proof irrelevance and `let` are merged, gate review
    owed; see "Status words" under Limitations.)
12. **IR 0.2 and the first SHA-2 words proved by Lean** ([parser] implementation
    approved). Lean proves `sha-rotr`, `sha-ch`, `sha-maj` and `sha-big-sigma0`
    equal FIPS 180-4's ROTR, Ch, Maj and Σ0 for every 32-bit input (4 of
    SHA-256's 8 helper functions; SHA-256 itself is not proved, and
    `src/lib/sha256.fs`, tested against the standard vectors, does not load
    these words). Still to
    do: `sha-shr`, Σ1, σ0, σ1.
13. **The command line.** `leanforth check` works on whole libraries: it
    stages the export and feeds the checker like the `Init` run, with
    `--resources` (time per phase, peak memory, fuel, the ten costliest
    declarations) and `--json` (report schema `check-report-0.1`; its
    [format] gate **approved** 2026-11-04). Owner choices: a declaration that is
    NOT PROVED (it uses an axiom outside the three standard ones) exits **0 as
    Lean does**; `--strict-axioms` makes it exit 6; the default engine is
    Gforth's checking one and `--fast` selects the quicker one. Neither flag
    is implemented yet (state **in progress**, plan 3.4, 5.3.1). Names are
    escaped (`«»`, as Lean does) so a crafted name can never forge another
    line. Figures for `Init` are under "Check Lean's whole `Init` library"
    below.
14. **`leanforth print` on whole libraries,** and the statement in **three
    forms**: Lean's notation, mathematics (LaTeX; `--latex`) and LeanForth
    words, which the authoring words read back to the identical term. Plan
    8.6.1 and 8.6.2 are **done**, and so is the print part of 3.4.1. A new
    page explains one symbol in three places (Forth's `+`, its model, Lean's
    `+`). Not started: 8.6.3 (a whole export written as one `.lf` file).
15. **Native LeanForth checking: design accepted** (ADR 0017 Amendment 1,
    owner's answers recorded). Forth's own interpreter runs theorem text from
    a file, at the prompt or inline between `lf[` and `]lf` (values passed in
    with `param:`); a library such as `Init` is one vocabulary looked up by
    hash index; the owner's concern about letter case is answered by an
    exact rule per layer, tested on `Init`'s 31 case pairs on both Gforths.
    Plan 8.2.1 is split into steps 8.2.1a-g: 8.2.1a, c and d works end to end (done check docs/development/done-checks/2026-11-12-lf-files.md); owner gates [parser], [bypass], [import] approved by the owner 2026-11-12; 8.2.1b, e, f and g are not started.

**The checker on the large store was held in the morning and approved in the
evening of 2026-11-04.** The owner had asked whether the fixed limits of 64
are needed (Lean has none; Mathlib uses up to 30 universe parameters and
terms nest to depth 1,221); the gate was asked again once plan 6.2.0 made them
dynamic.

**What it cannot do yet (all temporary).** It cannot decide anything that
needs the rest of unfolding (phase 4, tasks 4.2.2d-e), an indexed data type
(5.2.1c), mutual or nested blocks (5.2.5), a structure (5.2.2) or a number
literal (5.2.3) — which is nearly all of real Lean code and all of Mathlib.
`bin/leanforth check` now handles any size of export; the first big-library
run is below.

**What you can do with Mathlib today** (the owner asked):

| You can | You cannot yet |
| --- | --- |
| Read and validate the whole Mathlib export in Forth: all 110,895,826 records (6.3 GB) in about 1 min 49 s with `gforth-fast`, in 17 MB of memory; every record's shape and every reference to an earlier record is checked, and the result equals the independent Python reader's field for field | Keep what was read: the checker's stores grow (`Init` fits; `bin/leanforth check` takes any size), but Mathlib has not been fed to them |
| Check Lean's whole `Init` library end to end from the command line (`leanforth check --resources init.ndjson`: staged, fed in file order, checked). **Latest figures, from commit `9df4fa3` (2026-11-04, before recursive types merged; [COMMAND_LINE.md](../user/COMMAND_LINE.md#a-whole-library-leans-init)):** 59,349 declarations: 1,618 accepted, 0 rejected, 3,748 unknown, 53,800 unsupported, 179 exhausted (out of fuel), 4 full (more than 16 dependencies, plan 6.2.0); total 258 s with `gforth-fast` (stage 19 s, feed 19 s, check 220 s), peak 1,218 MB; the default checking engine takes about two and a half times as long. **After recursive types (`13b9a65`, probe in ADR 0015):** 261 of 604 data-type blocks accepted (was 184) and 1,609 other declarations (was 1,015), none rejected. The command-line page has not been re-run on `13b9a65` or later; that run is still to do | Check a real Lean theorem such as `n + 0 = n`, which needs structures, literals and the rest of unfolding (see the milestones) |
| Print a numbered, readable proof outline of an accepted declaration with `bin/leanforth print`, on any size of export (`Init` theorems too), with the statement in three forms: Lean, mathematics in LaTeX (`--latex`) and LeanForth words | Print proofs that need unfolding or data-type steps not yet built |
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
| Heap stores and the stage feed; the checker on the large store (ADR 0016 C9 step 3 in part; plan 1.1.5, 3.2.2) | [kernel] | **approved** 2026-11-04 (owner), after the fixed limits became dynamic: plan 6.2.0 part (a) universe lists and part (b) no depth limit (agent KC, `215a406`); re-review rvKC REVIEW-B nothing blocking ([decisions](OWNER_DECISIONS.md#checker-on-the-large-store-approved-resource-settings-2026-11-04-late)) |
| Data types, ADR 0015 (inductive types) | design | **accepted as a design** 2026-11-03; each implementation task has its own gate |
| Recursive data types (plan 5.2.1b; agent N1, `13b9a65`) | [kernel], [import] | **approved** 2026-11-04 (owner), after review rvN1 found two wrong acceptances on hand-made files, both fixed, and a second round found none; mutual blocks (5.2.5a) with it |
| Unfolding: `whnf`, delta, the quick equality check (plan 4.2.2b-c; agent U4, `998b89d`) | [kernel] | **approved** 2026-11-11 (owner) with the full lazy strategy (4.2.2d), after review rvCONV's two blocking findings were fixed (FX1) |
| Report format `check-report-0.1` (`--json`, schema `schemas/check-report-0.1.schema.json`; plan 3.4.3) | [format] | **approved** 2026-11-04 (owner); review fixes merged (`dd38dee`: inconsistent exit-0 reports refused, `--fuel` bounded, a run that stops is never ok); `--strict-axioms` and `--fast` merged (`84725e6`) |
| Report format `check-report-0.2` and run records `run-record-0.2` (the *skipped* verdict of unsafe and partial declarations, plan 5.2.7; schemas `schemas/check-report-0.2.schema.json`, `schemas/run-record-0.2.schema.json`; the 0.1 files kept unchanged, and reports without *skipped* still validate under 0.1) | [format] | **approved** 2026-11-11 (owner; review rvUNNI M2 recommended a version bump over changing 0.1 in place; agent FX8) |
| Report formats `check-report-0.4` (final runs) and `check-report-0.5` (snapshot runs), run records `run-record-0.3`: 0.2, 0.3 and 0.2 without the member `label` (schemas `schemas/check-report-0.4.schema.json`, `schemas/check-report-0.5.schema.json`, `schemas/run-record-0.3.schema.json`; the earlier files kept unchanged, and every new report and record with the label put back validates under them) | [format] | **decided** 2026-11-12 (owner: results carry no label; agent PA made new versions, as rvUNNI M2 did) |
| Approval round of 2026-11-11 ([OWNER_DECISIONS.md](OWNER_DECISIONS.md#approval-round-of-2026-11-11)): unfolding and the lazy strategy, `let`, eta, proof irrelevance, structures and projections, K-like recursors, literals, axioms with allowlist v1, opaque declarations and quotients, nested inductive types, unsafe and partial declarations skipped; result caches, compact-store steps S0-S4 and S6, the fuel model of ADR 0014 Amendments 3-5; importer numbering, `--any-lean-version`, Lean's JSON spellings, `print --lf` numeric name parts, print hooks | [kernel], [import], [format] | **approved** 2026-11-11 (owner), each after Lean-compared tests and an independent review with its blocking findings fixed; the export header stays strict by default, and Lean's official export checker is the referee for hand-made export files. Not yet asked (review done or running, approval owed): compact-store S5 and S5B, S7, IO, snapshots SN2-SN5, PF C1 and the 100,000,000 default fuel (ADR 0014 Amendment 6), SH |
| Native and inline LeanForth, ADR 0017 Amendment 1 (plan 8.2.1) | design | **accepted** 2026-11-04 with the owner's answers (OQ-1 revised, `lf[ ]lf` with `param:`, libraries as vocabularies, case rules); each step 8.2.1a-g has its own gate ([parser], [bypass]; 8.2.1g [kernel]) |
| Printer review fixes (names escaped in every form, growable lines; plan 8.6.2) | untrusted presentation | merged `bba87db` after independent review; no owner gate |
| Non-recursive data types (plan 5.2.1a) | [kernel], [import] | **approved** 2026-11-04 after three review rounds, the last clean. **Condition (owner):** its temporary differences from Lean close to 100% compatibility, any stricter behaviour only behind an opt-in flag: (1) a file using `T.rec` without declaring it gets LeanForth's own generated recursor, as in Lean; (2) a block rejected at the final comparison (B3) keeps its type and constructors usable afterwards, as in Lean's environment; (3) the guard on unit-like structures closes with task 5.2.2. **Condition met** 2026-11-04 after rounds 4–6: (1) and (2) done, an empty block now rejected as in Lean; every remaining gap temporary with its task ([decisions](OWNER_DECISIONS.md#data-types-first-step-condition-met-2026-11-04-late)) |
| Free variables and the local context (plan 4.2.2a) | [kernel] | **approved** 2026-11-04 after two review rounds; accepted cost: checking is 10-25% slower until the loose-variable range of ADR 0014 Q12 is built |
| Derivation log and proof outlines, `leanforth print` (plan 2.4.1, 2.4.4; ADR 0013) | gate D5 | **approved** 2026-11-04 after three review rounds; accepted memory: about 218 KB per context while the log is on, under 1 KB off |
| Run-record reading change: both passes and the recorded SHA-256 must agree, with or without the manifest (`src/import/checker-input.fs`) | [import] | **approved** 2026-11-04 after four review rounds, the last clean |
| IR 0.2 design (ADR 0019 Amendment 1: redefinition with Forth's early binding, output words as effects, SHA-2 additions `LSHIFT`, `-rot`, number prefixes, 32-bit literals) | [parser] design | **approved** 2026-11-04 as a design; **implemented** 2026-11-04 (agent IR3, merged `cc3afaf`; independent review rvIR3: nothing blocking, its low findings fixed); the [parser] implementation gate **approved** 2026-11-04 (owner); receipt schema 0.3 comes to the [format] gate with the first receipt that needs it |
| Design records ADR 0010, 0013, 0015, 0016, 0017, 0018 | design | **accepted** (0017 on 2026-11-02; the rest 2026-11-03; 0015 as a design, with a gate per task) |
| Checked environment v0 (2.2.2) | [kernel] | **approved** 2026-11-03 |
| Declaration check (2.2.3) and the level fix | [kernel], [bypass] | **approved** 2026-11-03 |
| Program reader (Forth to program IR, 2.5.3) | [parser] | replaced by the owner's two-mode design (ADR 0019, accepted in direction). The two-mode program words (verify mode emits the program IR, run mode executes as plain Forth; the portable mode shift is primary and the alias vocabulary is kept beside it; 287 inputs after the review fixes) are **approved** 2026-11-04 after three review rounds, with stated limits (source-to-IR is tested, not proved; a standard word redefined before the words load is not noticed). Next, IR 0.2 (row below) Today's text reader stays as a cross-check, then retires |
| LeanForth syntax words (8.1.2) | [parser] | **approved** 2026-11-03, after two clean review rounds (term-for-term equal to Lean on 67 declarations) |
| Program receipt schema 0.2 (2.5.1) | [format] | **approved** 2026-11-03 (schema pinned by hash; any change is a new version) |
| Program receipt schema 0.3 (5.5.1) | [format] | **decided by the owner** 2026-11-12: 0.2 without the result label (`check.label`), as check reports 0.4/0.5 and run records 0.3; 0.2 stays readable. Receipts for IR 0.2 programs take 0.4 |
| Run-record format 0.1 (environment identity, manifest-enforced field tied to the bytes read, both import passes compared, blank-looking names refused) | [format] | **approved** 2026-11-04 after three independent review rounds (`docs/programming/RUN_RECORDS.md`) |
| Axiom policy and defaults (owner, 2026-11-03) | policy | decided: `sorryAx` and any axiom outside the three standard ones get Lean's verdict, labelled **NOT PROVED** (the flag `--standard-axioms-only` refuses them); with no flags LeanForth is always Lean. **Exit status (owner, 2026-11-04 late): 0 like Lean by default, 6 with `--strict-axioms`.** The label and the exit status are not implemented in full yet (plan 5.3.1); the owner asked on 2026-11-04 to consider changing the rule (plan 5.3.3, options to be brought in plain words) |
| Big-number library (`lib/bignum.fs`, for literals) | [forth-review] | review found one serious memory bug in printing; fixed and merged 2026-11-03 (`ed4dab7`, merge `4c714f5`); **approved** 2026-11-11 (owner) with literals (plan 5.2.3) |

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
   *accepted; axioms: none*,
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
   and, part (b), terms and levels no fixed depth: every pass keeps its
   pending work on explicit stacks in the heap, checked against Lean with
   lambda, application and successor chains 2,000 and 10,000 deep, all
   agreeing (the local context, too, is limited only by the heap); the
   work grows with the square of the depth, a temporary gap (6.5.5), and
   the trial workload runs about 9% slower); feed
   declarations to the checker in file order (3.2.2; works for `Init`
   today, **approved** 2026-11-04 late); re-export byte for byte and compare with
   Lean's file (3.2.4, **done 2026-11-03**); the checksum manifest checked by default and an
   upgrade test for new Lean and Mathlib versions (owner, 2026-11-03);
   `leanforth check FILE.ndjson` and exit codes (3.4; `leanforth print`,
   readable proof outlines from the command line, merged and **approved** by
   the owner 2026-11-04, gate D5); the JSON API v0 for AI tools with schemas and golden examples
   (3.5); LeanForth text checked by the same checker (8.2.1a, c, d). *You will see:* one
   command checks a Lean export with only Forth installed. Today
   `bin/leanforth check` takes whole libraries (`Init` in about four
   minutes with `--fast`'s engine, `gforth-fast`); its report format
   (`--json`) awaits its [format] gate, and `--strict-axioms` and `--fast`
   are to come.
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
   needs: 5.2.1b recursive types (`Nat`; merged, its gate not passed), 5.2.2
   structures and projections, 5.2.3 number literals, and from phase 4 the
   unfolding steps 4.2.2b-e (free variables, 4.2.2a, are done; b-c are merged
   and in gate review). *You will
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
2026-11-03). *Plainly, as of 2026-11-12: LeanForth has not proved or checked any program proof. The program proofs that exist (the clamp contract, four SHA helper words) were proved and checked by Lean only; `src/lib/sha256.fs` is tested against the standard vectors, not proved; plan 5.5.1 (LeanForth re-checks Lean's program proofs) is in progress and `leanforth verify` (8.4.1) is not started.* Its flagship target is LeanForth's own SHA-256: a Lean
specification of FIPS 180-4 checked against the NIST vectors first, then
proofs that the Forth words compute it — the helper functions, the loops
of the block compression, then padding and buffers — as the program IR
gains loops and memory, and finally checked by LeanForth itself
([plan](PLAN_DRAFT.md#program-track-goal-most-of-forth-2012-core-owner-2026-11-02)).
Before that: contracts for the five other example words (done 2026-11-03) and
the owner's [parser] and [format] decisions on the program reader and
receipts (both **approved** 2026-11-04). IR 0.2 (redefinition, output
words and the SHA-2 additions) is **implemented and approved** (2026-11-04,
[parser] implementation gate), and stage SHA-2 has **started**: the helper
words `sha-rotr`, `sha-ch`, `sha-maj` and `sha-big-sigma0`, as plain Forth
program words (`src/program/sha-words.fs`), are proved in Lean equal to
FIPS 180-4's ROTR, Ch, Maj and Σ0 for every 32-bit input on cells of at
least 33 bits; `sha-shr`, Σ1, σ0 and σ1 remain, and `src/lib/sha256.fs`
does not run these words yet.

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
| T9 full Mathlib | 0 | 3 | 2 |
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
| T10.1 Forth words that build terms | syntax words merged | 15 example files and 50 printer cases round-trip; 42 `#print` lines from 14 fixtures equal pinned Lean's; `leanforth check FILE.lf` hands the terms to the checker (8.2.1a, c, d: works end to end, done check docs/development/done-checks/2026-11-12-lf-files.md) |
| T9.4 Mathlib time and memory | storage design accepted | ADR 0016: 2.94 GB stored, 4.16 GB peak, measured |
| T5.3 / T6 feeding the checker | `Init` fed end to end (plan 3.2.2, 1.1.5, in part) | 59,349 declarations fed; at the 2026-11-03 snapshot 37 accepted, 0 rejected, 59,025 unsupported at 100,000 fuel ([ADR 0016, step 3](../adr/0016-compact-store.md)); since task 5.2.1a, 184 data types and 1,014 definitions and theorems accepted, 0 rejected or invalid ([ADR 0015](../adr/0015-inductive-types.md)); reviews done, [kernel] gate held until the limits are dynamic |
| P6 program reader | two-mode program words approved [parser] 2026-11-04 | 273 inputs agree with the old reader, 4 intended differences, 287 after the review fixes ([program IR](../programming/PROGRAM_IR.md)); IR 0.2 implemented 2026-11-04, [parser] implementation gate pending |
| Plan tasks 5.2.1a, 4.2.2a, 2.4.1, 2.4.4 | merged and approved 2026-11-04 | see the gates table; the roadmap tasks they belong to (T5.3, T6, T10) stay in progress |
| Plan 6.2.0 parts (a), (b) | no fixed limit on universe lists or depth; **approved** 2026-11-04 late | 100, 300 and 1,000 universe parameters agree with pinned Lean (24 rows); 2,000- and 10,000-deep chains agree on every row |
| T5.3 checker, T6 | recursive types (5.2.1b) and the first half of unfolding (4.2.2b-c) merged, gates not passed | inductive table 198 cases; 133 of 140 rows of 5.2.1a-b give Lean's verdict; `Init`: 261 of 604 blocks accepted; 44 of 50 equality rows decided, none contradicts Lean |
| P6 program reader, P7 | IR 0.2 implemented and approved; first SHA-2 words proved by Lean | Lean proves ROTR, Ch, Maj, Σ0 for all 32-bit inputs; `sha-shr`, Σ1, σ0, σ1 remain |
| T6 / CLI | `leanforth check` and `print` work on whole libraries | `Init`: 1,618 accepted, 0 rejected of 59,349 (command-line page, `9df4fa3`) |

**Plan tasks by state (2026-11-04).** IDs are those of
[PLAN_DRAFT.md](PLAN_DRAFT.md); every row of the first table is merged. The
roadmap counts above are unchanged: they count the roadmap's acceptance
tasks, not the plan's.

| Plan task | State |
| --- | --- |
| 2.4.1 derivation log, 2.4.4 proof-outline printer, `leanforth print` (agent RB) | **done, approved** (gate D5) |
| 4.2.2a free variables and local context (agent D2A) | **done, approved** [kernel] |
| 5.2.1a non-recursive inductive blocks (agent I21) | **done, approved** [kernel][import]; the owner's 100%-Lean condition **met** 2026-11-04 (review rvI21 rounds 4–6): 94 Lean-checked rows, 88 with Lean's verdict, 6 pending on 5.2.1b and 4.2.2 |
| 6.2.0 parts (a) and (b) no fixed limit on universe lists or depth (agent KC) | **done, approved** [kernel] 2026-11-04 late (2 of 2 parts); the rest of 6.2.0 is part (c), next row |
| 6.2.0 part (c) the other fixed capacities: a check's dependencies, the dependency pool, a block's constructors, the signature index (agent KC) | **done on the branch**, review pending [kernel]; Lean's verdict at 41 and 1,001 dependencies, a pool of 66,066 and 600 constructors; on `Init` 0 *full* (31 before) |
| `leanforth check` on whole libraries and `--resources` (plan 3.4.1; the command-line part of 6.5.2; agent CLI2) | **done, merged**; report format at the [format] gate |
| 8.6.1 LaTeX printer mode, 8.6.2 statement in three forms; print part of 3.4.1 (agent PR) | **done** (untrusted presentation) |
| Program words (ADR 0019), run-record format 0.1, import-read change, IR 0.2 design and implementation | **approved** 2026-11-04 (see the gates table) |

| Plan task | State |
| --- | --- |
| 5.2.1b recursive types (agent N1) | **in progress**: merged, two wrong acceptances found by review being fixed; gate not passed |
| 4.2.2b-c `whnf`, delta, quick equality check (agent U4) | **in progress**: merged, gate review running (2 of 4 steps b-e merged) |
| 4.2.2d the full lazy strategy (agent U4); 4.2.4 function eta and 4.2.5 proof irrelevance (agent PE, 2026-11-05); 4.2.3 `let` (agent LT, 2026-11-05); K-like recursor reduction, part of 5.2.1c (agent KL, 2026-11-05); structure eta and unit-like types, part of 5.2.2 (agent SE, 2026-11-05); axioms with allowlist v1, opaque declarations and Lean's quotient, 5.3.1-5.3.2, 5.2.4, 4.2.6 (agent AX, 2026-11-05; allowlist v1 awaits the owner's approval; fixes by agent LE); result caches, 4.2.7 (agent CA, 2026-11-05); review fixes rvCONV (2 blocking) and rvCACHE (agent FX1), rvPARSE (FX2), rvAX (FX3: quotient names reserved), five planted faults repaired (FX4), rvKC (FX5), 2026-11-10; string literals, 5.2.3's string part (agent ST, 2026-11-10); the comparison's projection steps, 5.2.2 (agent PJ, 2026-11-10); level substitution that costs what it reaches, compact-store plan step S0 (agent S0, 2026-11-10; no rule change; Init 1M-line prefix check CPU 363 s -> 54.5 s, verdicts and fuel identical); audits and opening once per node, not per path, part of 6.5.5 (agent EX, 2026-11-10; ADR 0014 Amendment 2; Init 1M-line prefix: exhausted 17 -> 0, fuel 93M -> 39M); unsafe and partial declarations skipped as Lean's replay skips them, 5.2.7 (agent UN, 2026-11-10; new verdict *skipped*, [kernel][format]); nested inductive blocks, 5.2.5b (agent NI, 2026-11-10; Init 1M-line prefix after all merges: 8,672 of 9,202 accepted, 518 unknown, 12 exhausted, 0 unsupported; arena tests435 no wrong verdict); compact-store plan steps S1 (one joint scratch mark instead of hand-saved counts) and S2 (store headers checked at pass roots, nodes read by index; `lf-term-data@`) (agents S1, S2, 2026-11-11; no rule change; verdicts, fuel and trial digests identical); review rvPSE (PJ, S0, EX) not blocking, its fix FX7: level substitution per node with universe arguments too (2026-11-11); compact-store plan step S3, the hash-consed term store: 16-byte records with Lean's node facts, equal records one node (agent S3, 2026-11-11; no rule change; all of Init: 21 verdicts move to Lean's, peak memory 1,580 -> 1,279 MB, CPU +2-5%; the skeleton memo stays until S4; the store is not yet the compact tier itself, so the feed's copy remains until S5); compact-store plan step S6 parts a, d, e: instantiation as Lean's replace, node facts from the data word, Lean's infer-cache key (agent S6A, 2026-11-11; all of Init at default fuel: 55,587 of 59,349 accepted, 27 exhausted roots, every moved verdict to Lean's; CPU -17%; the 10,000-deep table 162 s -> 6.1 s; new fuel model in ADR 0014 Amendment 3 for the owner); step S6 part c: LeanForth's own audits once per node per check, every audit site kept (agent S6C, 2026-11-11; a defence change argued in ADR 0014 Amendment 4; all of Init at default fuel: 55,750 of 59,349 accepted (93.9%), 16 exhausted roots, 3,583 unknown that depend on them, fuel -33%); step S4: levels hash-consed, references interned, caches keyed by node (skeleton memo retired), Lean's == at every pair (agent S4, 2026-11-11; all of Init: 55,772 accepted (94.0%), 7 exhausted roots, check CPU 807 s, fuel -20%; the stamps stay until S5); default fuel raised from 2,000,000 to 20,000,000 per declaration (owner's approval to raise the default fuel, 2026-11-10): at 20,000,000 all of `Init` (59,349 declarations) is accepted with exit 0 on main af93afb (1,162 s, 1.15 GB), and Mathlib's first sixth gives 117,068 of 119,472 accepted (98.0%; 69 exhausted roots, 68 of them in the comparison; 5,715 s, 3.4 GB); compact-store step S5 parts 1-3: the checker reads the stage tier's expressions in place, copying only let, projection and mdata nodes and those above them (2.4% of Init); the full copy stays behind a switch (print uses it); scratch grows instead of fixed rooms (agent S5, 2026-11-11; all of Init both ways: same verdicts, feed 18.0 -> 2.5 s, peak memory 1,061 -> 546 MB; not yet: native let/projection shapes, retiring stamps and scratch identities, the printer reading the tier, deleting the copy; confirmed after the let-lambda fix: all of Init in place gives 0 verdict and 0 fuel differences against the copying main on all 59,349 declarations, peak 530 MB; Mathlib's first sixth loaded with fuel 1, to time the loading alone: in place 51.6 s and 1.06 GB, copied 131.8 s and 3.72 GB, main before S5 124 s and 3.37 GB); importer index numbering as lean4export's Export/Parse.lean v4.35.0 reads it (sparse, any order, a repeated index overwrites) and the opt-in `--any-lean-version` (agent IMP, 2026-11-10; [import][format]; review rvIMP not blocking, its findings fixed by agent FX6: Lean's JSON number spellings, unknown record members ignored, index maps freed) | **merged**; approved by the owner 2026-11-11 except compact-store step S5, whose round follows S5B [kernel] (4.2.3 also [import]); only the first importer (checker-input.fs) still refuses `let` |
| Merged 2026-11-11 evening (evidence on main `0627845`, reviews done, owner's approval owed unless noted): S5B (no input copy); IO (diagnostic 81 routes; arena wrong acceptances now rejected); SN1-SN5 (checked-environment snapshots: sections, tier save/load, environment save/reload, import and layers, stale flag and golden guard; plan 6.2.5 **in progress**, not done: the Mathlib snapshot is not yet saved and review rvSN4's finding B1 is open); PRG (`--progress`, streamed results, `scripts/export-slice.py`; no gate); ENG (`gforth-fast` default, `--checked`, `make engine-gate`; owner proposed it); PF batch 1 (default fuel 100,000,000, C1, verdict version 3); SH (shared input, plan 7.2.1) | **merged**; counted *done* only when approved and used by `leanforth check` |
| 5.2.1c indexed families, 5.2.2 structures and projections, 5.2.3 literals, 5.2.5 mutual and nested blocks, 5.2.6 per-declaration verdict for unclosed files | not started; they close the temporary gaps of 5.2.1a-b and are on the way to `n + 0 = n` |
| 3.4.3 `--json` report (`check-report-0.1`) | **done**: [format] gate approved 2026-11-04; `--strict-axioms` and `--fast` implemented (`84725e6`) |
| 6.5.5 work linear in a term's depth | not started (the quadratic cost is the temporary price of 6.2.0 part b) |
| 8.2.1a-g native and inline LeanForth (design accepted) | 8.2.1a, c, d: works end to end (done check docs/development/done-checks/2026-11-12-lf-files.md); owner gates [parser], [bypass], [import] approved by the owner 2026-11-12; 8.2.1b, e, f and g not started; 8.6.3 not started |
| SHA-2 helper words (program track) | **in progress**: 4 of SHA-256's 8 helper functions proved by Lean (ROTR, Ch, Maj, Σ0); SHA-256 itself is not proved; SHR, Σ1, σ0, σ1 remain. Since 2026-11-12 (branch `program-551`) Lean's proofs of the four are also re-checked by `bin/leanforth check` (2,890 declarations; sha-ch's old proof over a changed body, and a changed proof, rejected); no receipt until schema 0.4 |
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
| Q8 parallel program path | In progress: receipt schema 0.2, IR 0.1 with its Lean model and reader (plan 2.5.1–2.5.3), the IR interpreter's three-way comparison (2.5.4), the verification-condition generator v0 (2.5.5) and the first clamp receipt (2.5.6) pass `make check`; the reader's final review found nothing blocking (three small items being fixed); the reader ([parser]) and the receipt format ([format]) then go to the owner |
| Q9 consolidate experiments | Done 2026-11-02: 28 superseded modules and 91 test files retired with the owner's approval |
| Q10 refactor onto `src/lib` | Done (2026-11-02): every core and kernel module keeps its state in the per-task checker context (34 context members: stores, walk records, frames and module records; no global state left) and returns the shared outcomes (the 49 per-module status aliases are gone); cross-module field writes became stack interfaces; every module `require`s its direct dependencies; *exhausted* (out of fuel) and *full* (out of room) are separate; `src/core/` plus `src/kernel/` have about 690 words, none over ten lines (`make forth-metrics`), against a baseline of 218 words, 23% over ten lines and 225 globals. Randomized differentials against the previous code show no difference. Follow-ups: choose one of the three recursion patterns |

## Theorem proving and Mathlib

| Milestone | Status and evidence / remaining work |
| --- | --- |
| 1. Development foundation | 1 of 4 done (T1.3). Pinned Gforth 1.0.0 and Lean 4.35.0, CI on two Gforth versions, timeouts, `sorry`-proof Lean checks, documentation link and portability checks. Clean-machine reproduction (T1.1, T1.2) and a portability matrix (T1.4) remain. |
| 2. Terms, names and universes | In progress: stores on the library's `store:` records that now grow on the heap up to a per-context capacity (default 64; universe arguments, parameters and the level context now have no fixed limit, plan 6.2.0 part a; depth limits, part b, done; the owner's [kernel] gate for the large store was approved 2026-11-04 late), handles that detect stale references, symbolic Sorts kept apart from concrete ones, which no checker pass accepts (ADR 0007; the unsafe draft that mixed them was retired), structured names. Human review of the representation and serialization remain. |
| 3. Scope and substitutions | In progress: shift, instantiation and universe substitution passes compared with Lean on finite tables (80, 25 and 48 cases and others). General specification and review remain. |
| 4. Definitional equality | 1 of 3 done (T4.1, rules approved). Conversion compares after beta reduction, answers *rejected* where ADR 0011's approved rules say Lean certainly rejects, and *unknown* elsewhere; unfolding, eta and proof irrelevance are phase 4. |
| 5. Small trusted checker | 1 of 4 done (T5.1, rules and design approved). Expected results: 62 cases (14 must be accepted, 28 rejected, 1 invalid, 11 unknown, 8 unsupported) checked against Lean. The rejection rules in comparison and inference (plan 2.2.1) were **approved by the owner on 2026-11-03** ([kernel] gate). The checked environment v0 (2.2.2) awaits its last review fixes and gate. The declaration check (2.2.3) is implemented and merged (2026-11-03): end to end, it gives Lean's answer on all 62 rows; its independent review and gate are next. Next: Lean's rule for a "for all" whose body is not a type (ADR 0011 amendment), the failure-path suite (2.2.4) and replay (2.2.5). |
| 6. Lean NDJSON importer | In progress: the Forth reader (gate approved 2026-11-03) decodes every record kind of lean4export 3.1.0 and all of Mathlib (below); the importer stage (approved 2026-11-03) stages all of Mathlib and the byte-for-byte re-export is done; the checker is fed `Init` end to end (heap stores; gate approved 2026-11-04 late). Feeding Mathlib, the checksum manifest check by default and other Lean libraries (plan 6.1.6) remain. |
| 7. Lean checker compatibility corpus | In progress: selected differential tables and the first checker's expected-results table; no official corpus run. |
| 8. Lean declaration features | In progress: the checked environment is designed (ADR 0012, per-declaration universe scope); candidate signatures remain unchecked assumptions; non-recursive inductive types and their recursors are checked (plan 5.2.1a, approved 2026-11-04); recursive types are merged but not past their gate (5.2.1b); indexed types, structures, literals and quotients are decoded by the reader but not yet checked (plan 5.2.1b-c, 5.2.2, 5.2.3, phase 5). |
| 9. Full Mathlib | In progress (T9.1, T9.2, T9.4): every declaration of the pinned Mathlib export (729,263) checked on `b74a04d` (2026-11-12) with Lean's verdict on each, all accepted, 3.37 h on 8 workers, 29.4 GB; the checked snapshot saved and reloaded (425 s). T9.2's evidence is met; the review and owner gates for the checker changes it ran on are owed, so it is not marked done. |
| 10. Native proof authoring | In progress (T10.1 in part): theorems and proofs are written as LeanForth words run by Forth's own interpreter ([syntax](../user/LEANFORTH_SYNTAX.md), [ADR 0017](../adr/0017-leanforth-syntax.md) approved; plan 8.1.2 merged 2026-11-03, under the [parser] gate): binder words, `fun`, `forall`, `->`, `$`, `^`, `theorem … := … end`, namespaces, labels and notes; 53 error codes with line and column; 42 `#print` lines from 14 fixtures equal Lean's. The term printer matches Lean's printing on 50 cases. Readable proof outlines now come from the checker's derivation log (`leanforth print`, approved 2026-11-04). Not yet: handing terms to the checker in a separate process, literals, `let`, tactics. |

## Provably correct executable Forth

| Milestone | Status and evidence / remaining work |
| --- | --- |
| 1. Contract and assumptions | In progress: [receipt schema 0.3](../programming/PROGRAM_RECEIPTS.md) (0.2 without the check label, 2026-11-12) keeps CHECK, VERIFY and RUN apart, says whether Lean or LeanForth settled each obligation, lists axioms per theorem and requires runtime, cell, stack-capacity, two's-complement, Lean, reader, generator and floating-point assumptions; 29 tests with 114 mutations; the owner decided the format on 2026-11-12 (the result label removed). |
| 2. Tested Forth example | In progress: six example words with finite tests; all six now have formal contracts (plan 1.5.3, done 2026-11-03): Lean proves each word's reference model and IR meet its contract for every cell width (gcd and factorial through loop invariants) and refutes deliberately wrong models and programs, 27 theorems using at most `propext`, `Classical.choice` and `Quot.sound`. Choosing one word as the acceptance target (P2.3) remains. |
| 3. Formal execution model | 2 of 3 done (P3.1, P3.2): IR 0.1 and its Lean semantics. Remaining: review the model against documented Forth behaviour (P3.3). |
| 4. Model/runtime comparisons | In progress: finite comparisons of the words with Lean models (686 clamp triples, 1,296 memory cases and others); the IR interpreter (`src/program/ir-run.fs`) agrees with the host words and with Lean's evaluation of the model on 5,152 cases (5,092 also run on the host) and 300 random IR programs (2.5.4); testing is not proof. |
| 5. Shared proof kernel | In progress (2026-11-12, plan 5.5.1, works end to end (done check docs/development/done-checks/2026-11-12-program-track.md); owner gates [bypass], [runtime] approved by the owner 2026-11-12; branch not merged): the first program fact checked by LeanForth's checker: Lean's proofs of the clamp contract and its obligations, exported with their 4,277-declaration closure, accepted by `bin/leanforth check`; exports with a changed program IR term, postcondition or proof term rejected. Lean wrote the proofs; LeanForth wrote none. |
| 6. Forth program representation | In progress: the IR is versioned and the reader translates the example words with source locations, refusing anything outside IR 0.1; stack types, host comparison and memory remain. |
| 7. Verification conditions | In progress: Lean references for weakest preconditions and stack depth; generator v0 (`scripts/program_vc.py`, untrusted) turns IR plus a contract into Lean obligations: clamp, checked add, checked abs and in-range discharged by Lean, three wrong contracts refuted, gcd and factorial unsupported until loop invariants (4.4.1). The clamp receipt states LeanForth's verdict on Lean's proofs (`accepted-by-leanforth`, plan 5.5.1). |
| 8. User-facing verifier | Designed (2026-11-13, plan 8.4.1, [design](../design/VERIFY_COMMAND.md)); nothing built. |
| 9. Verified execution/compilation | In progress only for runtime testing; no source-to-runtime correspondence. |
| 10. Larger executable programs | Not started. The track's destination is now most of the Forth-2012 Core word set, in five stages ([owner decision](OWNER_DECISIONS.md#program-track-goal-most-of-forth-2012-core-2026-11-02-night)). |

## Where the two tracks overlap

- **One checker.** Program proofs are checked by the same LeanForth
  checker as theorems: since plan 5.5.1 (2026-11-12, branch `program-551`)
  the clamp proofs Lean wrote are exported with their closure and re-checked
  by `bin/leanforth check`, and the receipt states that verdict; the other
  program proofs are still checked by Lean only.
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
| Expression nodes staged into the compact store | all of Mathlib's 105,894,257; since compact-store step S5 (2026-11-11) the checker reads them in place, copying only `let`, projection and metadata nodes and the nodes above them (2.4% of `Init`'s) | nodes of the pinned export |
| Expression nodes fed into the checker's own stores | `Init`: 6,099,054 nodes of its 59,349 declarations; Mathlib: the first sixth (119,472 declarations) checked, the first third (217,032) staged and fed at fuel 1 on 2026-11-10 (loading only, no check); since step S5 only `let`, projection and metadata nodes and those above them are copied | the checker's stores grow with memory |
| Declarations checked by LeanForth | Mathlib: **729,263 of 729,263 (100%) accepted** on `b74a04d` (2026-11-12, fuel 250,000,000, 8 workers): the same verdict as Lean on every declaration, 1 NOT PROVED (`sorryAx`); 3.37 h, 25.6 CPU hours, 29.4 GB. `Init`: **59,349 of 59,349 (100%) accepted**, exit 0 | constants of the pinned Mathlib export with its dependencies; `Init`'s own count |
| Share of Mathlib the checker accepts | 99.88% (728,360 of 729,263) at fuel 20,000,000; a run at the new default fuel of 100,000,000 that also saves a snapshot is next | all declarations of the pinned export |
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

- **Acceptance-task completion: 0 of 5 T9 tasks done** (3 in progress: T9.1, T9.2, T9.4).
- **Storage:** the compact store (ADR 0016, accepted 2026-11-03) holds all
  of Mathlib in 2.94 GB (4.16 GB peak while loading) in a measurement
  prototype and, since the importer stage was approved, in `src/import/`.
  Since compact-store step S5 (2026-11-11) the checker reads it in place,
  copying only `let`, projection and metadata nodes and those above them
  (Mathlib's first sixth loads in 52 s and 1.06 GB, against 124 s and
  3.37 GB copied); step S5B (merged) removed the remaining copy, and the
  workers of `--jobs N` now share one input (SH).
- **Checked: all of Mathlib, every verdict Lean's** (`b74a04d`, 2026-11-12,
  fuel 250,000,000, `--memory-per-check 8192`, 8 workers, `gforth-fast`,
  shared in-place input): 729,263 of 729,263 accepted, exit 0, 1 NOT PROVED
  (`sorryAx`, as in Lean). 12,134 s (3.37 h), 92,220 CPU seconds (25.6 h),
  29.4 GB peak, 27.1 billion fuel steps (the largest single need about 230M,
  agent R5). Snapshot `mathlib-b74a04d.lfsnap` (2.2 GB, sha256 `31864083…`)
  saved; the export checked against it: 425 s (316 s of it reading the
  export), 9.5 GB. The first full run (`a43539e`, fuel 20,000,000, 4 workers:
  728,360 accepted, 28 exhausted, 875 unknown, 5.74 h) is superseded.
- **Declarations checked: 729,263 of 729,263 (729,263 accepted)** in the full export
  of Mathlib `v4.35.0` (commit `56a0058`) with its dependencies, sha256
  `18448e5d…59c6` ([measurements](../development/measurements/mathlib-2026-11-02/README.md)):
  184,355 definitions, 517,916 theorems, 2,913 opaque declarations, 4
  axioms, 4 quotient declarations, 7,046 inductive types, 9,863
  constructors and 7,162 recursors; 105.9 million expression nodes; up to 30
  universe arguments; expression depth up to 1,221.
- No local reference-checker baseline exists (nanoda stopped at the 16 GB
  memory limit set to protect the machine).

## Parallel checking groundwork

**Status (2026-11-11 evening): `check --jobs N` merged (agent S7, `41a3157`)
and the workers now share one copy of the input (agent SH, `0627845`); default
1 worker, the owner chooses the default; gates owed [kernel][runtime].** All of
`Init` at 1 to 12 workers gives output identical to one worker (59,349
accepted; SH: 0 differences). Check wall time of `Init` was 1,136 s on 1
worker, 536 s on 2, 183 s on 8 (6.2 times; machine shared with other runs).
With the shared input Mathlib's first sixth on 8 workers peaks at 4.7 GB (7.7
GB with a copy per worker); all of Mathlib on 8 workers is predicted at about
13 GB and 3.1 h on a quiet machine, 12 workers no faster. The full Mathlib run
above used 4 workers and 20 GB.

- **Written and tested in the library** ([ADR 0009](../adr/0009-reentrant-state-and-parallel-checking.md),
  accepted): per-task contexts (`src/lib/context.fs`) that modules declare
  their state into, with owners — a context belongs to one job until it is
  waited for; a worker pool (`src/lib/task.fs`) on Gforth 1.0's threads,
  Gforth 0.7.3's cooperative tasker or a serial path, with stack-overflow
  detection, compared with serial runs for 1, 2 and all workers.
- **Measured** (Gforth 1.0, Ryzen 5 7600X, 12 threads, WSL2): 12 workers
  ran 12 test jobs 5.7–6.3 times faster than one task (2 workers
  1.9–2.0×, 6 workers 4.4–5.0×); over 39,984 jobs the process stayed at
  about 9.5 MB. These are test jobs, not checker workloads.
- **Written and tested in the checker on synthetic trials** (ADR 0009 step 3, 2026-11-02): all 24 core and
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
- **Since S7 and SH:** the scheduler runs a whole file's declarations as jobs
  and the input is shared read-only (plan task 7.2.1, [kernel] review
  owed). Not done: the scheduler's per-term "seen" stamp array (about 0.42 GB
  for Mathlib) is to be indexed per record. Roadmap C1 and C2 are in progress,
  C3 and C4 partly.

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

**Since 2026-11-11 GitHub CI is off** at the owner's request (its runs
failed for billing, before any test ran). Before every push its two jobs run
locally under `ulimit -u 500`: `make check` with pinned Gforth 1.0.0 and Lean
4.35.0 (Lean cache on for merges; `LEAN_CACHE=0` once a day: exit 0 in 170 s
on 2026-11-11) and `make test` with Gforth 0.7.3 (exit 0 in 125 s). Pinned
Lean's outputs are replayed from the Lean cache (`scripts/lean-cache.py`,
keyed by the SHA-256 of every input) instead of rerun.

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

State on main at `0627845` (2026-11-11 evening): `bin/leanforth check` on all of Lean's
`Init` and on all of Mathlib (729,263 declarations of the pinned export), the cases of `tests/core/check-block-cases` and
`check-declaration-cases`, and the merged review reports.

**Status words.** *Coded and used*: `leanforth check` runs it by default.
*Coded, not used*: code and tests exist, `check` does not run it.
*Merged, gate owed*: used by `check`, but its human-review gate has not been
passed. *Planned*: not coded. No outside Lean expert has audited the checker yet
(plan 9.2.1).

- **Mathlib: all checked once, 99.88% accepted.** On `a43539e` (fuel
  20,000,000, 4 workers) 728,360 of 729,263 declarations were accepted, 0
  rejected, 28 exhausted and 875 *unknown* because they depend on those 28, 1
  NOT PROVED (`sorryAx`); 5.74 h wall, 21.4 CPU hours, 20 GB. At fuel
  100,000,000 (now the default) 23 of the 28 roots are accepted and 5 are not;
  a full run at the new default, saving a snapshot, has not been made yet.
  An exhausted or unknown result is a resource refusal, not a wrong verdict.
  Open: a snapshot slot's fuel can differ from a fresh check's (review rvSN4
  B1; PF task 6), so exhausted results are never taken from a snapshot.
- **`Init`: all accepted.** All 59,349 declarations at the default fuel, exit
  0 (`af93afb`: 1,162 s, 1.15 GB peak; read in place since step S5: same
  verdicts and fuel, 530 MB peak). Lean's official export checker takes
  50.7 s and 572 MB for the same file: LeanForth is about 23 times slower on
  one thread.
- **Coded and used, approved by the owner on 2026-11-11** ([round](OWNER_DECISIONS.md#approval-round-of-2026-11-11)):
  `let` (4.2.3), number and string literals (5.2.3), projections, structure
  eta and the comparison's projection steps (5.2.2), indexed families and
  K-like recursors, quotients (5.2.4), axioms with allowlist v1 and opaque
  declarations (5.3.1-5.3.2, 4.2.6), the full lazy strategy, eta, proof
  irrelevance (4.2.2b-d, 4.2.4, 4.2.5), nested inductive types (5.2.5b),
  unsafe and partial declarations skipped as Lean's export checker skips them
  (5.2.7), the result caches (4.2.7; off under a derivation log),
  compact-store steps S0-S4 and S6, and the importer's index numbering and
  `--any-lean-version` ([import][format]). Earlier parts approved one by
  one: rejection rules, environment, declaration check, free variables, the
  first data types, recursive types and mutual blocks, the derivation log,
  the checker on the large store without a depth limit.
- **Coded and used, gate owed** (reviews done, owner's approval not yet asked):
  compact-store step S5 and S5B (the checker reads the input in place, no
  copy); `check --jobs N` (S7, default 1 worker) with the **shared input**
  (SH: workers use one copy of the input, for every export, by default;
  Mathlib on 8 workers about 13 GB predicted); the diagnostic-81 routes (IO);
  snapshots (SN2-SN5: `--save-snapshot`, `--snapshot`, layered snapshots for
  dependent exports, `--snapshot-stale-ok`, golden verdict guard; report
  0.3, verdict version 3); `--progress` and streamed verdicts (PRG);
  `gforth-fast` as the default engine, `--checked` opt-in (ENG); PF batch 1
  (default fuel 100,000,000, fix C1; ADR 0014 Amendment 6).
- **Coded, not used by `leanforth check`**: the program track's IR, generator and receipts (they run through
  tests and Python scripts; there is no `leanforth program` command, plan 3.4.1, 8.4.1; the clamp proofs' export
  itself is checked by `leanforth check`, plan 5.5.1); the record and replay
  reader (`check --record`, `replay`: 32 declarations, no inductive types,
  `let`, literals, projections or metadata; its old limits are 64 names, 64
  levels and 64 term nodes); the test-only probe-mode inference
  (`lf-mixed-infer` probes, signature probe and audit,
  `mixed-definition-probe.fs`, `lf-mixed-convert`) and the old
  `import/load.fs` batch staging, both candidates for retirement (plan task
  5.2.8; diagnostics 33 and 64 appear only in the probes). The derivation log
  and `print` run only when asked, with caches off.
- **Still unsupported or unknown in `check`** (each *unsupported*, *unknown*
  or *full*, exit 2 or 3, never accepted): a block with both safe and unsafe
  members (5.2.7 part b); metadata `mdata` in a term (diagnostic 43, plan
  4.1.3; none in Mathlib's first sixth); iota on a major premise that is not
  a constructor application, in the routes not yet ported (diagnostic 81,
  follow-up of 5.2.1b/5.2.2), so a correct proof can still end *unknown*; a
  recursor or quotient constant no slot holds (diagnostic 77, 5.2.4); a file
  that uses an undeclared constant is invalid as a whole (5.2.6); numbers of
  2^32 and more in names, projections and counts are *full* (5.2.6); fuel can
  run out on a very large declaration (diagnostic 1; raise `--fuel`), though
  none did in `Init` or Mathlib's first sixth at the default; where Lean's
  verdict depends on how its levels share memory (rule K6, BEYOND_LEAN BL-3)
  LeanForth answers *unknown*.
- **Capacities** (each *full*; plan 6.2.2, 6.2.4, 6.5.7): a check's scratch
  above the input grows with memory up to about 2^31 terms, levels and
  constant references each (fixed at 1,048,576, 65,536 and 262,144 before
  step S5); 65,536 tokens per line, JSON nesting 64, a line of 64 MiB; the
  log and printer tables.
- **Resource refusals are not verdicts** (owner, BL-9): running out of fuel
  (*exhausted*) or memory (*full*) says nothing about whether a declaration
  is right.
- **Speed.** Work is linear in a term's depth since step S6 (the 10,000-deep
  test: about 13 minutes before steps S0-S6, 162 s before S6, about 6 s now). One thread: `Init` takes about 23
  times as long as Lean's official export checker. Parallel checking (S7, shared input) is
  merged; profiling the hot words (plan 6.5.8) waits for the owner's go.
- **Axiom policy** (allowlist v1, approved 2026-11-11): an axiom outside
  `propext`, `Classical.choice` and `Quot.sound` or with an altered statement
  gets Lean's verdict, labelled NOT PROVED, exit status 0 as Lean's
  (`--strict-axioms`: 6); the full axiom list of a theorem as `#print axioms`
  is planned (5.3.2, 5.3.3).
- Not yet reported per check: large proofs have no splitting guidance (6.5.3);
  the worker count is not a setting (6.5.4); Lean's own test suites and other
  Lean libraries are not yet run (6.4.2, 6.1.6).
- The program track's proofs are about the IR's Lean semantics, written
  and checked by Lean (the clamp's also re-checked by LeanForth, plan
  5.5.1); that Gforth runs the words as the IR says, and that the reader
  translates faithfully, are tested, not proved. IR 0.2 (redefinition,
  output words) is implemented and its [parser] implementation gate is
  approved; no receipt can describe an IR 0.2 program until receipt schema 0.4.
- Only Lean 4.35.0 exports in format 3.1.0 are read by default (other versions
  only with `--any-lean-version`); a file cut off cleanly between two lines
  is detected by the manifest unless `--no-manifest`; only Linux/WSL with
  Gforth 1.0.0 and 0.7.3 is tested.

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
design. The checker on the large store [kernel] was approved the same
evening, once universe lists (plan 6.2.0 part a) and depth (part b) had no
fixed limit. `Init` end to end: 184 data types and 1,014
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

## Update, 2026-11-04 late (commit `bba87db`)

Since `6266f70`: the owner approved the checker on the large store with no
depth limit (plan 6.2.0 parts a and b), the IR 0.2 implementation, and the
data-type condition as met; and chose that NOT PROVED exits 0 like Lean
(`--strict-axioms` gives 6) and that the default engine is the checking one
(`--fast` quicker). Merged and waiting for their gates: recursive data
types (5.2.1b, two wrong acceptances found by review are being fixed) and
the first half of unfolding (4.2.2b-c, gate review running). Merged without
a gate: `leanforth check` and `leanforth print` on whole libraries, the
statement in three forms (8.6.1, 8.6.2 done), escaped names, and the first
four proved SHA-2 words. ADR 0017 Amendment 1 (native and inline LeanForth,
library vocabularies, case rules) was accepted; plan 8.2.1a, c, d later
worked end to end (see the top of this file); 8.2.1b, e, f and g have not started. Every gap from Lean named here is temporary with a closing task.
Run for this documentation change: `make test` only, not `make check`; the
figures come from the cited documents and commit messages, the `Init`
command-line figures are those of `9df4fa3` (before recursive types), and
the CI status of `bba87db` was not looked up. Next on the critical path:
clear the 5.2.1b findings and the two gates, then 4.2.2d-e, structures
(5.2.2) and literals (5.2.3) on the way to `n + 0 = n`.

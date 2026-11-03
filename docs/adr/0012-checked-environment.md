# ADR 0012: the checked environment — implementation design

Status: **design accepted** by the owner on 2026-11-02 (G8–G11; [gate](../reviews/FIRST_CHECKER_GATE.md#owners-answer-second-set)); the implementation still needs its own gate approval. Previously: proposed, 2026-11-02 (plan task 2.1.3). A checker design: it
passes the [kernel] and [import] gates in `AGENTS.md` only with the owner's
approval of the plain-language summary in
[the gate document](../reviews/FIRST_CHECKER_GATE.md#second-set-of-questions)
(questions G8–G11). Nothing here is implemented. It implements the contract
of [ADR 0006](0006-constant-environments.md) for the first checker
([ADR 0011](0011-definite-rejection.md), rules approved) on the re-entrant
structure of [ADR 0009](0009-reentrant-state-and-parallel-checking.md)
(accepted), and answers questions 2, 5 and 6 of
[the checked-environment review packet](../reviews/CHECKED_ENVIRONMENT_REVIEW.md).

Amended 2026-11-02 ([Amendment 1](#amendment-1-2026-11-02-after-the-independent-review-of-v0)):
stricter or clarifying changes after the independent review of the
implementation; the status above is unchanged.

## Summary in plain words

The checked environment is LeanForth's library of accepted declarations.
Each declaration of the input gets one numbered entry, in input order. An
entry is written exactly once, by one part of the program (the
*publisher*), after the declaration's check has ended, and never changes
afterwards. Only an *accepted* entry can be used by later declarations, and
only by declarations that come later in the input. A check works in its own
scratch space; whatever happens to it — rejected, unknown, out of memory, a
crash — that space is thrown away and the library is unchanged. The proof
that was checked is the proof that is stored: the publisher does not copy
or translate it. Each accepted entry lists the statements assumed without
proof (axioms) it depends on, directly or indirectly; in the first checker
that list is always empty, and is computed rather than assumed. When checks
run in parallel, each still sees only finished earlier entries, so the
verdicts and the library are exactly those of a one-at-a-time run.

## What is already decided

- **ADR 0006** (contract): one immutable snapshot per check; exact universe
  arity; simultaneous substitution in the callee's scope; transactional
  registration that publishes nothing on failure; handles and caches bound
  to snapshot identity; an empty axiom allowlist with transitive reporting.
- **ADR 0009** (accepted): all per-check state in records; one context per
  worker, reached through the `USER` pointer `lf-context`
  (`src/lib/context.fs`); the environment append-only, then read-only and
  shared without locks; one scheduler publishing in dependency order;
  Forth tasks (`src/lib/task.fs`); parallel verdicts equal to serial ones.
- **ADR 0011** (rules approved): unknown, forward and self references are
  rejected (N1); a second declaration with an accepted declaration's name is
  rejected (N2); a constant naming an undecided earlier declaration makes
  its user *unknown*, or *unsupported* if that one was (K5); axioms are
  *unsupported* (U1); acceptance (A1) publishes, nothing else does.
- **Owner decisions of 2026-11-02**
  ([evening record](../project/OWNER_DECISIONS.md#legacy-retirement-and-the-first-checkers-rules-2026-11-02-evening)):
  theorem mode (a theorem's statement must be a proposition) is rebuilt in
  phase 2; the environment needs a *per-declaration universe scope*; checking
  open terms under a supplied context waits for a Lean-style local context;
  axioms are *unsupported* in the first checker (gate answer G3). And
  ([planning answers](../project/OWNER_DECISIONS.md#planning-answers-2026-11-02-later-the-same-day)):
  saved results may be reused only in development and research runs,
  labelled, and a final run re-checks everything (OQ-3); the checker runs as
  its own program (OQ-1).

## Facts from Lean 4.35.0

Read from tag `v4.35.0` (commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`)
at `raw.githubusercontent.com/leanprover/lean4/v4.35.0/` on 2026-11-02.
`type_checker.cpp`, `environment.cpp`, `declaration.h`, `declaration.cpp`,
`level.cpp` and `Lean/Environment.lean` have the SHA-256 hashes ADR 0011
records; the others are under *Reproduction*.

1. **Lean's kernel environment is a value that is never changed.**
   "Environments are never destructively updated" (`src/Lean/Environment.lean`
   194–207); its constructor is private "to protect against modification
   that bypasses the kernel" (208–213). `addDeclCore` returns either a new
   environment or a kernel exception (295–298); `environment::add` builds
   the new value only after every check of the declaration has passed
   (`src/kernel/environment.cpp` 192–209 for theorems, 160–190 for
   definitions, 271–282), and the private `add` inserts one constant
   (`Environment.lean` 310–312). A failed check therefore leaves the caller's
   environment exactly as it was.
2. **Additions are linear.** "The kernel environment type
   `Lean.Kernel.Environment` enforces a linear order on the addition of
   declarations" (`Environment.lean` 32–73). Lean's elaborator works on
   branches in parallel, but the kernel environment has one history.
3. **Names are unique** (`check_name`, `environment.cpp` 102–105), and a
   declaration's universe parameters are distinct (111–121).
4. **Universe parameters belong to one declaration.** The checker is given
   the declaration's own parameter list (`type_checker::check`,
   `type_checker.cpp` 364–367), and every level must use only those
   (`check_level` 85–91). A reference supplies exactly as many levels as its
   target has parameters (`infer_constant` 103–108); the levels are checked in
   the caller's scope (118–120); the target's stored type is then
   instantiated by replacing each of the target's own parameters by the
   level in the same position (`instantiate_type_lparams`,
   `src/kernel/instantiate.cpp` 232–254). The replacement is simultaneous: a
   substituted level is not searched again (`instantiate`, `level.cpp`
   317–339).
5. **Axioms are collected transitively** over the constants named in a
   declaration's type and value: an axiom contributes itself and its type's
   axioms; a definition, theorem or opaque declaration its type's and its
   value's (`collect`, `src/Lean/Util/CollectAxioms.lean` 37–74; this is
   `#print axioms`).
6. **Lean's kernel unfolds theorems, last** (agent I's finding, recorded in
   ADR 0011 fact 2 and gate question G5). `is_delta` accepts any constant
   whose `has_value` holds (`type_checker.cpp` 555–563), which includes
   theorems (`declaration.h` 466–468); a theorem's reducibility hint is
   `opaque` (`constant_info::get_hints`, `declaration.cpp` 294–299), and when
   two different hints meet, the non-opaque side is unfolded first
   (`compare`, `declaration.cpp` 24–49). ADR 0006's "theorems ... must not
   be unfolded" therefore differs from Lean; the owner decides in phase 4
   (G5). This design keeps every theorem's value and hint, so either answer
   remains possible.

## Decision (proposed)

### E1 Three kinds of storage

| Storage | Holds | Written by | Read by |
| --- | --- | --- | --- |
| **Input** | the names, levels and terms decoded from the input (export records), unchecked | the importer, before checking starts; then never | every check |
| **Environment** | one slot per input declaration: its verdict and, if accepted, its record (E2) | the publisher only, once per slot | every check, within its snapshot (E3) |
| **Context** | everything one check builds: scratch terms, walk records, fuel, the candidate record, the derivation log, diagnostics | its own task | its own task; the publisher reads the candidate after the check ends |

- Environment records point only into the input (their type and value roots
  and names) and at earlier slots; never into a context. A context may hold
  input indices and slot numbers, never addresses of shared records
  (addresses can change when storage grows).
- **The checked claim is the stored claim.** An accepted record points at
  the very input terms that were checked; nothing is copied or translated
  at publication, so no copying mistake can make the library hold a
  statement other than the one checked. This requires the input to stay
  unchanged once loading ends (gate question G10, [import]).
- **Phase 2.** The input is today's term, level and name stores, filled by
  the test-only transport before checking starts. Loading ends with a store
  mark (plan task 1.1.3); each check allocates above the mark and is rolled
  back to it afterwards, whatever its outcome. No word writes a record below
  the mark after loading; the failure-path suite checks this with a digest
  of the input region before and after every check. Phase 7 moves scratch
  into per-context stores (`context-store:`), which needs a tier mark on
  child references; that is a no-behaviour-change [kernel] review (plan
  task 7.2.1).

### E2 The record of an accepted declaration

| Field | Contents |
| --- | --- |
| `slot-state` | empty, or final (set last, E4) |
| `slot-outcome` | the check's outcome (ADR 0008): ok for accepted, else rejected, unknown, unsupported, invalid, exhausted or full |
| `decl-name` | the input name |
| `decl-kind` | definition or theorem (later: inductive types and their parts, the allowlisted axioms) |
| `decl-params` | its universe parameter names, in order, distinct (L3) |
| `decl-type`, `decl-value` | the input term roots that were checked |
| `decl-hint` | a definition's reducibility hint from the export; `opaque` for a theorem, as Lean's `get_hints` gives (fact 6) |
| `decl-deps` | the slot numbers of the declarations named in its type and value, sorted and distinct |
| `decl-axioms` | its transitive axiom set (E6) |
| `decl-provenance` | checked in this run, or loaded from saved results and not re-checked (E8) |

Only `slot-state` and `slot-outcome` are meaningful for a declaration that
was not accepted. A record is complete before its slot is final and is never
changed afterwards.

**Per-declaration universe scope** (owner decision; review question 2).
A record's own parameter list is the only universe scope of its type and
value (fact 4). A reference `c.{l₁,…,lₙ}` inside another declaration is
checked in three steps, as Lean does: exactly as many levels as `c` has
parameters (L1), each level within the *caller's* parameters (L2), then
`c`'s stored type with each of `c`'s parameters replaced by the level in the
same position, all at once. The names of `c`'s parameters are matched only
inside `c`'s stored type, and the caller's levels are substituted as values
and never searched again, so a caller parameter that happens to share a
name with one of `c`'s cannot be confused with it. The existing
`tests/reference/constant-environment-oracle.lean` cases (swapped
two-parameter substitution, nested `max`/`imax` arguments, unbound
parameters) become LeanForth differential rows in task 2.2.2. Level
equality stays as ADR 0011 approved it: identical, or both concrete with
the same value, is equal; a witness assignment shows apart (D1); anything
else is *unknown* (K4) until Lean's level normalisation (plan task 4.1.2).

### E3 Snapshots and handles

- **Slot numbers follow the input.** Declaration `i` (counting from 0 in
  input order) owns slot `i`. Numbers therefore never depend on timing.
- **Environment identity.** Each environment gets a number from a counter
  that only grows and never repeats; when it runs out, no further
  environment can be made (like the store serial in `src/lib/store.fs`).
  There is no reset and no rollback: starting over means a new environment
  with a new identity, so no generation numbers are needed.
- **A check's snapshot** is (environment identity, `i`): the check of
  declaration `i` may read slot `d` only if `d < i` and slot `d` is final.
  In a serial run every slot below `i` is final when the check starts, so
  the snapshot is exactly "the verdicts of the first `i` declarations",
  ADR 0006's prefix snapshot. In a parallel run only the slots the check
  needs are guaranteed final (G-P5 below), and it reads no others. Every
  snapshot stays valid for the life of its environment, because slots are
  written once and never removed.
- **A handle** to an accepted declaration is (environment identity, `d`). In
  a check with snapshot (identity′, `i`) it is valid only if the identities
  are equal, `d < i`, slot `d` is one the check may read (in a serial run
  any slot below `i`; in a parallel run those its readiness made final,
  G-P5), and its outcome is ok. Every other handle — from another or a
  freed environment, from the future (`d ≥ i`), to a declaration that was
  not accepted, or a forged number — gives *invalid*
  ([expected-results table](../reviews/FIRST_CHECKER_EXPECTED.md), "Cases
  with no Lean counterpart"). Checking a handle reads only the handle, the
  check's context and slots it may read, never freed memory or a slot still
  being written.
- **Caches** (none in phase 2; plan task 4.2.7) are keyed by environment
  identity and snapshot as well as by context, universe substitution and
  policy (ADR 0006). Because slots never change, a *success* found under one
  snapshot stays true in every later one; *unknown*, *invalid*, *exhausted*
  and *full* are never cached as success.

### E4 Staging, then publishing only after full success

A check of declaration `i` runs entirely in its context:

1. It records its snapshot (identity, `i`) in the context.
2. It audits and checks in ADR 0011's order. Everything it builds — scratch
   terms, the dependency list, the axiom set, the derivation log — is in the
   context.
3. It ends with one outcome and, if the outcome is ok, a complete
   *candidate record* in the context.
4. It hands the outcome and candidate over to the publisher (in a serial
   run, the same task). Once the publisher has taken them, the context is
   rolled back to its mark, whatever the outcome.

The publisher then fills slot `i`:

1. For ok, it re-checks the candidate's cheap invariants against the
   environment: every slot below `i` with the same name is final and
   *rejected* (N2 with K5: an accepted, undecided or unsupported one, or
   one not yet final, fails the re-check; amended 2026-11-02, see
   [Amendment 1](#amendment-1-2026-11-02-after-the-independent-review-of-v0));
   every dependency is below `i`, final and accepted; the axiom set is the
   union of the dependencies' sets; kind and safety are in scope. A failure
   means a fault in LeanForth, and the outcome becomes *invalid*.
2. It writes the record fields (ok) or only the outcome (anything else).
3. Last, under the publisher's lock, it marks the slot final. This is the
   single point at which a result becomes visible.

A `THROW` in the publisher before step 3 leaves the slot not final, so no
check reads it; the run then stops with an internal fault, and the
declaration is reported *invalid*. (A `THROW` inside a check is handled at
the job boundary instead, G-P6.)
Running out of room for the dependency list or records gives *full*, with
nothing made final as accepted. No path other than an ok check followed by
steps 1–3 can make a slot final with outcome ok, and no path changes a
final slot.

### E5 Finding a constant

To resolve a constant named `X` in declaration `i`, the checker itself (not
the scheduler) looks at the earlier declarations whose input name is `X`:

- one of them is final and accepted: use it (by N2 there is at most one);
- otherwise, if one is final with *unknown*, *exhausted*, *full* or
  *invalid*: the user ends *unknown*; with *unsupported*: *unsupported*
  (K5). When there are both an undecided and an unsupported one, the user
  is *unknown*, whatever their order: unknown first, the cautious answer
  (amended 2026-11-02, see
  [Amendment 1](#amendment-1-2026-11-02-after-the-independent-review-of-v0);
  the owner is asked to confirm);
- otherwise (none, or all *rejected*): `X` is unknown to Lean too, and the
  user is *rejected* (N1).

Phase 2 finds these by scanning the input names below `i` (names are in the
input, which never changes). Comparing names is structural (ADR 0005);
sharing of equal names is an optimisation that correctness never assumes.
A later name index (plan task 6.2.1) is checked against the scan in tests.
If a needed slot is not final when the checker looks, the scheduler started
the check too early: the check ends *invalid*, never accepted. The same
lookup on the declaration's own name decides N2: an accepted earlier
declaration of that name makes it *rejected*, an undecided one *unknown*
and an unsupported one *unsupported* (K5, unknown first), and a rejected
one is no conflict.

### E6 The transitive axiom set

- A record's axiom set is the union of the sets of the declarations named in
  its type and value, plus the record itself if it is an allowlisted axiom
  — Lean's own rule (fact 5). Dependencies are final before their users, so
  each set is computed once, from direct dependencies only.
- The set is a bit set over the owner-approved, versioned allowlist (at
  most `propext`, `Classical.choice` and `Quot.sound`, owner decision 4).
  The allowlist and its version are fixed when the environment is made; an
  environment never mixes versions. Nothing outside the allowlist can be
  accepted, so nothing else can appear.
- **Phase 2:** the allowlist is empty (version 0); axioms are *unsupported*
  (U1) and so is everything that uses one (K5). Every set is therefore
  empty, and every accepted result prints *axioms: none* — computed from
  the records, not assumed (ADR 0011, *Accepted results*). Checking the
  union itself needs a test-only allowlist bit on synthetic records, never an
  accepted axiom.

### E7 Per-task contexts and the single publisher

How ADR 0009's contexts fit, phase 7 in view (phase 2 has one task):

| State | Kind | Written by | Read by |
| --- | --- | --- | --- |
| scratch stores, walk records, fuel | context members (`context-store:`, `context-walk:`) | its task | its task |
| snapshot, current declaration's universe parameters, candidate record, dependency list, axiom set being built, derivation log, diagnostics | one context record (`context-record:`) | its task | its task; the publisher after the check |
| input | shared | the importer, before tasks start | all |
| environment header, slots, records, dependency lists | shared, reached through one pointer set before tasks start | the publisher | all, within their snapshots |
| allowlist and version, run mode, capacities | shared | set before tasks start | all |
| job queue, readiness counts | shared | the scheduler, under its lock | the scheduler |

- A bound variable's type is part of a walk (de Bruijn context inside the
  check), not of the environment. A Lean-style local context for checking
  *open* terms supplied by a caller is not in phase 2 (owner decision); when
  it comes it is a context member, never shared.
- `src/lib/context.fs` seals the context layout at the first `context-new`
  and forbids `ALLOT` and compiling after tasks start, so the environment's
  storage exists before tasks start: in phase 2 fixed-capacity stores made
  at load time; later heap storage that never moves a slot already written
  (for example a directory of fixed chunks), because checks read slots
  without a lock and `RESIZE` could move memory under them.
- The environment is owned by the task that made it and freed only after
  every task using it has been waited for (`task-wait`).

**What the single publisher must guarantee** (review question 5):

- **G-P1 One writer.** Only the publisher writes slots, records,
  dependency lists and the environment header; only the scheduler writes
  the queue. Checks write only their own context and job record.
- **G-P2 Complete before visible.** A slot's fields are written before it
  is marked final; marking final happens under the lock, and a check is
  handed out under the same lock after the slots it needs are final. On
  Gforth 1.0's threads the lock gives the required memory ordering; on the
  cooperative tasker (Gforth 0.7.3) and the serial host no task switch can
  happen inside these words, provided they neither pause nor print (the
  tasker switches tasks in `PAUSE`, `TYPE`, `EMIT` and `KEY`,
  `src/lib/task.fs`).
- **G-P3 Only full successes.** A slot becomes final with outcome ok only
  for an ok outcome of a complete check of exactly that declaration against
  its snapshot, after E4's re-check. Every other outcome is recorded as
  that outcome and publishes nothing usable.
- **G-P4 Same result as one at a time.** A check reads only slots below its
  own number that are final (E3, E5); slot numbers follow the input. So the
  verdicts and the environment do not depend on how many tasks run or in
  which order they finish (ADR 0009 decision 5).
- **G-P5 Readiness.** A check is started only when every earlier
  declaration whose name it uses — and every earlier one with its own name —
  is final. The scheduler may only delay a check; it never decides what a
  lookup finds, and starting a check too early ends it *invalid* (E5).
- **G-P6 Failures stay inside the job.** A `THROW` in a check is caught at
  the job boundary (`job-run` in `src/lib/task.fs`); the declaration ends
  *invalid* (internal fault), the worker's context is freed and replaced
  rather than reused, and no slot is affected. The same holds for the
  serial driver of phase 2, which catches the `THROW` itself (amended
  2026-11-02, see
  [Amendment 1](#amendment-1-2026-11-02-after-the-independent-review-of-v0)).
- **G-P7 No speculation.** No check uses a declaration that is not final
  and accepted (question G9).

### E8 Saved results and the two run modes

The owner's answer to OQ-3: development and research runs may reuse saved
results; a final run re-checks everything and reads no saved results.

- The run mode is fixed when the environment is made: *final* or
  *development*.
- A final run's environment holds only declarations checked in that run;
  any attempt to load saved results into it fails closed.
- In a development run, a record loaded from saved results has provenance
  *not re-checked in this run*, and so does every record that depends on
  one, directly or not (propagated like the axiom set). Output prints the
  label; only a final run's results support a claim.
- The format of saved results is a [format] decision for later (plan tasks
  2.2.5 and 3.4.3). Phase 2 implements the final mode only.

### E9 Outcomes

ADR 0008's vocabulary, with ADR 0011's meanings. Specific to the
environment: an invalid, stale, cross-environment or future handle gives
*invalid*; no room for a record or dependency list gives *full*; a failed
re-check by the publisher or a `THROW` in a check gives *invalid* (internal
fault). None of them is ever accepted, stored as accepted or cached as
success.

## Answers to the review packet's questions 2, 5 and 6

- **Question 2** (universe arity, scope, simultaneous substitution,
  caller and callee names; which symbolic rules to trust first): E2,
  *Per-declaration universe scope*, following Lean's `check_level`,
  `infer_constant` and `instantiate_lparams` (fact 4); the trusted level
  rules are ADR 0011's (identical or equal concrete values; witnesses for
  apart; otherwise *unknown*), and theorem mode uses ADR 0011's exact
  proposition test (S3).
- **Question 5** (identity, ownership, lifetime, invalidation, overflow,
  concurrency, recovery): identity and lifetime E3; no invalidation is
  needed because nothing is ever removed or changed; overflow only of the
  identity counter, which stops instead of wrapping; ownership and
  concurrency E7 (G-P1–G-P7); atomic publication and recovery E4 (a
  failure before the final mark leaves nothing visible; nothing is kept on
  disk, so a crashed run is simply rerun).
- **Question 6** (evidence and review before use or merge): the test matrix
  below, the [kernel] gate's four parts (Lean's behaviour, agreeing pinned-Lean
  differential tests reaching every outcome, an independent AI review of the
  exact change with no unresolved findings, owner approval of a plain
  summary), and the [import] gate for the input (E1).

## Test matrix (plan tasks 2.2.2–2.2.5)

1. **Every row of the first checker's table** (60 Lean kernel cases: 14
   accepted, 28 rejected, 1 invalid, 9 unknown, 8 unsupported) run through
   the environment, plus the binder-domain table (ADR 0003, Amendment 1):
   accepted rows are published and get valid handles; no other row makes a
   slot final with outcome ok.
2. **Nothing changes on failure.** After every outcome other than accepted,
   the digests of all final slots, the dependency lists and the input region
   are unchanged; after acceptance exactly one slot changed.
3. **Names:** unknown, forward, self and duplicate references (N1, N2);
   reusing a rejected name (no conflict); using an undecided one (K5).
4. **Universe scope:** zero, exact, too few and too many levels; undeclared
   and repeated parameters; same-named caller and callee parameters in
   swapped order; nested `max`/`imax` arguments.
5. **Handles:** from another environment, from a freed one, from the future,
   to a rejected or undecided declaration, forged — all *invalid*; an old
   handle stays valid in later snapshots.
6. **Atomicity:** allocation failure injected at every allocation during the
   check and during publication (plan task 1.4.6), fuel exhaustion at every
   step, no room at publication, a `THROW` inside the publisher before the
   final mark: nothing published, digests unchanged.
7. **Axiom sets:** *none* computed for every accepted row; the union and the
   provenance label checked on synthetic records with a test-only allowlist
   bit.
8. **Determinism and replay:** the same input twice gives byte-identical
   verdicts and environment digests (plan task 2.2.5).
9. **Interleaving:** two contexts checking interleaved — cooperatively on
   Gforth 0.7.3, as threads on 1.0 — give the serial verdicts and
   environment (ADR 0009 step 3); a check started before a slot it needs is
   final ends *invalid*.
10. **Planted faults** (plan task 1.4.2), each of which must be caught:
    publishing an *unknown* outcome; marking final before writing the
    record; skipping the N2 re-check; accepting a handle with `d ≥ i`;
    dropping a dependency's axiom bit; reading a slot that is not final.

## Consequences

- The first checker needs: store marks (task 1.1.3), the slot table and
  dependency lists, the scan of E5, a digest helper for tests, and the
  publisher's re-check. In phase 2 the scheduler is a loop over the input.
- ADR 0006 stays the contract. Its sentence that theorems are never
  unfolded is not relied on here (fact 6); phase 4 settles it (G5).
- The untrusted experiments that hold *unchecked* candidate signatures
  (`src/kernel/mixed-signature-probe.fs` and its index token,
  `src/core/generation-handles.fs`) are not the environment. Once the
  environment exists, acceptance never consults them; task 2.2.2 retires or
  repurposes them.
- Plan section 6.11's "a job records the published count when it starts"
  becomes "a job is bound to its own slot number and reads only final
  slots below it": the same guarantee without making every job wait for all
  earlier declarations.

## Rejected alternatives

- **Copy accepted terms into a separate environment store.** Two copies of
  every term, and a copying mistake could store a different claim from the
  one checked; a re-comparison would then be needed. Keeping the input
  unchanged is simpler (E1).
- **Lean's persistent maps for snapshots.** They allow branching
  environments, which Lean's elaborator needs (fact 2); the checker needs
  one history, and write-once numbered slots give every snapshot for free.
- **A published count: publish strictly in input order and let each job
  read below the count at its start.** Also deterministic, but one slow
  declaration would hold back every later check that needs anything after
  it.
- **Publish in the order checks finish, numbering by completion.** Fast, but
  numbers, handles and receipts would depend on timing.
- **Speculative checking** against declarations not yet accepted, accepting
  all of them only when the whole chain passes (the scale assessment's
  closure pass). It would make "accepted" rest on a second mechanism, a
  [bypass] risk, before any measurement shows it is needed (G9).
- **Locks on every read.** Unneeded for write-once data, and they serialise
  the hot path (ADR 0009).
- **Resetting or rolling back the environment.** Brings back stale handles
  and generation counters; a new environment is cheap.
- **Checks writing their own results into the environment under a lock.**
  More writers and harder review than one publisher.

## Amendment 1 (2026-11-02): after the independent review of v0

The independent review of the first implementation (plan task 2.2.2,
`src/kernel/environment.fs` and `env-publish.fs`) found two faults and
several gaps. The changes below are stricter than, or clarify, the design
the owner accepted; they leave its status unchanged. The owner is asked
to confirm item 3.

1. **The publisher's name re-check (E4 step 1).** The design said "no
   accepted slot below `i` has the same name". That let an ok claim
   through when an earlier declaration of the same name was *undecided*
   or *unsupported*, where the check's own N2 lookup (E5) gives *unknown*
   or *unsupported* (K5): Lean may have accepted that earlier declaration
   and would then reject this one as already declared. The re-check now
   requires every same-named slot below `i` to be final and *rejected*,
   exactly the case in which the check's own N2 lookup says ok. A claim
   that fails it is a fault in LeanForth and is recorded as *invalid*.
2. **Replacing the context after a `THROW` (G-P6), also in the serial
   driver.** A `THROW` in a check can leave a context's state
   inconsistent (for example, walk frames still marked busy). The
   declaration is *invalid*, and the context is *spent*: it can begin no
   further check, and is freed and replaced rather than reused. In v0 the
   input is per context (E1, `src/core/input.fs`), so the serial driver
   gets a replacement from a maker the caller supplies, which must load the
   same input; the environment's input fingerprint (item 4) refuses any
   other. The driver frees the contexts it made and never frees the
   caller's. A parallel scheduler does the same at the job boundary. Once
   the input is a shared tier (plan task 7.2.1) the maker needs no reload.
3. **K5's tie-break (E5).** When the earlier declarations of a name
   include both an *undecided* and an *unsupported* one and none is
   accepted, a use of the name, and N2 on it, give *unknown*, whatever
   their order. This is the cautious choice: *unknown* says that more work
   might decide the question; neither answer is ever accepted.
   Recommendation to the owner: confirm unknown first.
4. **The input fingerprint: purpose and limits (E1).** Because the input
   is per context in v0, an environment records a fingerprint of the input
   it was made over, and is usable only in a context whose input is intact
   and has that fingerprint. The fingerprint covers every input store's
   records, identities, count and generation below its mark, and, since
   this amendment, the name bytes and their count (before, two inputs
   differing only in the text of their names had the same fingerprint).
   It guards against mistakes, such as checking in a context that loaded
   another input; it is not a defence against forgery (its FNV-style
   mixing is not a cryptographic hash, and two inputs can share one). It is
   computed once, when loading ends; later changes to the input are caught
   by the store marks as far as counts and identities show, and by the
   tests' digests, never by the fingerprint.

The same review led to further implementation fixes that change no rule
of this design: only the publisher's entry may publish, and environments
are made, chosen and freed only outside jobs (G-P1); a check that begins
another declaration is a fault; results and handles are read within the
check's snapshot (G-P4); a pool that cannot be marked is a fault; and the
test-only fault-injection hook is compiled only into tests.

## Reproduction

The Lean files were read from
`https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/` on 2026-11-02
(`git ls-remote https://github.com/leanprover/lean4 refs/tags/v4.35.0`
shows the commit above). SHA-256 of the files not listed in ADR 0011:
`src/kernel/instantiate.cpp`
`42527c96f4053fb3cbf4c26fbd544b1c4e0399e5c41b0fd792935d1d42f8916a`,
`src/Lean/Util/CollectAxioms.lean`
`64f340d42f18c51ee83527f03fa69cc26415dd71dcf7fe71031b7760be90007d`.
No LeanForth test exercises this design yet; the Lean-side evidence for
the first checker is `make reference-first-checker` and
`make reference-binder-domains`.

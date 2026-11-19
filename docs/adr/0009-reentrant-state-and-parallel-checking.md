# ADR 0009: re-entrant state and parallel checking — proposal

Status: **accepted** by the owner, 2026-11-02, with native Forth tasks as
the parallel method ([owner decisions](../project/OWNER_DECISIONS.md#planning-answers-2026-11-02-later-the-same-day)). Shapes the code structure of untrusted,
in-progress modules; changes no typing or conversion rule. It answers roadmap
item C1 in part and sets the direction for C2.

Approval status: accepted 2026-11-02, gate: design, [OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md) section "Planning answers (2026-11-02, later the same day)"

## Problem

Checking a large development is mostly independent work: once the
declarations a theorem depends on are checked, many theorem bodies can be
checked at the same time. Lean's own build checks files in parallel the same
way. The owner expects complex theorems with many sub-theorems and
substantial Mathlib use, and wants the 12-core development machine used in
parallel.

Today almost every mutable cell is a global: 337 `VARIABLE`s, 73 `CREATE`d
tables, and 7 tables made by the library's defining words
(`make forth-metrics`, 2026-11-02). Many are used as registers between
words. Two kernel modules even borrow another module's scratch work stack.
Nothing can run twice at once in one Forth image.

## Facts measured (2026-11-02, this machine: 12 logical cores, WSL2)

- Gforth 1.0 has a native multitasker built on POSIX threads (`newtask4`,
  `execute-task`, `pass`, `semaphore`, `lock`/`unlock`) and per-task
  `USER` variables. Twelve CPU-bound tasks finished in 0.31 s against about
  1.8 s for the same work in sequence, using 1118% CPU: about 6×, which is
  consistent with 6 physical cores with two hardware threads each.
- Gforth 0.7.3 (the CI portability host) has only the cooperative
  multitasker: tasks take turns on one core. Forth-2012 standardizes no
  multitasking. The classic design — tasks with `USER` variables, `PAUSE`,
  semaphores — is common to Gforth, SwiftForth and VFX Forth, with
  different spellings of the task words.

## Decision (proposed)

1. **All per-check state lives in records, passed by address.** No word may
   keep state for one check in a global. Long-lived stores are records made
   by defining words (`store:`); each walk's stack, fuel and current node is
   a walk record (`walk:`). Scratch borrowed across modules is replaced by
   each module's own record. The metrics script counts every such table as
   a global, so progress stays measurable.
2. **One checker context per worker.** A check's records (term, level and
   name stores, walk records, session) are grouped into one context record.
   Module words reach their state through a single current-context pointer,
   so their stack effects stay short. That pointer is a `USER` variable,
   giving each Forth task its own context; a host without tasks has one
   worker.
3. **The checked environment is append-only, then read-only.** A declaration
   joins the shared environment only after it is checked, and is never
   modified afterwards. Workers read it without locks. A scheduler hands out
   declarations whose dependencies are all checked, and publishes results in
   dependency order. No worker can see another worker's partial results,
   scratch or assumptions (roadmap C2).
4. **Forth tasks, not operating-system processes.** The owner prefers a
   Forth-compatible solution to Linux multiprocessing. Parallel checking runs
   as Forth tasks in one image, sharing one copy of the environment, each
   with its own context through its `USER` pointer. The few task words
   (create, start, wait) live in one small adapter file per host. On Gforth
   1.0 the tasks run on all cores; on a cooperative multitasker such as
   Gforth 0.7.3 they take turns, which still tests in CI that interleaved
   contexts do not interfere. One worker in one task is the serial path.
   (Running the checker as its own program, apart from user Forth code, is
   a separate protection decision, OQ-1.)
5. **Parallelism never bypasses checking.** A result checked in parallel
   must equal the serial result; tests compare them.

## Order of work

1. Done: `store:` and `walk:` records; the term, level and name stores and
   the four lowest walkers converted (roadmap Q10).
2. Convert the remaining modules' registers and borrowed stacks to records
   during the refactor.
3. Done (2026-11-02): introduce the context record and current-context
   pointer, with a test that runs two contexts interleaved in one image and
   compares with serial runs. `src/lib/context.fs` and the job pool
   `src/lib/task.fs` came first; then every module of `src/core/` and
   `src/kernel/` moved its state into the context (stores, walk and frames
   records, module records, and set-up words for what used to be reset
   while loading). `tests/core/contexts.fs` checks that every state word
   lies inside the current context, that a new context starts with the
   bytes the main context had after loading, and that a trial of real
   checker work gives its serial digest when contexts are interleaved in
   one task and when trials run as jobs (threads on Gforth 1.0,
   cooperative on 0.7.3, serial); `contexts-serial.fs` runs it on the
   serial host. Reaching state through the context cost about 13% of
   checker time on `gforth` and 23% on `gforth-fast`; since members became
   colon definitions with compiled offsets (2026-11-02) it costs about 9%
   and 15% (measured in
   [the library notes](../development/FORTH_LIBRARY.md#design-per-task-contexts-and-how-modules-convert)).
   Still global by design: the job pool, the context layout, constant
   tables and the deferred words set once while loading. Converted since:
   the loader's batch, the NDJSON counter's tally (its export record owns
   heap buffers and stays shared), the term printer, and the program reader
   and interpreter; the line and JSON readers keep their state in records
   their callers pass. Since 2026-11-02 `tests/core/contexts.fs` and
   `contexts-main.fs` also check that the dictionary the modules lay down
   while loading is unchanged after real checker work, which finds state
   left outside the context without a list.
4. A dependency-ordered scheduler and native tasks through the adapter,
   validated against serial runs (roadmap C3). Serializing the checked
   environment is needed later for the separate checker program and saved
   results, not for parallelism. Built on 2026-11-11 (plan task 7.3.1;
   [Amendment 2](#amendment-2-2026-11-11-the-scheduler-built)): `check
   --jobs N`.

## Amendment 1 (2026-11-03): context members that own heap memory

Approval status: accepted 2026-11-12, gate: none (library rule; touches [runtime] memory safety), [OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md) section "Approval round of 2026-11-12, night (approval pack)": the owner's approval was conditional on the Forth review of src/lib/context.fs, which found nothing blocking ([report](../development/forth-reviews/2026-11-12-context.md); its low findings are plan work)

**The rule until now.** A context member held no `ALLOCATE`d memory
([the library notes](../development/FORTH_LIBRARY.md#design-per-task-contexts-and-how-modules-convert),
"Rules for converted modules"): `context-free` gave back the context's own
block and nothing else, so a heap block a member pointed at would have
leaked with every freed context. Modules that own heap buffers (the NDJSON
counter's and the re-exporter's export records) therefore stayed shared.

**Why it changes.** [ADR 0016](0016-compact-store.md) C3 gives every check
a *scratch tier*: growable heap stores and hash tables, owned by the
check's context and emptied after each check. A per-context scratch tier
is the only way checks running in parallel can each build terms without
locks, and its blocks must be given back when the context is freed, also
when the job that used it ended with a `THROW`.

**The new rule** (`src/lib/context.fs`, `context-teardown`). A member may
own heap blocks only if its module registers, while loading, a *teardown
word* `( -- )` that frees them. `context-free` runs every teardown word,
newest first, in the context being freed (selected as the current context
afresh before each, so that one which threw with another context selected
cannot make the next free that context's blocks), and then frees the
context's block; `context-new` runs them too when a setup word fails,
before it gives its block back, and gives the setup word's code, the
earliest failure. A
teardown word must free exactly what its member holds, whatever happened
to it: after a `THROW` in the middle of a check, and on a member that its
setup word never reached (still zeroed), so it frees only the blocks it
finds and zeroes what it freed. It must not make, free, claim or select
contexts. Each runs balanced under `CATCH`: one that throws or changes the
stack does not stop the others or keep the context's block, and
`context-free` then gives the first such code instead of `FREE`'s ior.
Registering a teardown word after the layout is sealed aborts, like every
declaration. The main context is never freed, so its members keep their
blocks until the program ends. Members without heap memory need nothing
new; shared heap-owning records may stay shared.

*Not chosen:* a release word stored with each member (one module may own
several members, or one block for several, and a word pairs naturally
with `context-setup`); and a per-context registry of every block
allocated (every allocation would have to go through it, and `RESIZE`
moves blocks behind its back, as `slab.fs` and `htab.fs` do when they
grow).

**Evidence.** `tests/lib/context.fs` counts heap blocks
(`tests/support/heap-watch.fs`): a new context holds its block and its
member's, and freeing it gives both back; a check that grows the member's
block and adds a second one, then throws, leaves nothing behind once the
context is freed; teardown words run newest first and in the freed
context, also when it is the current one; one that throws (code 91) or
leaves an extra item (`context-unbalanced`) does not keep any block; a
setup word that fails after another allocated gives that block back; the
randomized model of 6,000 steps with 50 new contexts ends with no block
held. `tests/core/stage.fs` makes a scratch tier over a sealed input tier
a context member and frees it the same way, also after a `THROW`. Three
planted faults in `tests/mutants/faults.toml` (`context-teardown-…`,
`context-new-failure-leaks`) are each caught. Run on Gforth 1.0 and 0.7.3.

## Amendment 2 (2026-11-11): the scheduler, built

Approval status: accepted 2026-11-12, gate: kernel and runtime, [OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md) section "Approval round of 2026-11-12"; the entry names S7 (check --jobs N) (gate recorded 2026-11-12 night: kernel and runtime, [OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md) section "Approval round of 2026-11-12, night (approval pack)")

**What.** `leanforth check --jobs N` (plan tasks 6.5.4, 7.3.1; default
1, the serial run, unchanged) checks with N worker contexts, each a job of
the pool of `src/lib/task.fs` (threads on Gforth 1.0, cooperative on
0.7.3, serial elsewhere), and publishes in the driving task through
[ADR 0012](0012-checked-environment.md)'s single publisher. The scheduler
is `src/kernel/env-schedule.fs`; its rules are in ADR 0012
([Amendment 2](0012-checked-environment.md#amendment-2-2026-11-11-the-parallel-scheduler)).
The input is still per context (E1, plan task 7.2.1 not done): each worker
is fed the same sealed stage, which is shared read-only, and must have
the input fingerprint of the run's context; the stage, the environment and
the job pool are the only shared heap data.

**The audit of state added since 2026-11-02** (task 1 of the brief; every
table must be a context member or read-only after loading). Verdicts:
- `kernel/caches.fs` (result caches): context members, emptied when a
  check begins: safe.
- `kernel/replace-memo.fs` (substitution memo): one table per pass and
  context; stamped entries emptied when an inference job starts; costs no
  fuel: safe.
- The audit memo (`core/constant-term-boundary.fs`, `lf-audit-state`,
  `lf-audit-reached`, the marks): context members, new epochs with every
  check: safe. Its tables `lf-audit-facts` and the hook are read-only after
  loading.
- The S3/S4 hash tables (`core/terms.fs` term table, `core/levels.fs`
  level table, `core/constant-references.fs` interning): context members;
  a rollback takes its records' entries out (Algorithm R), so each check
  starts from the same set: safe. Their hook records (`lf-term-hooks` and
  the like) are filled while loading, read-only after.
- Level and reference interning, the stamp map (`generation-handles.fs`):
  context members, rolled back with the input marks: safe.
- Literals (`core/literals.fs`, `string-literals.fs`): limb and byte
  slabs per context, not rolled back (unreferenced limbs stay); no check
  reads another check's limbs: safe, memory grows per worker.
- `kernel/inductive-nested.fs`, `kernel/quot.fs`: state in context
  records; `lf-quot-entries` is a constant table: safe.
- The input view and its leaf table (`core/terms.fs`), the binder table,
  the names' view (`core/names.fs`): per context over the sealed stage
  tier, whose finds write nothing (`lib/cons.fs`: a sealed set's table is
  frozen); names a check makes go into the context's own scratch tier:
  safe.
- **Found and fixed:** the level scope memo of `kernel/level-compare.fs`
  (a column keyed by level identity and the parameter context's
  generation) outlived its check, so an input level checked in an earlier
  check cost no fuel in later ones: a check's fuel depended on which checks
  its context had run (63 of the first 9,202 declarations of `Init` used
  1-8 more units in a worker). It now also holds the audit memo's
  per-check epoch, so it lasts one check, as documented; serial fuel on
  that prefix rises by 2,753 units (0.003%) in 871 declarations, verdicts
  unchanged.
- Shared and written while checks run: only by the driving task, outside
  jobs: the environment (slots, pool, header), `lf-envs`, the scheduler's
  record `lf-sched`, `cli/check-run.fs`'s run records, the job pool.
  `tests/core/contexts-main.fs` checks that a parallel check leaves every
  other byte of the dictionary unchanged, and catches a planted check
  that writes a shared cell.
Still global by design and read-only during checks: catalogues, rule
tables, `htab` hook records, the derivation log's options (set only
outside jobs), deferred words set while loading.

**Amendment 2, review rvS7 (2026-11-11).** The worker count is cut to the
cores and the pool's queue (`ck-jobs!`); the pool is started before the
run, so a refusal leaves the whole run to the serial one, with the cause
in the resource report; a run with no worker left ends as the serial run
stops (declarations past the stop are dropped from the ready heap first).
Threads run only on x86-64 (`lf-sched-host-ok`, read once from
`/proc/sys/kernel/arch`; unreadable counts as another architecture): the
publisher writes a slot's fields and then its final state, and checks read
the state first, which is correct with x86-64's store order but has no
memory barrier; cooperative and serial hosts are not affected. Known and
left: (m1) the early-read test runs before the hand-over, so an early read
first noted during the publisher's re-checks is published as invalid
(fail closed, never accepted; not reached by any test), a rerun would
need a test between the re-checks and the publication; (m3) a declaration
has about 23 readiness edges for builtin names, about 400 MB on all of
Mathlib, one barrier would replace them; (m4) the scratch name tier is not
rolled back per check, so name ids differ between workers and the tier
grows, harmless because only equality uses them, found by `lookups.

**Evidence.** Output (text and JSON but `measured`) identical to `--jobs
1` on all 388 test exports at 3 workers and on the first 1M lines of
`Init` (9,202 declarations) at 4; full `Init`: see ADR 0012 Amendment 2.

## Amendment 3 (2026-11-18): the re-entrancy audit, guarded and tested

Approval status: proposed, awaiting the owner (gate: kernel in form, for
the guards of `core/terms.fs` and the test-build counter of
`kernel/environment.fs`; plan 9.4.8p, branch `parallel-1`)

The audit of main `c240a927` found no definite race
in the release build and five items; this amendment records what was done.

- **M1, the borrowed input during a run.** The driving task never writes
  the input the workers read in place while they run: the carry pass's
  decision on readiness (`ck-pre`, env-import.fs `imp-decide`, `take`,
  `imp-fill`) and the ticks (`ck-tick`, the line word) only read it,
  publish into the environment (as designed), intern names in the driving
  context's own name pool and roll their own scratch back to the input's
  marks, which neither grows nor moves a block the workers read. That is
  now checked, not assumed: `cli/check-run.fs` keeps each part's block and
  count (the view's three tables and leaves, the declarations, their name
  index and inductive data, the references) when the workers are made,
  compares them before each hand-out and around each tick, and on a change
  stops the run as an internal fault, its verdicts read only below the
  slots final at the change (exit 5). A transient write that is rolled back
  before the next comparison is not seen; the Forth stress test hashes the
  borrowed input before and after a run as a second check.
- **L2, load-time tables.** `core/terms.fs`'s tag tables
  (`lf-term-unshare`, `lf-tin-leaf-tags+`, `lf-term-input-tag!`,
  `lf-term-input-twin!`) and `lib/store-columns.fs`'s `column-add` abort
  once `context-sealed?`, as context members do; every caller runs while
  loading, before the first `context-new`, and behaves as before.
- **L1, the test build's I2 counter.** `lf-i2-misses` (test build only)
  adds with `lib/task.fs`'s `task+!`: Gforth 1.0's `atomic+!@` (a locked
  `xadd`) with threads. Gforth's `+!@` is not atomic.
- **L3, no fence.** Not changed: Gforth 1.0's `barrier` is a full fence (a
  locked `or` on x86-64); threads still run only on x86-64
  (`lf-sched-host-ok`), whose store order makes the publisher's protocol
  correct. A `barrier` in a task.fs adapter around the final-state store
  and its read stays a plan item for other hosts.
- **M2, tests.** `make parallel-init` (daily) and `make
  test-parallel-stress` (`docs/development/TESTING_STRATEGY.md`, "Parallel
  checking").

## Rejected alternatives

- **Pass a context on the stack to every word.** Most transparent and
  portable, but it adds a stack item to nearly every word, against the style
  guide's limit of about three inputs. A single current-context pointer
  gives the same isolation.
- **Locks around shared mutable stores.** Serializes the hot paths and
  invites races; an append-only environment and per-worker scratch need no
  locks on the read path.
- **Operating-system processes for parallelism.** Portable and crash
  isolated, but each process holds its own copy of the environment (the
  limiting memory cost at Mathlib scale) and needs serialization before any
  speed-up; the owner prefers Forth's own multitasking.

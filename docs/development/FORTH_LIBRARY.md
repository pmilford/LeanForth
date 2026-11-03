# Forth library inventory

What reusable Forth facilities exist, how mature they are, and what the
product will need that does not exist yet. Everything listed is untrusted
experimental code unless stated otherwise; none is a reviewed kernel
component. Measured 2026-11-02 at commit `4779924`; library entries updated the same day. Modules are in
`src/core/` (data model) or `src/kernel/` (checker passes) unless named
with another folder ([source layout](../../src/README.md)); the superseded
variants were retired on 2026-11-02.

## What exists

| Facility | Module(s) | What it is | State |
| --- | --- | --- | --- |
| Bounded record stores | `src/lib/store.fs` | `store:` defining word: a fixed number of fixed-width records with an allocation count, a reset generation that saturates to a poisoned state, an identity per record that never repeats, and a sealed shape so header corruption fails closed. `store-size` and `store-init` make the same store in memory obtained at run time (`ALLOCATE`, or a region of a context); `store-plan?` also refuses a size that would not fit in a cell | New 2026-11-02; used by the term, level and name stores; unit-tested in `tests/lib/lib.fs`, run-time stores in `tests/lib/context.fs` |
| Tagged nodes | `src/lib/node.fs` | `BEGIN-STRUCTURE` record of tag and two fields, with whole-node `node!`/`node@` and `node-new`/`node-read` on a store | New 2026-11-02; terms and levels |
| Range checks | `src/lib/bounds.fs` | `between?` and `upto?` (inclusive, signed, never wrapping) and `cells-zero?` | New 2026-11-02 |
| Outcome vocabulary | `src/lib/outcome.fs` | ok, invalid, exhausted (out of fuel), unknown, rejected, unsupported and full (out of room: a store, work stack, frame, depth or size limit) (ADR 0008), with `ok?`, `outcome-sane`, `flag>outcome` and `room>outcome` (a validity or room flag as ok, else invalid or full), `visit-outcome` (the one rule for a visit bounded by fuel and room: no fuel is exhausted whatever the room, then no room is full), the continue-on-ok steps `ok-then?`, `ok-keep?` and `ok-keep2?`, and `no-result` | New 2026-11-02; every core and kernel module uses it; the per-module status aliases were removed |
| DAG walks | `src/lib/walk.fs` | `walk:` defining word: fuel, current node, one visitor cell and a bounded work stack in one record; `walk-run` drives a visitor and `walk-visit` reads and dispatches a node. A push without room is full whatever fuel is left (checked where the push happens), and a root that cannot be pushed means a corrupted capacity, which is invalid. `walk-size`/`walk-init` and `walk2-size`/`walk2-init` make the same records at run time. The walk words keep no state of their own, but each module still owns one walk record, so a module's check is not re-entrant | New 2026-11-02; level scope, Sort representation, session and handle audits use it |
| Bounded recursion | `src/lib/frame.fs` | A frames record: fuel, visits in progress and their limit, the visitor (set once), a context cell (such as a binder depth) and a job cell pointing at the pass's own record. `frames:` defines a standalone record and `frame-init` sets one up inside a larger record. `frame-call` charges one unit of fuel and one frame per visit of a visitor `( x frames -- result outcome )`, `frame-call2` the same for `( x y frames -- outcome )`, `frame-under` visits one context level deeper, `frame-run` starts a pass. `frame-room` says why a visit cannot open: a limit below 1 (a corrupted record) is invalid, then no fuel left is exhausted and no free frame full (`visit-outcome`, so the fuel decides); `frame-under` applies the same before its context, which is full at `max-n`. A busy record refuses a new budget or pass, so a pass cannot be restarted from inside itself; `frame-reset` recovers after a THROW. Values a visitor keeps across a child's visit stay on the data stack, so each nested visit holds host stack cells: measured 2 to 6 return-stack and 3 to 4 data-stack cells per frame, and 701 and 494 cells at the deepest nesting found for a 64-node store (124 frames of beta, instantiate and shift), the same on Gforth 0.7.3 and 1.0. `mixed-beta.fs` checks at load time that the host's stacks hold three times `lf-term-capacity` frames | New 2026-11-02; the kernel's shift, instantiate and beta passes use it; unit tests and a randomized model test |
| Checker contexts | `src/lib/context.fs` | One `ALLOCATE`d record per worker for all of a check's mutable state ([ADR 0009](../adr/0009-reentrant-state-and-parallel-checking.md)), reached through the `USER` variable `lf-context` (a plain variable on hosts without Gforth's `USER`). Modules declare members while they load: `context-record:`, `context-store:`, `context-walk:`, `context-walk2:`, `context-frames:` (a frames record, set up with `frame-init`), and `context-setup` for set-up words; a refused declaration changes nothing. `context-new`, `context-use` and `context-free` make, select and free contexts. Each context is idle or owned by one job; each task has an owner token `lf-owner` and may select only contexts it owns (the main task: idle ones); owned contexts cannot be freed | New 2026-11-02; ownership, frames members and atomic declarations 2026-11-02 after an independent review; no module uses it yet (see the design below); tested in `tests/lib/context.fs`, including a randomized model with context switches at every step |
| Job pool | `src/lib/task.fs` | `job-submit ( context xt -- job ior )` and `job-wait ( job -- ior )`: a fixed pool of long-lived workers (at most one per logical core, setting `task-workers`) fed from a bounded queue; POSIX threads with a mutex and two condition variables on Gforth 1.0, the cooperative `tasker.fs` on Gforth 0.7.3, and a serial path elsewhere (or when forced, for tests). A job's context is owned by the job until it is waited for. Wrong stack effects give `task-unbalanced`; stack overflows never report success (guard pages on 1.0, canary zones on 0.7.3); a worker that cannot be created is reported (`task-no-worker`). `job-stacks-cover?` tells whether the workers' stacks hold a recursion requirement. Not loaded by `src/main.fs`; the scheduler will load it | New 2026-11-02; pool replaced one thread per task the same day; `tests/lib/task.fs` and `task-serial.fs` compare jobs and interleaved contexts with serial runs for 1, 2 and all workers and reach every refusal; `task-overflow.fs` and `task-overflow-serial.fs` overflow both stacks inside jobs; `tests/lib/task-bench.fs` measures speed-up |
| Line reader and UTF-8 | `src/lib/bytes.fs` | `reader:` record over a Forth-2012 file: whole lines in one heap buffer that grows for long lines up to a limit, strict framing (final line feed; `text-framed` refuses carriage returns and a byte-order mark), line numbers and double-cell file offsets; `utf8-length`, `utf8-valid?` and `utf8-put` (RFC 3629, no overlongs or surrogates); `counted,`; `heap-claim` and `heap-release` for owned heap buffers. Uses Gforth's native `scan` behind an adapter, with a portable loop otherwise | New 2026-11-02; unit-tested against an independent UTF-8 model in `tests/lib/bytes.fs` |
| JSON reader | `src/lib/json.fs` | `json:` view record: a fail-closed, non-recursive RFC 8259 parser of one text into a growable token tape (containers know their item count and extent), escapes decoded in place, numbers kept as digit text, limits on depth, tokens, string and number length; `json-find`, `json-next`, `json-natural`, `json-u`, `digits>u` and `decimal>u` (decimal, independent of `BASE`); kind-checked `json-items-of` and `json-kind-at` | New 2026-11-02; malformed corpus and every limit tested in `tests/lib/json.fs` |
| Portability adapter | `src/lib/portability.fs` | Forth-2012 definitions of `>=`, `<=`, `0<=`, `0>=`, `max-n` and the structure words, compiled only where the host lacks them | New 2026-11-02; defines nothing under Gforth except `max-n` |
| Expression store | `src/core/terms.fs` | Index-based nodes for sorts, bound variables, application, λ, Π and constants; nodes refer to earlier indices, so a term is a DAG with sharing | 64 nodes; global; built on `store:`; constructors check ranges only |
| Universe-level store | `src/core/levels.fs` | Level DAGs: zero, succ, max, imax, parameters | 64 levels; global; built on `store:` |
| Name interning | `src/core/names.fs` | Lean structured names (string and numeric components) stored once and referred to by index | 64 names, 2,048 bytes; built on `store:` with named entry fields; lookup is a linear scan, no hashing |
| Stale-handle detection | `src/core/generation-handles.fs`, `symbolic-session.fs` | Handles carry a generation number so a handle from before a reset is rejected | Works; tests found one unguarded path |
| Constant references | `src/core/constant-references.fs`, `constant-term-*.fs` | A constant's name plus universe arguments, with syntax and scope audits | Global, 32 references |
| DAG walkers | `mixed-shift`, `mixed-instantiate`, `mixed-beta`, `mixed-compare`/`mixed-convert`, `mixed-infer` in `src/kernel/` | Bounded traversals with explicit work stacks and fuel, rolling back on failure | Current; the earlier plain and `tagged-` variants were retired 2026-11-02 (roadmap Q9) |
| Level algorithms | `level-scope`, `level-value`, `level-compare`, `level-substitute`, `mixed-level-substitute` | Scope checks, evaluation, conservative equality and simultaneous substitution of levels | Current |
| Signature index | `mixed-signature-probe.fs`, `mixed-signature-audit.fs` | Candidate signatures of constants, specialised to universe arguments | 32 entries; unchecked assumptions |
| Record staging | `src/import/load.fs` | Copies already-decoded expression records into the term store | Not a parser; stages concrete Sorts, which no current checker pass accepts; kept with its round-trip tests until the Forth NDJSON reader replaces it |
| NDJSON export reader | `src/import/ndjson.fs`, `ndjson-count.fs` | Decodes every record kind of lean4export format 3.1.0 into decoded-record layouts and hands each to a handler per kind; checks exact field sets, dense indices and earlier references; a counting tool | New 2026-11-02; untrusted, fail-closed; equal to Python on all of Mathlib; see [NDJSON_READER.md](NDJSON_READER.md) |
| Presentation side table | `src/present/binder-table.fs` | Binder names and kinds, source record IDs and declared constant types, keyed by term index and stamped with the term's identity and the name store's generation, so a reset makes entries read as absent; never read by the checker | New 2026-11-02; one context record; 64 term entries, 32 declarations; `tests/present/term-printer.fs` |
| Term printer | `src/present/term-printer.fs` and `print-job.fs`, `print-names.fs`, `print-tokens.fs`, `latex-text.fs`, `print-levels.fs`, `print-analysis.fs` | Prints terms, levels and names to a caller's sink xt in Lean's notation, ASCII or LaTeX (and Markdown math): capture-free binder names, ∀/→ and binder grouping, hidden implicit arguments and minimal parentheses as Lean's delaborator; fuel, a nested-visit limit (one `frames` record for all recursion) and a name pool, all failing as exhausted | New 2026-11-02; agrees with Lean on 49 cases and the five pinned fixtures (`make test-printer-differential`); [user guide](../user/TERM_PRINTER.md) |
| Program examples | `src/program/clamp.fs`, `examples.fs` | Six executable words (clamp, checked add, abs, factorial, gcd, in-range) | Runtime tested against Lean models, not verified |
| Depth analyzer | `src/program/program-depth.fs` | Stack-depth diagnostic for a tiny opcode list | Not connected to real Forth words |
| Test support | `tests/support/tester.fs`, `checks.fs`, `term-cases.fs`, `composition.fs` | Adapter for Gforth's bundled tester that fails the run on the first error; shared checks and fixtures | Test-only |

## JSON and NDJSON

Since 2026-11-02 Forth reads Lean's NDJSON exports itself (owner decision
OQ-4): `src/lib/bytes.fs`, `src/lib/json.fs` and `src/import/ndjson.fs`,
described in [NDJSON_READER.md](NDJSON_READER.md). It decodes the whole
pinned Mathlib export, field for field as Python's `json` module does, in
under two minutes with `gforth-fast`. It does not yet stage records into
the term, level and name stores (they hold 64 entries each). The Python
preview (`tests/support/ndjson_preview.py`) and the eleven hand-written
Forth stream readers of its byte transport (`tests/core/*-stream.fs`) remain until their tests move to the Forth
reader (plan item 3.2.5); the Python code stays as a test oracle only.

## Missing for a usable checker at Mathlib scale

- **Capacity and memory.** Every store holds 64 entries in fixed global
  arrays. Mathlib's export has millions of expression nodes. Needed: growable
  or file-backed arenas, explicit memory budgets and measured limits.
- **Hashing and hash-consing.** Names are found by linear search and terms are
  not shared by content. Needed: hash tables for names and structural sharing
  of identical terms and levels.
- **Records and defining words.** `store:` and the node and name records now
  cover the term, level and name stores (2026-11-02). The other modules still
  re-implement array-plus-count storage with raw offsets and should move onto
  `store:` and named fields as they are refactored (roadmap Q10).
- **One outcome vocabulary.** 34 words translate one module's status codes
  into another's. A shared set of outcomes (ok, rejected, unknown, invalid,
  exhausted, full) would remove them.
- **Dispatch tables.** Walkers branch on node tags with long `IF` chains; no
  execution-token tables are used.
- **Namespaces.** No wordlists; the `LF.CORE`, `LF.KERNEL` modules planned in
  the handoff do not exist.
- **Re-entrancy.** Most state is still global, so only one check can run per
  Forth image (roadmap C1–C4). Stores and walks are now records, and the
  context and job-pool machinery exists (below); the modules still have to
  move their state into contexts, and the scheduler is still to be written
  (ADR 0009).
- **Serialization.** No deterministic, architecture-independent format for
  checked terms or receipts.
- **Pretty-printing and explanation.** No printer for terms, levels or proof
  steps.
- **Moving the test readers onto the Forth NDJSON reader**, retiring the
  eleven byte-stream readers, and staging decoded records into growable
  stores.

## Design: per-task contexts and how modules convert

Implemented 2026-11-02 in `src/lib/context.fs` and `src/lib/task.fs`
([ADR 0009](../adr/0009-reentrant-state-and-parallel-checking.md)) and
revised the same day after an independent review (contexts gained owners,
frames members and atomic declarations; one thread per task became a pool
of workers); no module uses them yet. Untrusted, like the rest of the
library.

**Contexts.** All of one check's mutable state lives in one context record,
obtained with `ALLOCATE`. The current task finds it through `lf-context`, a
`USER` variable, so each Forth task has its own. Modules declare their
state as *members* of the context layout while they load; each member's
name ( -- addr ) gives its address in the current context. A *main context*
exists from the moment the library loads and grows with each declaration,
so a program that never makes another context runs exactly as before.
`context-new` makes a new context with every member initialised and every
set-up word run, in declaration order; it holds exactly the state the main
context had right after loading. `context-use` selects a context;
`context-free` frees one. A declaration first checks its arguments and
grows the main context with `RESIZE`; when either fails it aborts with
nothing defined and the layout unchanged. A set-up word that throws while
it is declared is not registered.

**Ownership and handles.** A context is *idle* or *owned* by one job. Each
task has an owner token, `lf-owner`: 0, or the job it is running. A task
may select only a context whose owner is its own token, so the main task
uses only idle contexts and a job only its own; an owned context cannot be
freed, and contexts are made and freed only outside jobs (`context-new`
and `context-free` abort inside one). A context's address is its handle,
valid until `context-free`; `context?` cannot recognise every stale handle,
because `FREE` may reuse the block's first cells and `context-new` may hand
out the same address again, so a handle must never be used after it is
freed. Handles into a context's stores (indices and identities) mean
something only in that context: every new context restarts its stores'
serial numbers, so such handles must never cross contexts.

**Converting a module** changes only the lines that define its state, the
ones its header lists under "State:". Nothing else changes, because the
module's words already reach their state only through those names.

| Today | In a context |
| --- | --- |
| `lf-term-capacity walk2: lf-cts-walker` | `lf-term-capacity context-walk2: lf-cts-walker` |
| `lf-level-capacity walk: lf-lsubst-walker` | `lf-level-capacity context-walk: lf-lsubst-walker` |
| `lf-term-capacity /node 0 store: lf-terms` | `lf-term-capacity /node 0 context-store: lf-terms` |
| `create lf-lsubst-job /lf-lsrec allot` and `lf-lsubst-job /lf-lsrec erase` | `/lf-lsrec context-record: lf-lsubst-job` (members start zeroed) |
| a frames record set up with `frame-init` after its visitor, such as `lf-term-capacity ' lf-mbeta-visit lf-mbeta-frames frame-init` | `lf-term-capacity ' lf-mbeta-visit context-frames: lf-mbeta-frames` (declared after the visitor, which reaches the record through its frames argument) |
| load-time set-up such as `lf-level-reset` at the end of `levels.fs` | `' lf-level-reset context-setup` (runs now in the main context and in every new one) |

Rules for converted modules:

- Declare every member before the first `context-new`, `job-submit` or
  `pool-start`; each seals the layout, and a later declaration aborts.
- Initial state must come from a member's initialiser or a set-up word.
  Interpret-time code that changes state while a module loads changes only
  the main context. Set-up words must not change data outside the context.
- Never keep a member's address in a variable, a constant or another
  record: the address differs in every context, and the main context can
  move while modules load. Records hold indices, not addresses.
- Loose `VARIABLE`s and `CREATE`d arrays (for example `level-scope`'s
  parameter list, `mixed-infer`'s binder stack) are first grouped into one
  record (`BEGIN-STRUCTURE`) and then declared with `context-record:`.
- Data that tasks share — the checked environment, constant tables built at
  load time — stays outside contexts and must not change while jobs run.
- A member that owns heap memory would need a release hook in
  `context-free`; none exists yet, so members hold no `ALLOCATE`d memory.

**Jobs.** `job-submit ( context xt -- job ior )` claims the context for a
new job and queues it; a worker runs `xt ( -- )` with that context
selected. `job-wait ( job -- ior )` waits until the word has returned or
thrown, releases the context, frees the job and gives 0 when the word
returned with the stack balanced; otherwise the word's `THROW` code,
`task-unbalanced`, `task-overflow`, or `FREE`'s ior. **0 means only that
the word returned, never that a check was accepted**; on any other value
the scheduler must report a failure outcome and discard the context's
contents. Reporting `THROW` codes leans on the CATCH/THROW convention,
which still needs an ADR. One task outside the pool (normally the main
task) drives it: it alone submits, waits, and starts and stops the pool;
a job never submits, waits, makes or frees contexts, or selects another
context. The adapter chooses one of three hosts when it loads:

| Host | Gforth | How jobs run |
| --- | --- | --- |
| threads | 1.0 (`newtask4`, `pthread_create`, `pthread_cond_wait`) | A fixed pool of long-lived POSIX-thread workers on all cores, fed from a bounded ring queue. One mutex, `task-lock`, guards the queue and every job's done flag and result; idle workers wait on one condition variable and waiting tasks on another, so a finished worker touches only the mutex and the conditions after it unlocks. Worker threads are joinable and are joined by `pool-stop`; `bye` stops the pool first, as Gforth's own `cilk.fs` does |
| cooperative | 0.7.3 (`tasker.fs`) | The same pool and queue on one core; workers switch only at `task-yield` and while a task waits |
| serial | any other Forth, or forced by defining `task-serial-only` | No workers: `job-submit` runs the word at once, to the end, in the calling task |

| Setting | Default | Meaning |
| --- | --- | --- |
| `task-workers` (value) | `task-cores` | Workers the pool starts, kept between 1 and `task-cores`; change it with `TO` while the pool is stopped (`pool-stop`) |
| `task-cores` | logical cores online | Read from Linux's `/sys/devices/system/cpu/online` when `task.fs` loads; 1 where that cannot be read |
| `task-data-cells`, `task-return-cells` (values) | 8,192, or the main task's if larger | Depth of each worker's data and return stacks; raise them with `TO` while the pool is stopped |
| `task-slack-cells` | 64 | Cells of each stack the worker's own words use below a job's word |
| `task-guard-cells` | 1,024 | Canary cells beyond each stack on Gforth 0.7.3 |
| `task-queue-jobs` | 1,024 | Most jobs queued and not yet taken by a worker |

| Refusal (job 0) | Code |
| --- | --- |
| not a context, the main context, the caller's current context, a context another job owns, or a submission inside a job (`job-wait` inside a job gives the same) | `task-refused` (-4098) |
| the queue holds `task-queue-jobs` jobs | `task-queue-full` (-4099) |
| a worker task or thread could not be created (the workers already started are stopped) | `task-no-worker` (-4100) |
| Gforth 0.7.3, after an overflow that left a guard zone | `task-overflow` (-4097) |

**Stacks, frames limits and overflows.**

- A recursive pass nests about its frames limit times its cells per frame
  (2 to 6 return-stack and 3 to 4 data-stack cells measured, see
  `frame.fs` above) plus its entry words. A module that runs in jobs must
  check at load time that `job-stacks-cover? ( data-cells return-cells --
  flag )` holds for its worst nesting: the workers' depths less
  `task-slack-cells`, or on the serial host the main task's stack sizes
  less the slack (the caller's own use also comes off those). If not, it
  raises `task-data-cells` and `task-return-cells` or lowers its limits.
  The test job's 500-frame pass used 1,004 return-stack and 1,001
  data-stack cells inside each worker; checker passes were measured at up
  to about 720 return cells, and nested passes may approach 1,500.
- A stack overflow inside a job is never reported as success. Gforth 1.0:
  the guard pages give `THROW` -3 (data) or -5 (return), and the worker
  goes on serving jobs. Gforth 0.7.3 has no guard pages for task stacks:
  each worker keeps `task-guard-cells` canary cells beyond the far end of
  each stack, checked after every job; an overflow into them gives
  `task-overflow` and the worker goes on. An overflow beyond them may
  already have corrupted the worker's user area or other memory, so it
  gives `task-overflow` and breaks the pool: every later job fails. A
  runaway recursion on 0.7.3 can still crash or hang the program before the
  check (it then reports nothing). Serial host: the job runs on the
  caller's stacks, where an overflow is the host's `THROW`.
- A job's word runs above a sentinel (its job's address): a word that
  leaves, consumes or replaces a cell gives `task-unbalanced`, and the job
  record and the memory around it are never touched.

**Limits.**

- Nothing may `ALLOT`, `CREATE` or compile while the pool runs: all tasks
  share one dictionary, and all run-time memory comes from `ALLOCATE`.
- Each context holds a full copy of every module's stores, so memory grows
  with the number of contexts; this will matter at Mathlib scale (see the
  [scale assessment](../project/SCALE_ASSESSMENT.md)). The pool itself
  keeps memory and threads flat: over 39,984 jobs on 12 workers the
  process stayed at 9,552–9,556 kB resident and 13 threads (Gforth 1.0,
  2026-11-02). Each worker creation costs about 1.3 kB that Gforth never
  returns (200 stops and restarts of 12 workers added 3.2 MB), and a task
  whose thread could not be created is not freed.
- On Gforth 1.0, a failed `newtask4` also prints "Cannot allocate memory"
  to standard error.
- The cooperative and serial hosts run one job at a time: they test that
  contexts do not interfere, not speed.

**Measured speed-up** (Gforth 1.0, this machine: 12 logical cores, WSL2,
2026-11-02; `gforth tests/lib/task-bench.fs`, three runs). Twelve jobs of
400 rounds of the test job, run one after another in one task against
running them on a pool of that many workers (started before the clock).

| Workers | Serial (ms) | Pool (ms) | Speed-up |
| --- | --- | --- | --- |
| 1 | 3,090–3,139 | 3,072–3,222 | 0.95–1.01 |
| 2 | 3,047–3,125 | 1,564–1,644 | 1.86–1.99 |
| 6 | 3,079–3,145 | 630–719 | 4.37–4.96 |
| 12 | 3,082–3,248 | 512–541 | 5.69–6.25 |

Twelve workers gain about 5.7–6.3 times, consistent with six physical cores
with two hardware threads each (the ADR's earlier probe measured about 6).

How the existing code should be written and refactored is in
[the Forth style guide](FORTH_STYLE.md).

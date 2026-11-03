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
| Checker contexts | `src/lib/context.fs` | One `ALLOCATE`d record per worker for all of a check's mutable state ([ADR 0009](../adr/0009-reentrant-state-and-parallel-checking.md)), reached through the `USER` variable `lf-context` (a plain variable on hosts without Gforth's `USER`). Modules declare members while they load: `context-record:`, `context-store:`, `context-walk:`, `context-walk2:`, and `context-setup` for set-up words; `context-new`, `context-use` and `context-free` make, select and free contexts | New 2026-11-02; no module uses it yet (see the design below); tested in `tests/lib/context.fs`, including a randomized model with context switches at every step |
| Task adapter | `src/lib/task.fs` | `task-start ( context xt -- task ior )`, `task-wait ( task -- ior )` and `task-yield`: POSIX-thread tasks on Gforth 1.0, the cooperative `tasker.fs` on Gforth 0.7.3, and a serial path elsewhere (or when forced, for tests). Not loaded by `src/main.fs`; the scheduler will load it | New 2026-11-02; `tests/lib/task.fs` and `task-serial.fs` compare tasks and interleaved contexts with serial runs; `tests/lib/task-bench.fs` measures speed-up |
| Line reader and UTF-8 | `src/lib/bytes.fs` | `reader:` record over a Forth-2012 file: whole lines in one heap buffer that grows for long lines up to a limit, strict framing (final line feed; `text-framed` refuses carriage returns and a byte-order mark), line numbers and double-cell file offsets; `utf8-length`, `utf8-valid?` and `utf8-put` (RFC 3629, no overlongs or surrogates); `counted,`. Uses Gforth's native `scan` behind an adapter, with a portable loop otherwise | New 2026-11-02; unit-tested against an independent UTF-8 model in `tests/lib/bytes.fs` |
| JSON reader | `src/lib/json.fs` | `json:` view record: a fail-closed, non-recursive RFC 8259 parser of one text into a growable token tape (containers know their item count and extent), escapes decoded in place, numbers kept as digit text, limits on depth, tokens, string and number length; `json-find`, `json-next`, `json-natural`, `json-u`, `digits>u` | New 2026-11-02; malformed corpus and every limit tested in `tests/lib/json.fs` |
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
  context and task machinery exists (below); the modules still have to move
  their state into contexts, and the scheduler is still to be written
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
([ADR 0009](../adr/0009-reentrant-state-and-parallel-checking.md)); no
module uses them yet. Untrusted, like the rest of the library.

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
`context-free` frees one.

**Converting a module** changes only the lines that define its state, the
ones its header lists under "State:". Nothing else changes, because the
module's words already reach their state only through those names.

| Today | In a context |
| --- | --- |
| `lf-term-capacity walk2: lf-cts-walker` | `lf-term-capacity context-walk2: lf-cts-walker` |
| `lf-level-capacity walk: lf-lsubst-walker` | `lf-level-capacity context-walk: lf-lsubst-walker` |
| `lf-term-capacity /node 0 store: lf-terms` | `lf-term-capacity /node 0 context-store: lf-terms` |
| `create lf-lsubst-job /lf-lsrec allot` and `lf-lsubst-job /lf-lsrec erase` | `/lf-lsrec context-record: lf-lsubst-job` (members start zeroed) |
| load-time set-up such as `lf-level-reset` at the end of `levels.fs` | `' lf-level-reset context-setup` (runs now in the main context and in every new one) |

Rules for converted modules:

- Declare every member before the first `context-new` or `task-start`;
  both seal the layout, and a later declaration aborts.
- Initial state must come from a member's initialiser or a set-up word.
  Interpret-time code that changes state while a module loads changes only
  the main context.
- Never keep a member's address in a variable, a constant or another
  record: the address differs in every context, and the main context can
  move while modules load. Records hold indices, not addresses.
- Loose `VARIABLE`s and `CREATE`d arrays (for example `level-scope`'s
  parameter list, `mixed-infer`'s binder stack) are first grouped into one
  record (`BEGIN-STRUCTURE`) and then declared with `context-record:`.
- Data that tasks share — the checked environment, constant tables built at
  load time — stays outside contexts and must not change while tasks run.

**What `frames:` needs.** `src/lib/frame.fs` (under review, so unchanged
here) should gain `frames-size ( -- u )` (that is, `/frames`) and
`frames-init ( limit frames -- flag )`, which zeroes the record and sets the
limit, or gives false and writes nothing for a limit below 1. Then `frames:`
is re-expressed through them, as `store:` and `walk:` now are, and
`context.fs` gains `context-frames: ( limit "name" -- )`. Until then a
module can declare `/frames context-record: name` plus a set-up word that
stores the limit; `tests/lib/task-job.fs` does this.

**Tasks.** `task-start ( context xt -- task ior )` runs `xt ( -- )` in a new
task with that context selected; `task-wait ( task -- ior )` waits and gives
xt's `THROW` code (0 when it returned normally). A task's word reaches
mutable state only through its own context. The adapter chooses one of
three hosts when it loads:

| Host | Gforth | How tasks run |
| --- | --- | --- |
| threads | 1.0 (`newtask4`, `initiate`, `send-event`) | POSIX threads on all cores; a mutex guards each job's done flag, and an event wakes the waiting task |
| cooperative | 0.7.3 (`tasker.fs`) | one core; tasks switch only at `task-yield` and `task-wait` |
| serial | any other Forth, or forced by defining `task-serial-only` | `task-start` runs the word at once |

**Limits.**

- Nothing may `ALLOT`, `CREATE` or compile after tasks start: all tasks share
  one dictionary, and all run-time memory comes from `ALLOCATE`.
- Each task's data and return stacks hold at least `task-data-cells` and
  `task-return-cells` (8,192 cells each), and never less than the main
  task's (Gforth 0.7.3: 2,048 data and 1,920 return cells; Gforth 1.0:
  3,968 to 4,096 cells per stack, from `stacksize4`). The test job's
  recursive pass, 500 frames deep, used
  1,004 return-stack and 1,001 data-stack cells inside each task; checker
  passes were measured at up to about 720 return cells, and nested passes
  may approach 1,500.
- A stack overflow is never an accepted result, but it is not always
  recoverable. In a Gforth 1.0 task it is a `THROW` (-5) that `task-wait`
  reports; in a Gforth 0.7.3 task it crashes the whole program (those
  stacks have no guard pages); in the main task it is an uncaught `THROW`
  unless the caller catches it. So every recursive pass must bound its
  depth well below these stack sizes.
- Each context holds a full copy of every module's stores, so memory grows
  with the number of tasks; this will matter at Mathlib scale (see the
  [scale assessment](../project/SCALE_ASSESSMENT.md)).
- The cooperative and serial hosts run one task at a time: they test that
  contexts do not interfere, not speed.

**Measured speed-up** (Gforth 1.0, this machine: 12 logical cores, WSL2,
2026-11-02; `gforth tests/lib/task-bench.fs`, three runs). Each job is 400
rounds of the test job; times are for running the jobs one after another
in one task against running them as that many tasks.

| Jobs | Serial (ms) | Tasks (ms) | Speed-up |
| --- | --- | --- | --- |
| 1 | 250–277 | 253–257 | 0.97–1.08 |
| 2 | 531–557 | 265–284 | 1.86–2.10 |
| 6 | 1,591–1,700 | 350–370 | 4.54–4.59 |
| 12 | 3,172–3,239 | 545–580 | 5.56–5.87 |

Twelve tasks gain about 5.6–5.9 times, consistent with six physical cores
with two hardware threads each (the ADR's earlier probe measured about 6).

How the existing code should be written and refactored is in
[the Forth style guide](FORTH_STYLE.md).

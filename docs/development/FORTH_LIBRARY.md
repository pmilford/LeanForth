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
| Bounded record stores | `src/lib/store.fs` | `store:` defining word: a fixed number of fixed-width records with an allocation count, a reset generation that saturates to a poisoned state, an identity per record that never repeats, and a sealed shape so header corruption fails closed. `store-size` and `store-init` make the same store in memory obtained at run time (`ALLOCATE`, or a region of a context); `store-plan?` also refuses a size that would not fit in a cell. **Marks** (plan task 1.1.3): `store-mark ( mark store -- outcome )` records the store, its generation, serial and count in a `/store-mark` record the caller provides (fields `mark-store`, `mark-generation`, `mark-serial`, `mark-count`); `store-rollback ( mark store -- outcome )` restores the count, giving back every record allocated since, and never rewinds identities; `store-mark-valid? ( mark store -- flag )` tells whether it would. A rollback is refused, invalid with nothing changed, for a mark of another store, from another generation (a reset since), above the current count, of an invalid or poisoned store, or stale: records below its count must be older than the mark and the one at its count newer, so a mark below which an earlier rollback went and records were allocated again is refused. Marks are not capabilities: a forged record that passes these checks is accepted | New 2026-11-02; used by the term, level and name stores; unit-tested in `tests/lib/lib.fs`, run-time stores in `tests/lib/context.fs`; marks 2026-11-02 in `tests/lib/store-mark.fs` (every refusal, and 20,000 random operations against a model that kills a mark when the count drops below it or the store is reset), used by the checked environment's input (`src/core/input.fs`); the hand-written count saving in the existing modules is not converted yet |
| Tagged nodes | `src/lib/node.fs` | `BEGIN-STRUCTURE` record of tag and two fields, with whole-node `node!`/`node@` and `node-new`/`node-read` on a store | New 2026-11-02; terms and levels |
| Range checks | `src/lib/bounds.fs` | `between?` and `upto?` (inclusive, signed, never wrapping) and `cells-zero?` | New 2026-11-02 |
| Outcome vocabulary | `src/lib/outcome.fs` | ok, invalid, exhausted (out of fuel), unknown, rejected, unsupported and full (out of room: a store, work stack, frame, depth or size limit) (ADR 0008), with `ok?`, `outcome-sane`, `flag>outcome` and `room>outcome` (a validity or room flag as ok, else invalid or full), `visit-outcome` (the one rule for a visit bounded by fuel and room: no fuel is exhausted whatever the room, then no room is full), the continue-on-ok steps `ok-then?`, `ok-keep?` and `ok-keep2?`, and `no-result`, and `outcome-text` (each outcome's name, for reports) | New 2026-11-02; every core and kernel module uses it; the per-module status aliases were removed |
| DAG walks | `src/lib/walk.fs` | `walk:` defining word: fuel, current node, one visitor cell and a bounded work stack in one record; `walk-run` drives a visitor and `walk-visit` reads and dispatches a node. A push without room is full whatever fuel is left (checked where the push happens), and a root that cannot be pushed means a corrupted capacity, which is invalid. `walk-size`/`walk-init` and `walk2-size`/`walk2-init` make the same records at run time. The walk words keep no state of their own; each module's walk records are members of the checker context, one set per context | New 2026-11-02; level scope, Sort representation, session and handle audits use it |
| Bounded recursion | `src/lib/frame.fs` | A frames record: fuel, visits in progress and their limit, the visitor (set once), a context cell (such as a binder depth) and a job cell pointing at the pass's own record. `frames:` defines a standalone record and `frame-init` sets one up inside a larger record. `frame-call` charges one unit of fuel and one frame per visit of a visitor `( x frames -- result outcome )`, `frame-call2` the same for `( x y frames -- outcome )`, `frame-under` visits one context level deeper, `frame-run` starts a pass. `frame-room` says why a visit cannot open: a limit below 1 (a corrupted record) is invalid, then no fuel left is exhausted and no free frame full (`visit-outcome`, so the fuel decides); `frame-under` applies the same before its context, which is full at `max-n`. A busy record refuses a new budget or pass, so a pass cannot be restarted from inside itself; `frame-reset` recovers after a THROW. Values a visitor keeps across a child's visit stay on the data stack, so each nested visit holds host stack cells: measured 2 to 6 return-stack and 3 to 4 data-stack cells per frame, and 701 and 494 cells at the deepest nesting found for a 64-node store (124 frames of beta, instantiate and shift), the same on Gforth 0.7.3 and 1.0. `mixed-beta.fs` checks at load time that the host's stacks hold three times `lf-term-capacity` frames | New 2026-11-02; the kernel's shift, instantiate and beta passes use it; unit tests and a randomized model test |
| Checker contexts | `src/lib/context.fs` | One `ALLOCATE`d record per worker for all of a check's mutable state ([ADR 0009](../adr/0009-reentrant-state-and-parallel-checking.md)), reached through the `USER` variable `lf-context` (a plain variable on hosts without Gforth's `USER`). Modules declare members while they load: `context-record:`, `context-store:`, `context-walk:`, `context-walk2:`, `context-frames:` (a frames record, set up with `frame-init`), and `context-setup` for set-up words; a refused declaration changes nothing. Each member's name is a colon definition that adds its offset, a literal, to `lf-context @`. Modules also state how deep their checks nest on the host stacks (`context-need`), which the job pool checks. `context-new`, `context-use` and `context-free` make, select and free contexts. Each context is idle or owned by one job; each task has an owner token `lf-owner` and may select only contexts it owns (the main task: idle ones); owned contexts cannot be freed. `context-in-job?` says whether the current task runs a job or a check; the checked environment's serial driver gives a check the token `context-check-owner`, so every in-job guard refuses it too. `call-balanced ( x xt -- )` runs a word above a cell and throws `context-unbalanced` (-4096) when the word changed the stack depth or that cell (the checked environment's serial driver uses it; `task.fs`'s `job-call` still has its own copy) | New 2026-11-02; ownership, frames members and atomic declarations 2026-11-02 after an independent review; every module of `src/core/` and `src/kernel/` keeps its state in it since 2026-11-02 (see the design below); tested in `tests/lib/context.fs`, including a randomized model with context switches at every step, and with real checker work in `tests/core/contexts.fs` |
| Job pool | `src/lib/task.fs` | `job-submit ( context xt -- job ior )` and `job-wait ( job -- ior )`: a fixed pool of long-lived workers (at most one per logical core, setting `task-workers`) fed from a bounded queue; POSIX threads with a mutex and two condition variables on Gforth 1.0, the cooperative `tasker.fs` on Gforth 0.7.3, and a serial path elsewhere (or when forced, for tests). A job's context is owned by the job until it is waited for. Wrong stack effects give `task-unbalanced`; stack overflows never report success (guard pages on 1.0, canary zones on 0.7.3); a worker that cannot be created is reported (`task-no-worker`). `job-stacks-cover?` tells whether the workers' stacks hold a recursion requirement, and the pool refuses to start with stack settings below the largest need modules stated (`task-stacks-small`). On Gforth 1.0 each worker owns its exception-backtrace and error-stack strings (a new task copies the creator's user area, and shared strings were corrupted by concurrent THROWs). Job rules: never parse or use `PAD` (one buffer for all tasks on Gforth 1.0), use `<# #>` text before the job yields (one buffer on 0.7.3), and restore `BASE` if a job changes it (a worker starts with the main task's). Not loaded by `src/main.fs`; the scheduler will load it | New 2026-11-02; pool replaced one thread per task the same day; `tests/lib/task.fs` and `task-serial.fs` compare jobs and interleaved contexts with serial runs for 1, 2 and all workers and reach every refusal; `task-overflow.fs` and `task-overflow-serial.fs` overflow both stacks inside jobs; `tests/lib/task-bench.fs` measures speed-up |
| Line reader and UTF-8 | `src/lib/bytes.fs` | `reader:` record over a Forth-2012 file: whole lines in one heap buffer that grows for long lines up to a limit, strict framing (final line feed; `text-framed` refuses carriage returns and a byte-order mark), line numbers and double-cell file offsets; `utf8-length`, `utf8-valid?` and `utf8-put` (RFC 3629, no overlongs or surrogates); `counted,`; `heap-claim` and `heap-release` for owned heap buffers; `fnv-step` and `bytes-mix` (an FNV-style mix of bytes into a hash, used by the checked environment's input fingerprint). Uses Gforth's native `scan` behind an adapter, with a portable loop otherwise. Loads in decimal whatever `BASE` is, and restores it | New 2026-11-02; unit-tested against an independent UTF-8 model in `tests/lib/bytes.fs`, which loads it under `HEX` and counts heap blocks to show that a second `reader-init` frees the first buffer |
| JSON reader | `src/lib/json.fs` | `json:` view record: a fail-closed, non-recursive RFC 8259 parser of one text into a growable token tape (containers know their item count and extent), escapes decoded in place, numbers kept as digit text, limits on depth, tokens, string and number length; `json-find`, `json-next`, `json-natural`, `json-u`, `digits>u` and `decimal>u` (decimal, independent of `BASE`); kind-checked `json-items-of` and `json-kind-at`. Loads in decimal whatever `BASE` is, and restores it | New 2026-11-02; malformed corpus and every limit tested in `tests/lib/json.fs`, loaded under `HEX` |
| JSON writer | `src/lib/json-write.fs` | Plan task 3.1.3. A writer record (`json-writer: ( depth room "name" -- )`, or `jw-size` and `jw-init` in memory the caller owns, such as a context member) writes one JSON text to the caller's sink xt `( c-addr u -- )`: `jw-start ( sink writer -- )`, then `jw-string`, `jw-n` (signed cell), `jw-u` (unsigned cell), `jw-digits` (integer text of any size, as `json.fs` keeps it), `jw-bool`, `jw-null`, `jw-open-object`, `jw-key`, `jw-close-object`, `jw-open-array`, `jw-close-array`, or `jw-copy ( index view writer -- )` of a value `json.fs` parsed; `jw-end ( writer -- outcome )`. Every call takes the writer last and returns nothing. Deterministic bytes: no whitespace; members in call order, and with `jw-sorted` set each object's keys must strictly increase in byte order (code point order), checked against the last key kept in a key pool of `room` bytes; integers in decimal whatever `BASE` is, `-0` written `0`; strings escaped only as `\"`, `\\`, `\b \f \n \r \t` and `\u00xx` (lowercase) for other bytes below 32, everything else, valid UTF-8 included, as itself, which are the bytes of Python's `json.dumps(v, separators=(",", ":"), ensure_ascii=False)`; no real numbers (`jw-copy` of one is unsupported). The first failing call writes nothing and its outcome sticks until the next `jw-start` (`jw-outcome` reads it): invalid for calls out of order (a close that does not match its open or follows a key, a value where a key is due, a second value, `jw-end` before the value is complete, writes before `jw-start` or after `jw-end`), invalid UTF-8, bad integer text or flags, keys out of order in sorted mode, and any call from inside the writer's own sink (`jw-reset` or `jw-init` there fails the text when the sink returns); full past the byte limit `jw-limit` (so a buffer of n bytes never overflows), the depth or the key pool. So `jw-end` gives ok only for exactly one complete JSON value, and the sink only ever receives a prefix of one. After a THROW out of a writer word the caller discards the text and calls `jw-reset` (a THROW outside the sink leaves no mark); a sink that writes over the string or view being written is unchecked. No state of its own; `jw-copy` is a loop over the value's tokens, without recursion (a container it opens records the index of the token after it, and closes there), so a few stack cells serve any depth the writer allows. Loads in decimal whatever `BASE` is, and restores it | New 2026-11-02; `tests/lib/json-write.fs` (180 assertions: every word's positive and negative cases, every limit at and one past its bound, sorted keys, keys refused as strings are, the sink rules including `jw-reset` and `jw-init` from inside the sink, a copy 10,000 containers deep and copies stopped by a failed close, two interleaved writers and a context member, 2,000 random strings and 2,000 random cells written and read back by `json.fs`, and all 138 lines of `tests/reference/*.ndjson` plus 16 lines with every other record kind of lean4export 3.1.0, `tests/lib/json-write-corpus.ndjson`, copied back byte for byte in both key modes), loaded and partly run under `HEX`; `tests/lib/test_json_write.py` compares 300 random values written with the writer's words and 150 non-canonical texts copied with `jw-copy` against Python's `json.dumps`, 40 copies of values nested up to 64 deep, plus 50 refusals with their exact prefixes; 21 planted faults each caught, and after the independent review (2026-11-02) 6 more, one per fix reverted or broken, on Gforth 0.7.3 and 1.0 |
| Packed 32-bit fields | `src/lib/u32.fs` | `u32@ ( addr -- u )` and `u32! ( u addr -- )` read and write an unsigned 32-bit field; `u32s ( n -- au )` sizes *n* fields; `u32-mask` is the 32-bit mask on any cell size. Gforth's `l@`/`l!` where the host has them and a load-time check (`u32-sound?`) shows they are unsigned 32-bit access: a value with bit 31 set comes back unchanged, and the four characters after the field keep their values; otherwise, or when `lf-u32-portable` is defined first, the Forth-2012 `u32-bytes@`/`u32-bytes!` (four characters, least significant first, an order the module fixes; public for the tests only). `u32!` keeps the low 32 bits; on a 32-bit host a value of 2³¹ or more reads back as a negative cell, so compare with `U<`. Loads in decimal whatever `BASE` is, and restores it. The layout of packed records is defined by arithmetic on the values, never by byte order, and is never written to a file. The only non-text module allowed byte access (`scripts/check-portable-forth.py`) | New 2026-11-02 for the compact store ([ADR 0016](../adr/0016-compact-store.md), proposed); not yet loaded by `lib.fs` or used by a module; both versions tested on every host in `tests/lib/lib.fs`, which loads it under `HEX` and asserts that Gforth's words are in use, shows the check refusing a sign-extending fetch and a cell-wide store, and loads it again under `BASE` 8 with `lf-u32-portable` defined to get the Forth-2012 version; after the independent review (2026-11-02) 6 planted faults each caught |
| Big natural numbers | `src/lib/bignum.fs` | Arbitrary-precision naturals for Lean's `Nat` literals ([below](#big-natural-numbers)): numbers in an arena the caller provides (`/big-arena`, `big-arena-init`; `big-mark` and `big-release` give back what was made since a mark), one-cell limbs whose width is counted (`limb-bits`), decimal reading and printing (`decimal>big`, `big>decimal`), conversion to and from a cell (`u>big`, `big>u`), comparison (`big-compare`, `big=`, `big<=`), and the operations Lean 4.35.0's kernel computes on literals (`big+ big- big* big/ big-mod big-gcd big-and big-or big-xor big-lshift big-rshift big-pow`, each `( a b arena -- c outcome )`). Schoolbook multiplication with Karatsuba from 48 limbs, Knuth's algorithm D, Lehmer's gcd. Outcomes ok, invalid (a malformed or released number, text or arena) and full (no room, or more bits than the arena's limit, by default Lean's 2^30). No state; loads in decimal whatever `BASE` is | New 2026-11-02 (plan task 5.2.3, library part); not yet used by the kernel (task 5.1.4); `tests/lib/bignum.fs` reaches every outcome; `make test` compares 37,585 cases with Python's integers on the running Gforth and catches 22 planted faults; review fixes of 2026-11-03 (printing overwrote the number below its text, stale operands, two speed fixes) with guarded-arena sweeps; `make check` has 984 of them computed by pinned Lean's kernel |
| Portability adapter | `src/lib/portability.fs` | Forth-2012 definitions of `>=`, `<=`, `0<=`, `0>=`, `-rot`, `max-n`, `cell` and the structure words, compiled only where the host lacks them. `scripts/check-portable-forth.py` refuses a module under `src/` that uses one of them without loading this file, directly or through the files it loads | New 2026-11-02; defines nothing under Gforth except `max-n`; `cell` and the load check added 2026-11-02 |
| Diagnostics | `src/core/diagnostics.fs` | One record per checker context explaining the first failure of a check: a reason code, the site (module and word, a counted string) and two numbers; first failure wins until `lf-diag-clear`; `lf-diag@`, `lf-diag.`; helpers `lf-diag-walk`, `lf-diag-frames` and `lf-diag-store` explain a walk's, a pass's or a store's failure. Never changes an outcome; catalogue in [DIAGNOSTICS.md](../programming/DIAGNOSTICS.md) | New 2026-11-02 (plan 6.7, first form); every core and kernel module records its full and exhausted sites; `tests/core/diagnostics.fs` |
| Expression store | `src/core/terms.fs` | Index-based nodes for sorts, bound variables, application, λ, Π and constants; nodes refer to earlier indices, so a term is a DAG with sharing | 64 nodes per checker context; built on `context-store:`; constructors check ranges only |
| Universe-level store | `src/core/levels.fs` | Level DAGs: zero, succ, max, imax, parameters | 64 levels per checker context; built on `context-store:` |
| Name interning | `src/core/names.fs` | Lean structured names (string and numeric components) stored once and referred to by index | 64 names, 2,048 bytes; built on `store:` with named entry fields; lookup is a linear scan, no hashing |
| Stale-handle detection | `src/core/generation-handles.fs`, `symbolic-session.fs` | Handles carry a generation number so a handle from before a reset is rejected | Works; tests found one unguarded path |
| Constant references | `src/core/constant-references.fs`, `constant-term-*.fs` | A constant's name plus universe arguments, with syntax and scope audits | 32 references per checker context |
| DAG walkers | `mixed-shift`, `mixed-instantiate`, `mixed-beta`, `mixed-compare`/`mixed-convert`, `mixed-infer` in `src/kernel/` | Bounded traversals with explicit work stacks and fuel, rolling back on failure | Current; the earlier plain and `tagged-` variants were retired 2026-11-02 (roadmap Q9) |
| Level algorithms | `level-scope`, `level-value`, `level-compare`, `level-substitute`, `mixed-level-substitute` | Scope checks, evaluation, conservative equality and simultaneous substitution of levels | Current |
| Signature index | `mixed-signature-probe.fs`, `mixed-signature-audit.fs` | Candidate signatures of constants, specialised to universe arguments | 32 entries; unchecked assumptions |
| Record staging | `src/import/load.fs` | Copies already-decoded expression records into the term store | Not a parser; stages concrete Sorts, which no current checker pass accepts; kept with its round-trip tests until the Forth NDJSON reader replaces it |
| NDJSON export reader | `src/import/ndjson.fs`, `ndjson-count.fs` | Decodes every record kind of lean4export format 3.1.0 into decoded-record layouts and hands each to a handler per kind; checks exact field sets, dense indices and earlier references; a counting tool | New 2026-11-02; untrusted, fail-closed; equal to Python on all of Mathlib; see [NDJSON_READER.md](NDJSON_READER.md) |
| Presentation side table | `src/present/binder-table.fs` | Binder names and kinds, source record IDs and declared constant types, keyed by term index and stamped with the term's identity and the name store's generation, so a reset makes entries read as absent; never read by the checker | New 2026-11-02; one context record; 64 term entries, 32 declarations; `tests/present/term-printer.fs` |
| Term printer | `src/present/term-printer.fs` and `print-job.fs`, `print-names.fs`, `print-tokens.fs`, `latex-text.fs`, `print-levels.fs`, `print-analysis.fs` | Prints terms, levels and names to a caller's sink xt in Lean's notation, ASCII or LaTeX (and Markdown math): capture-free binder names, ∀/→ and binder grouping, hidden implicit arguments and minimal parentheses as Lean's delaborator; fuel, a nested-visit limit (one `frames` record for all recursion) and a name pool, all failing as exhausted | New 2026-11-02; agrees with Lean on 49 cases and the five pinned fixtures (`make test-printer-differential`); [user guide](../user/TERM_PRINTER.md) |
| Program examples | `src/program/clamp.fs`, `examples.fs` | Six executable words (clamp, checked add, abs, factorial, gcd, in-range) | Runtime tested against Lean models, not verified |
| Depth analyzer | `src/program/program-depth.fs` | Stack-depth diagnostic for a tiny opcode list | Not connected to real Forth words |
| Test support | `tests/support/tester.fs`, `checks.fs`, `term-cases.fs`, `composition.fs`, `heap-watch.fs` | Adapter for Gforth's bundled tester that fails the run on the first error; shared checks and fixtures; `ALLOCATE` and `FREE` that count the heap blocks held, in a word list of their own, for tests that show a module frees what it allocates | Test-only |

## Reusability: the libraries as standalone Forth code

**Rule** (owner, 2026-11-03; `AGENTS.md`): general-purpose libraries are
written so that other Forth programs can use them, not coupled to
LeanForth, unless coupling gains a lot. Audit of `src/lib/` on 2026-11-03:

| Library | General purpose? | What ties it to LeanForth today |
| --- | --- | --- |
| `bignum.fs` (natural numbers) | yes; no Lean code (Lean only in comments) | needs `outcome.fs`, `bounds.fs`, `portability.fs` (104 lines); naturals only (subtraction stops at 0, as Lean's `Nat`); all helper names public. Shown working from an unrelated folder on both Gforths |
| `json.fs` (RFC 8259 reader), `json-write.fs` | yes | `json.fs` requires `bytes.fs`, which requires the whole `lib.fs` (contexts, walk records, frames) although it uses little of it; helper names public |
| `bytes.fs` (bounded line reader, UTF-8) | yes, with strict framing rules chosen for Lean's exports (no carriage return, no byte-order mark, final line feed) | requires all of `lib.fs`; the framing rules should become options |
| `u32.fs` (32-bit access) | yes | none beyond `portability.fs` |
| `store.fs`, `node.fs`, `walk.fs`, `frame.fs` (bounded stores, records, explicit-stack walks) | yes | the shared outcome vocabulary |
| `context.fs`, `task.fs` (per-task contexts, job pool) | partly: a general job pool and context mechanism, designed around the checker's per-check state | the checker's context model (ADR 0009) |
| `outcome.fs` (ok, invalid, exhausted, unknown, rejected, unsupported, full) | LeanForth's shared result vocabulary | deliberately shared: one vocabulary for every module |
| coming: `sha256.fs`, the compact store (ADR 0016) | written to this rule from the start | — |

**Why they are not yet packaged as standalone libraries.** They were built
just in time for the checker, with correctness and fail-closed behaviour
first; their headers already say "a general tool with no Lean knowledge",
but nothing required minimal `require` lines, private helper names, a
standalone example or tests runnable outside the project. Plan task 1.1.8
does that, together with ADR 0010's word lists for the library.

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

Forth also writes JSON, deterministically (`src/lib/json-write.fs`, plan
task 3.1.3; see the table above), for receipts, the derivation log, the API
and the round trip of decoded export records (plan 3.2.4, 3.4.3 and 3.5).
A writer record goes with each text in progress; the output goes to the
caller's sink, here `TYPE`:

```forth
require src/lib/json-write.fs
8 256 json-writer: receipt    \ containers nested 8 deep, 256 bytes for sorted keys
true receipt jw-sorted !      \ each object's keys must increase: canonical text
: write-receipt ( -- outcome )
  ['] type receipt jw-start
  receipt jw-open-object
    s" checked" receipt jw-key  42 receipt jw-u
    s" name" receipt jw-key  s\" Nat.add_comm \xe2\x9c\x93\n" receipt jw-string
    s" ok" receipt jw-key  true receipt jw-bool
  receipt jw-close-object
  receipt jw-end ;
write-receipt .
```

prints `{"checked":42,"name":"Nat.add_comm ✓\n","ok":true}` and then `0`
(ok). Writing the keys in another order, closing with `jw-close-array`,
or passing invalid UTF-8 would print only the part written before that
call and give 1 (invalid); a 40-byte `jw-limit` would give 6 (full) before
the string. A caller that keeps the text checks the outcome and discards
the text unless it is ok. `jw-copy ( index view writer -- )` writes a
value parsed by `json.fs` the same way; every line of the reference
exports, whose keys are already in increasing order, comes back byte for
byte.

## Big natural numbers

`src/lib/bignum.fs` (plan section 6.8 and task 5.2.3, library part,
2026-11-02). The owner chose our own Forth code over GMP (OQ-6), *"but it
should be able to be very fast too"*. It is untrusted until the review
gate in `AGENTS.md`; once the checker's verdicts depend on it, it is
trusted code. The kernel does not use it yet: that is the literals ADR
(task 5.1.4) and its integration.

**What Lean computes.** Lean 4.35.0's kernel computes these operations on
`Nat` literals (`src/kernel/type_checker.cpp` at tag `v4.35.0`,
`reduce_nat`, lines 672–703, called from `whnf`, line 732, and from
`lazy_delta_reduction`, lines 1060–1065, when neither side has free
variables). Each argument is first put in weak head normal form and must
then be a literal or `Nat.zero` (`is_nat_lit_ext`, 607–612). The results
are those of Lean's runtime: `include/lean/lean.h` of the pinned toolchain
(lines 1665–1676, 1694–1705, 1721–1732, 1813–1822) and
`src/runtime/object.cpp` (1427–1441, 1457–1470, 1488–1505, 1573–1627,
1643–1655).

| Lean | Word | Result | Lean refuses (kernel exception) |
| --- | --- | --- | --- |
| `Nat.succ n` | `big+` with 1 | n + 1 | a result over the size limit (681) |
| `Nat.add` | `big+` | a + b | a result over the limit (622–626) |
| `Nat.sub` | `big-` | a − b, or 0 when b > a | a result over the limit (never happens) |
| `Nat.mul` | `big*` | a · b | a result over the limit |
| `Nat.div` | `big/` | ⌊a / b⌋; a / 0 = 0 | never |
| `Nat.mod` | `big-mod` | a mod b; a mod 0 = a | never |
| `Nat.gcd` | `big-gcd` | gcd(a, b); gcd(a, 0) = a | never |
| `Nat.beq` | `big=` | `Bool.true` when a = b, else `Bool.false` | never |
| `Nat.ble` | `big<=` | `Bool.true` when a ≤ b, else `Bool.false` | never |
| `Nat.land`, `Nat.lor`, `Nat.xor` | `big-and`, `big-or`, `big-xor` | bitwise and, or, exclusive or | never |
| `Nat.shiftLeft` | `big-lshift` | a · 2^b; 0 when a = 0, whatever b | a ≠ 0 and b > 2^32 − 1; or size(a) + b/8 + 1 bytes over the limit, an estimate (647–660) |
| `Nat.shiftRight` | `big-rshift` | ⌊a / 2^b⌋, so 0 for every b too large | never |
| `Nat.pow` | `big-pow` | a^b; a^0 = 1, so 0^0 = 1 | b > 2^32 − 1, even when a is 0 or 1 (`get_count_arg`, 305–313, checked first at 637); a > 1, b ≠ 0 and size(a) > limit / b, an estimate (640) |

`Nat.log2` is *not* computed by the 4.35.0 kernel: the runtime's
`lean_nat_log2` (`object.cpp` 1657–1669) is never called from
`type_checker.cpp`. `big-bits` gives the bit length it would need. The
size Lean measures is `lean_nat_size_in_bytes` (`object.cpp` 1671–1675,
`mpz.cpp` 232–234): 8 bytes for a value below 2^63, otherwise 8 bytes per
64-bit limb. The limit is 128 MiB (`type_checker.cpp` line 36), changed
by the environment variable `LEAN_NAT_MAX_SIZE` (1266–1280); with the
default a numeral passes exactly when it has at most 2^30 bits. Every
literal is checked when its type is inferred (`infer_lit`, 315–321).

**The library's own limit.** An arena has a limit in bits, by default
`big-lean-bits` (2^30); `big-limit!` sets another, at most 2^(cell bits − 2).
A result with more bits is *full*; so is any result when the arena has no
room. Each of Lean's checks admits only results of at most 2^30 bits, so
at the default the library never refuses what Lean computes, given room.
The limit is not Lean's rule, though: the estimates and the 2^32 − 1 caps
in the table refuse some results the library computes (such as
3^(2^24 + 1), or 0^(2^40)); the kernel integration must apply Lean's
rules itself before calling the library (below).

**Design.** A number is the address of a cell holding its limb count and
then the limbs, least significant first; a limb is one cell read as
unsigned, and `limb-bits` is counted when the file loads, so no result
depends on the cell size (only 64-bit hosts have been run). Numbers are
normalized (no zero top limb; 0 has no limbs) and never change once made.
Every operation makes its result at the arena's top, its scratch above
the result, and gives the scratch back; a failure leaves the top where it
was and gives -1 with the outcome (`big>decimal` gives 0 0, an empty
text). Inputs are checked in O(1): the count is at least 0, the top limb
is not 0, and the number does not reach into the arena's free part
(`big-live?`: a released number, which the result would overwrite, is
*invalid*; one whose memory was claimed again cannot be told from a live
one); the arena record is checked too. Comparisons and `big-bits` trust
their arguments. Limb arithmetic uses Forth-2012's
`UM*`, `UM/MOD`, `D+`, `D-` and `DU<`. Multiplication is by rows below 48
limbs and by Karatsuba above, the longer factor cut into chunks of the
shorter one's size; a shorter last chunk (the tail) is never padded: it
goes by rows below 48 limbs, and otherwise the job turns round, the
shorter factor cut into chunks of the tail's size, so the sizes shrink as
in Euclid's algorithm with no more room. Division is Knuth's algorithm D
(TAOCP 4.3.1); gcd is Lehmer's algorithm with single-limb leading parts
of `limb-bits − 3` bits (Knuth's algorithm L, 4.5.2), with a full
division when no simulated step agrees; powers are left to right over the
exponent's bits, recursively, and a product that cannot fit the limit
(at least bits(a) + bits(b) − 1 bits) is refused before it is made;
decimal text goes in chunks of the largest power of ten that fits a limb
(10^19 on 64-bit cells), each written whole, so the text's room is
bits / 3 + `chunk-digits` characters. The module defines no state;
`limb-bits`, `chunk-base` and `chunk-digits` are constants computed while
loading. Karatsuba's step claims cannot fail after the room check; one
that did would be a fault in the module, which stops the run with
`ABORT"` rather than write past the arena (ADR 0018, proposed, would make
it its `throw-fault`).

**Tests.**

- `tests/lib/bignum.fs` (loaded under `HEX`): limb geometry, arenas and
  marks (refused marks change nothing), conversions, every operation's
  edges (0, 1, limb boundaries, max-u ± 1, equal operands, subtraction
  below 0, division by 0, huge shifts and exponents), and every failure:
  malformed numbers, text and arenas, and released (stale) operands,
  wholly or in part (invalid), the bit limit and a 64-cell arena (full),
  each leaving the arena's top unchanged. Every number printed is read
  again afterwards. A power over the limit (3^4095 at 4,096 bits) writes
  no higher above the top than the valid 3^2047, so its last product is
  refused, not made. Guarded arenas: an arena of every size from 0 cells
  up, between guard cells, runs all twelve operations on three pairs of
  operands, products of 100 by 47, 160 by 100 and 233 by 144 limbs, and
  printing, of a number outside the arena and of the arena's own newest
  number: each result is right or *full* with nothing made, no guard
  cell changes, the printed number is unchanged, and a product works
  from exactly the room it needs (the result, a frame or the job with T,
  and the Karatsuba scratch).
- `tests/lib/bignum_differential.py` (`make test`): 13,585 edge cases
  (special values, limb boundaries of 32- and 64-bit limbs, very unequal
  sizes, Knuth D's rare add-back and qhat = B − 1 cases, Fibonacci
  neighbours for gcd, Karatsuba sizes 47 to 1,049 limbs with all-ones
  limbs, including short tails by rows and long tails that turn the job
  round once or twice, results on both sides of limits from 0 to 256
  bits) and 24,000 random cases from a fixed seed, up to 10,000 digits,
  run by `tests/lib/bignum-cases.fs`: every printed result equals
  Python's, and every number printed is compared afterwards with a copy
  made before. Extra runs with other seeds (60,000 random cases each,
  `gforth` and `gforth-fast`) also agreed. Then 22 faults planted in a
  copy of the module (a lost carry, a carry of 1 to start, ignored
  borrows, a dropped high product limb, four Karatsuba faults, a skipped
  add-back, a wrong qhat when u2 = v1, an unscaled remainder, two Lehmer
  faults, a short decimal chunk, too little room for the text, two shift
  faults, a lost factor in powers, incomplete normalization, an
  off-by-one limit, a comparison of the top limb only): each changes a
  result among the edge cases, on Gforth 1.0 and 0.7.3. A run is stopped
  at its first wrong line, because a broken library may then loop.
- `make check` gives 984 of the cases (all 14 operations, 12 of more than
  3,000 digits) to pinned Lean as `example : Nat.op A B = R := by decide
  +kernel`, so that Lean's kernel itself computes the operation (no
  axioms): all are accepted, and every one of them with R changed is
  rejected.

**Speed** (`python3 tests/lib/bignum_bench.py`, 2026-11-02, this machine
shared with other work, Python 3.13.2; nanoseconds per operation, Forth
over Python; division and remainder take a 2n-digit dividend, the power
is 3^e with an n-digit result). Python's integers are C with 30-bit
digits and Karatsuba; the two sides are timed differently, so the ratios
are approximate.

| Operation | Digits | Python (ns) | `gforth` (ns) | ratio | `gforth-fast` (ns) | ratio |
| --- | --- | --- | --- | --- | --- | --- |
| add | 10 / 100 / 1,000 / 10,000 | 30 / 31 / 75 / 553 | 212 / 260 / 614 / 3,943 | 7.0 / 8.3 / 8.2 / 7.1 | 68 / 91 / 203 / 1,166 | 2.3 / 2.9 / 2.7 / 2.1 |
| multiply | same | 37 / 119 / 4,665 / 214,157 | 452 / 830 / 19,893 / 915,128 | 12 / 7.0 / 4.3 / 4.3 | 132 / 239 / 6,484 / 280,620 | 3.6 / 2.0 / 1.4 / 1.3 |
| divide | same | 58 / 233 / 10,311 / 469,512 | 223 / 1,092 / 27,253 / 2,195,492 | 3.8 / 4.7 / 2.6 / 4.7 | 68 / 392 / 8,217 / 615,820 | 1.2 / 1.7 / 0.8 / 1.3 |
| remainder | same | 53 / 231 / 10,354 / 962,732 | 223 / 1,138 / 25,776 / 2,231,960 | 4.2 / 4.9 / 2.5 / 2.3 | 67 / 451 / 8,578 / 607,634 | 1.3 / 1.9 / 0.8 / 0.6 |
| gcd | same | 101 / 708 / 15,728 / 1,019,446 | 431 / 15,670 / 271,403 / 9,612,000 | 4.3 / 22 / 17 / 9.4 | 134 / 4,996 / 87,479 / 3,392,546 | 1.3 / 7.1 / 5.6 / 3.3 |
| power | same | 66 / 157 / 1,269 / 65,722 | 1,801 / 3,114 / 11,170 / 441,833 | 27 / 20 / 8.8 / 6.7 | 583 / 1,000 / 3,744 / 130,286 | 8.9 / 6.4 / 2.9 / 2.0 |
| read decimal | same | 43 / 163 / 3,570 / 195,132 | 356 / 1,616 / 20,075 / 867,988 | 8.3 / 9.9 / 5.6 / 4.4 | 92 / 378 / 4,477 / 226,079 | 2.1 / 2.3 / 1.3 / 1.2 |
| print decimal | same | 48 / 179 / 8,209 / 439,806 | 512 / 1,440 / 14,675 / 744,154 | 11 / 8.1 / 1.8 / 1.7 | 149 / 468 / 7,594 / 526,560 | 3.1 / 2.6 / 0.9 / 1.2 |

With `gforth-fast` most operations are within 1–3 times Python; gcd (3–7
times above 100 digits) and small powers (6–9 times) are the slowest.
Karatsuba was measured against rows alone for thresholds of 16 to 96
limbs: it breaks even near 64 limbs and pays above; with the chosen 48
limbs a 520-limb (10,000-digit) product takes 268 instead of 668 µs
(`gforth-fast`) and 981 instead of 1,877 µs (`gforth`).

Review fixes of 2026-11-03, timed before and after on this machine, one
run at a time (best of three powers, of five batches of ten products):

| Case | `gforth-fast` before → after | `gforth` before → after |
| --- | --- | --- |
| 3^(2^22 − 1) at a 2^22-bit limit: *full* | 625 → 200 ms | 2,007 → 661 ms |
| 3^(2^21 − 1) at that limit, valid (for scale) | 201 → 197 ms | 637 → 663 ms |
| product of 1,000 by 1,000 limbs (for scale) | 737 → 733 µs | 2,398 → 2,375 µs |
| 1,049 by 1,000 limbs (a tail of 49) | 1,503 → 839 µs | 4,771 → 2,725 µs |
| 1,500 by 1,000 limbs (a tail of 500) | 1,474 → 1,217 µs | 4,869 → 3,939 µs |
| 1,999 by 1,000 limbs (a tail of 999) | 1,475 → 1,473 µs | 4,889 → 4,818 µs |
| 233 by 144 limbs (tails of 89, 55, 34) | 63 → 57 µs | 213 → 189 µs |

A refused power used to make its last, doomed product; a short tail was
padded to a whole chunk. A Karatsuba product also needs fewer cells now:
no padded copy of the tail.

**Follow-ups for the kernel integration (task 5.1.4).**

- Apply Lean's refusals before calling the library: the 2^32 − 1 caps on
  `Nat.pow` exponents (whatever the base) and on `Nat.shiftLeft` shifts of
  a nonzero value, and the two size estimates, with Lean's host-specific
  measure (8 bytes per 64-bit limb, at least 8), from `big-bits`. Decide
  how a refusal is reported (it is a kernel exception in Lean, so the
  declaration is not accepted) and how `LEAN_NAT_MAX_SIZE` is treated.
- Literal terms: the term store holds cells; a literal needs a handle into
  an arena that lives as long as the terms (the shared, read-only input of
  ADR 0012 E1, plan task 7.2.1), and number handles are addresses, valid
  only while that memory does not move.
- `Nat.succ` and `Nat.zero` as literals, and `is_def_eq_offset`'s
  predecessor of a literal (`type_checker.cpp` 1025–1052), compose from
  `big+` and `big-` with 1.
- Speed for Mathlib: profile real literal workloads before tuning further
  (double-limb Lehmer steps for gcd; fewer claims for small powers).

## Missing for a usable checker at Mathlib scale

- **Capacity and memory.** Every store holds 64 entries in fixed arrays,
  one copy per checker context. Mathlib's export has millions of expression nodes. Needed: growable
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
- **Re-entrancy.** Done for `src/core/` and `src/kernel/` (2026-11-02):
  their state lives in the per-task checker context, so checks run in
  several contexts at once (below). Still global: `src/import/`,
  `src/program/`, the line and JSON readers, and the term, level and name
  stores are per context rather than a shared, read-only input (ADR 0012
  E1 needs that split later). The scheduler is still to be written
  (roadmap C1–C4, ADR 0009).
- **Serialization.** The JSON writer (`src/lib/json-write.fs`, 2026-11-02)
  gives deterministic, architecture-independent bytes; the formats for
  checked terms and receipts built on it are still to be defined.
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
of workers). Every module of `src/core/` and `src/kernel/` moved its state
into the context the same day (ADR 0009 step 3; see *Converted modules*
below). Untrusted, like the rest of the library.

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

| Before | In a context |
| --- | --- |
| `lf-term-capacity walk2: lf-cts-walker` | `lf-term-capacity context-walk2: lf-cts-walker` |
| `lf-level-capacity walk: lf-lsubst-walker` | `lf-level-capacity context-walk: lf-lsubst-walker` |
| `lf-term-capacity /node 0 store: lf-terms` | `lf-term-capacity /node 0 context-store: lf-terms` |
| `create lf-lsubst-job /lf-lsrec allot` and `lf-lsubst-job /lf-lsrec erase` | `/lf-lsrec context-record: lf-lsubst-job` (members start zeroed) |
| a frames record set up with `frame-init` after its visitor, such as `lf-term-capacity ' lf-mbeta-visit lf-mbeta-frames frame-init` | `lf-term-capacity ' lf-mbeta-visit context-frames: lf-mbeta-frames` (declared after the visitor, which reaches the record through its frames argument) |
| load-time set-up such as `lf-level-reset` at the end of `levels.fs` | `' lf-level-reset context-setup` (runs now in the main context and in every new one) |

Rules for converted modules:

- Declare every member, and state every stack need (`context-need`),
  before the first `context-new`, `job-submit` or `pool-start`; each seals
  the layout, and a later declaration aborts.
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
- A pass record that embeds its frames record puts the frames first, so
  the visitor finds the pass's own fields at the frames address it is given
  (`mixed-shift.fs` and `mixed-instantiate.fs` check this at load time);
  the frames' job cell is not used for it, because a pointer stored there
  would go stale when the main context moves.
- An address of a member may be passed down a call and kept in a member
  for the length of one call (for example a caller array in a request
  record), never across calls.

**Converted modules.** All modules of `src/core/` and `src/kernel/` keep
the state a check writes in the context (2026-11-02): stores, walk
records, the beta frames record and module records (among them the
diagnostic record, `core/diagnostics.fs`, the checked environment's input,
`core/input.fs`, and its candidate, `kernel/environment.fs`), with set-up
words for the level and name stores, the parameter context, the
assignment table and the shift and instantiate frames. So do, outside
them, the loader's batch record (`import/load.fs`, since the term store it
rolls back is per context), the NDJSON counter's tally
(`import/ndjson-count.fs`; its export record owns heap buffers, which a
member may not, so it stays shared and one count runs at a time), the
term printer's records (`present/`) and the program reader and
interpreter (`program/ir-reader.fs`, `ir-run.fs`). What stays shared is
read-only once loading ends — constants, tables filled while loading (such
as the diagnostic catalogue), the deferred words set once while loading
(`lf-lvalue-walk`, `lf-lcmp-walk`, `lf-minfer-walk`) and the site names —
except the checked environment's registry (`lf-envs`; environments are on the heap), which
only the task driving the checks writes, outside jobs. Each context holds
104,296 bytes on a 64-bit host (`context-bytes` after `src/main.fs` loads,
Gforth 0.7.3 and 1.0 alike; measured 2026-11-02, once the program reader
and interpreter had joined). Every context's stores are its own, so the
term, level and name stores are *not* yet the shared, read-only input that
ADR 0012 (E1) describes; splitting them is plan task 7.2.1.

`tests/core/contexts.fs` (and `contexts-serial.fs` on the serial host)
checks the conversion of the core and kernel modules, and
`tests/core/contexts-main.fs` that of everything `src/main.fs` loads:

- *No state outside the context.* The dictionary that the library, the job
  pool and the modules lay down while loading must be unchanged, byte for
  byte, after real checker work in contexts (`tests/support/dictionary-check.fs`;
  allowed by name is the environment registry `lf-envs`, written only by
  the driving task): a trial of 2,000 steps (below) in one context, and a
  serial run of the checked environment's synthetic checks with every
  publication in another; `contexts-main.fs` also stages a loader batch,
  reads programs with the program reader, loads and runs one with the IR
  interpreter, and prints every term, level and name of the trial in all
  three printer modes. A forgotten `VARIABLE`
  fails even when it is only a register within one call, on every host,
  which the interleaving and job tests below cannot promise (the
  cooperative and serial hosts switch only between whole steps). Today
  this covers 488,752 bytes with `src/main.fs` loaded (64-bit Gforth 1.0;
  498,632 on 0.7.3).
- *Members* other modules and tests name lie inside the current context,
  at the same offset in every context (a hand-kept list, a second line of
  defence), and a new context starts with exactly the bytes the main
  context held right after loading (past the header, whose size field
  grows when tests declare members of their own).
- *Independence.* A *trial* of real checker work — the definition table's
  nine pairs, the composition DAG, the five plain shift and instantiate
  cases, and random terms run through inference, conversion, comparison,
  beta, shift, instantiation, the level passes, universe substitution, the
  signature index and the definition probe — folded into a digest of every
  outcome, result, fuel, count and diagnostic (cleared before each check;
  code and numbers), gives exactly its serial digest when two and then
  eight contexts are interleaved step by step in one task, and when the
  trials run as jobs, with the main context untouched.
- *Recursion in jobs.* The deepest recursive inputs known (beta over 124
  frames, inference over 26 applications, a 63-level chain) run inside a
  job, with both stacks painted: they used 688 return-stack and 480
  data-stack cells, below every stated need (see *Stacks* below).

Measured 2026-11-02 (stress runs, 24 jobs of 1,000 steps per batch, each
run also followed by a run of the checked environment's job test,
`tests/core/environment-tasks.fs` or its serial twin): Gforth 1.0 threads
20 runs × 30 batches, Gforth 0.7.3 cooperative 10 × 10, serial host on
both 10 × 10, 0 failures. Planted faults are caught: a register `VARIABLE`
inside `lf-term-binary` by the dictionary check on all four hosts (the
earlier tests missed it on Gforth 0.7.3 and on the serial host, and caught
it on threads only through a race); the loader's batch record made global
again, by `tests/core/load.fs` and by the dictionary check; a diagnostic
that depends on shared state, by the interleaving, but only while the
digest includes diagnostics; earlier, a walk record or the signature index
left global and a missing set-up word, by the structural checks.

**Cost.** Each member's name is a colon definition that adds its offset,
compiled as a literal, to `lf-context @`, a `USER` variable (until
2026-11-02 a `DOES>` word that fetched the offset from the member record).
A fixed checker workload (composition, deep beta, deep inference, a level
chain and the plain cases, each round: the composition DAG inferred,
probed and converted; beta of the 18- and 61-lambda twins; inference over
26 applications; value and comparison of a 63-level chain; the five plain
cases through inference, beta, shift and instantiation; 1,000 rounds, same
results) took, in five runs of each interleaved on a machine shared with
other work (load about 3.5 on 12 cores):

| Engine | Before contexts (`f8aa35d`) | `DOES>` members (`dbbef73`) | Colon members |
| --- | --- | --- | --- |
| `gforth` | 1,418–1,473 ms (median 1,459) | 1,649–1,731 ms (1,665), +14% | 1,539–1,618 ms (1,588), +9% |
| `gforth-fast` | 482–519 ms (498) | 592–630 ms (615), +23% | 555–604 ms (574), +15% |

So compiled offsets remove about a third of the cost of reaching state
through the context (V's first prototype measured somewhat more, on an
idler machine); passing a store's address on the stack through hot loops
would remove most of the rest. The `DOES>` column includes the diagnostics
(about 1%).

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
| the stack settings do not cover the largest need a module stated (`context-need`); nothing is started | `task-stacks-small` (-4101) |
| Gforth 0.7.3, after an overflow that left a guard zone | `task-overflow` (-4097) |

**Stacks, frames limits and overflows.**

- A recursive pass nests about its frames limit times its cells per frame
  (2 to 6 return-stack and 3 to 4 data-stack cells measured, see
  `frame.fs` above) plus its entry words. A module states its worst
  nesting while it loads with `context-need ( data-cells return-cells --
  )` (`lib/context.fs`; the largest of each is kept, `context-needs` gives
  them, and a need stated after the layout is sealed aborts).
  `pool-start`, and so the first `job-submit`, refuses with
  `task-stacks-small` (-4101), starting nothing, unless `job-stacks-cover?
  ( data-cells return-cells -- flag )` holds for that need: the workers'
  depths less `task-slack-cells`, or on the serial host the host's stack
  sizes less the slack (a host that does not report a size through
  `ENVIRONMENT?` is not checked). So lowering `task-data-cells` or
  `task-return-cells` with `TO` below the need is caught whichever of
  `task.fs` and the kernel loads first. The checker states two needs:
  beta with its nested instantiate and shift passes (`mixed-beta.fs`,
  1,216 return and 960 data cells) and inference, which can nest them at
  its deepest level (`mixed-infer.fs`, 1,728 and 1,280: at most 8 return
  and 5 data cells per level, measured by stack painting along its five
  recursion paths and the two of its rejection analysis (plan task 2.2.1;
  the D5 path needs 8) on Gforth 0.7.3 and 1.0, which agree, times
  `lf-term-capacity` levels, plus beta's need; the definition probe nests
  no deeper). The test job's 500-frame pass used 1,004 return-stack and
  1,001 data-stack cells inside each worker; the deepest checker inputs
  known used 688 and 480 inside a job, and 16 random trials of 2,000
  steps at most 90 and 28 above the caller.
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

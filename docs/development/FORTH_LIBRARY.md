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
| Bounded record stores | `src/lib/store.fs` | `store:` defining word: a fixed number of fixed-width records with an allocation count, a reset generation that saturates to a poisoned state, an identity per record that never repeats, and a sealed shape so header corruption fails closed. `store-size` and `store-init` make the same store in memory obtained at run time (`ALLOCATE`, or a region of a context); `store-plan?` also refuses a size that would not fit in a cell. **Marks** (plan task 1.1.3): `store-mark ( mark store -- outcome )` records the store, its generation, serial and count in a `/store-mark` record the caller provides (fields `mark-store`, `mark-generation`, `mark-serial`, `mark-count`); `store-rollback ( mark store -- outcome )` restores the count, giving back every record allocated since, and never rewinds identities; `store-mark-valid? ( mark store -- flag )` tells whether it would. A rollback is refused, invalid with nothing changed, for a mark of another store, from another generation (a reset since), above the current count, of an invalid or poisoned store, or stale: records below its count must be older than the mark and the one at its count newer, so a mark below which an earlier rollback went and records were allocated again is refused. Marks are not capabilities: a forged record that passes these checks is accepted. **Heap stores** (plan task 1.1.5, ADR 0016 C9 step 3, 2026-11-03): `store-heap-init ( capacity width base store -- outcome )` puts the header in the caller's memory (it may move, as a context member does) and the block of identities and records on the heap; `store-grow ( store -- outcome )` doubles the block, at least 16 more records, up to the limit, when every record is in use (full at the limit, with no heap, or when the test hook refuses; nothing changed then); `store-limit! ( limit store -- outcome )` sets the limit (at least the count; a larger block shrinks); `store-heap-free`. The block and the limit are sealed shape fields; marks stay valid while the block grows; an address from `store-slot` is valid only until the next growth | New 2026-11-02; used by the term, level and name stores; heap stores (the checker's five stores) tested in `tests/lib/lib.fs` (growth, limit, marks across growth, shrinking, freeing); unit-tested in `tests/lib/lib.fs`, run-time stores in `tests/lib/context.fs`; marks 2026-11-02 in `tests/lib/store-mark.fs` (every refusal, and 20,000 random operations against a model that kills a mark when the count drops below it or the store is reset), used by the checked environment's input (`src/core/input.fs`); the hand-written count saving in the existing modules is not converted yet |
| Tagged nodes | `src/lib/node.fs` | `BEGIN-STRUCTURE` record of tag and two fields, with whole-node `node!`/`node@` and `node-new`/`node-read` on a store | New 2026-11-02; terms and levels |
| Range checks | `src/lib/bounds.fs` | `between?` and `upto?` (inclusive, signed, never wrapping) and `cells-zero?` | New 2026-11-02 |
| Outcome vocabulary | `src/lib/outcome.fs` | ok, invalid, exhausted (out of fuel), unknown, rejected, unsupported and full (out of room: a store, work stack, frame, depth or size limit) (ADR 0008), with `ok?`, `outcome-sane`, `flag>outcome` and `room>outcome` (a validity or room flag as ok, else invalid or full), `visit-outcome` (the one rule for a visit bounded by fuel and room: no fuel is exhausted whatever the room, then no room is full), the continue-on-ok steps `ok-then?`, `ok-then2?`, `ok-then3?`, `ok-keep?` and `ok-keep2?`, `outcome-and` (two outcomes as one, the first failure), `outcome-steps` (a 0-ended list of steps run to the first failure; review FRI B6), `ok-and` and `ok-with` (a step run only while the outcome so far is ok, on the values below or on a value kept below; review FRK A), `no-result`, and `outcome-text` (each outcome's name, for reports) | New 2026-11-02; every core and kernel module uses it; the per-module status aliases were removed |
| DAG walks | `src/lib/walk.fs` | `walk:` defining word: fuel, current node, one visitor cell and a bounded work stack in one record; `walk-run` drives a visitor and `walk-visit` reads and dispatches a node. A push without room is full whatever fuel is left (checked where the push happens), and a root that cannot be pushed means a corrupted capacity, which is invalid. `walk-size`/`walk-init` and `walk2-size`/`walk2-init` make the same records at run time. The walk words keep no state of their own; each module's walk records are members of the checker context, one set per context | New 2026-11-02; level scope, Sort representation, session and handle audits use it |
| Passes on an explicit stack | `src/lib/frame.fs` | A frames record: fuel, visits in progress, the visitor (set once), a context cell (such as a binder depth), a job cell, and the pass's stack, a heap block that grows by doubling (plan task 6.2.0). A visit is a chain of steps `( ... frames -- ... frames next )` run by a loop (`frame-run`, `frame-loop`, `frame-steps`), never nested on the host's stacks: a step either asks for a child's visit with `frame-call` or `frame-under` (one context level deeper), naming the step that continues with the child's `( result outcome )`, or returns `( result outcome frames 0 )`; values kept across a child's visit go on the pass's stack (`frame-save`, `frame-restore`, `frame-pick`, `frame-drop`; up to `frame-spare` cells a visit, all its steps together; a save past the block throws `frame-overrun`, -4111, instead of writing outside it, for 0.5% more instructions on the trial workload). `frame-admit` says why a visit cannot open: an unsound stack is invalid, then no fuel left is exhausted, then a stack the heap cannot grow full (the fuel decides first); `frame-under` is full at context `max-n`. `frame-open` opens a visit of another kind (mixed-infer.fs: inference and the rejection analysis share one record), and a step may run a loop of its own on the same record. A busy record refuses a new budget or pass; `frame-reset` recovers after a THROW; `frame-free` gives the stack back. Host-stack use is a constant whatever the depth | New 2026-11-02, explicit stack 2026-11-04; the kernel's shift, instantiate, beta and opening passes, inference and the analysis, normalize, is_geq and level evaluation use it; unit tests and a randomized model test |
| Checker contexts | `src/lib/context.fs` | One `ALLOCATE`d record per worker for all of a check's mutable state ([ADR 0009](../adr/0009-reentrant-state-and-parallel-checking.md)), reached through the `USER` variable `lf-context` (a plain variable on hosts without Gforth's `USER`). Modules declare members while they load: `context-record:`, `context-store:`, `context-walk:`, `context-walk2:`, `context-frames:` (a frames record, set up with `frame-init`), and `context-setup` for set-up words; a refused declaration changes nothing. Each member's name is a colon definition that adds its offset, a literal, to `lf-context @`. Modules also state how deep their checks nest on the host stacks (`context-need`), which the job pool checks. `context-new`, `context-use` and `context-free` make, select and free contexts. Each context is idle or owned by one job; each task has an owner token `lf-owner` and may select only contexts it owns (the main task: idle ones); owned contexts cannot be freed. `context-in-job?` says whether the current task runs a job or a check; the checked environment's serial driver gives a check the token `context-check-owner`, so every in-job guard refuses it too. `context-claim` and `context-release` (the job pool's) are refused there as well. `call-balanced ( x xt -- )` runs a word above a cell and throws `context-unbalanced` (-4096) when the word changed the stack depth or that cell (the checked environment's serial driver uses it; `task.fs`'s `job-call` still has its own copy); `context-catch ( i*x xt -- j*x ior )` is `CATCH` that restores the current context afterwards. `context-slab:` declares a growable array member and `context-teardown` a word that frees a member's heap blocks with its context. The header lists the interface and gives an example; every other word is private (`lf-lib-private`, since 2026-11-12) | New 2026-11-02; ownership, frames members and atomic declarations 2026-11-02 after an independent review; every module of `src/core/` and `src/kernel/` keeps its state in it since 2026-11-02 (see the design below); tested in `tests/lib/context.fs`, including a randomized model with context switches at every step, and with real checker work in `tests/core/contexts.fs` |
| Job pool | `src/lib/task.fs` | `job-submit ( context xt -- job ior )` and `job-wait ( job -- ior )`: a fixed pool of long-lived workers (at most one per logical core, setting `task-workers`) fed from a bounded queue; POSIX threads with a mutex and two condition variables on Gforth 1.0, the cooperative `tasker.fs` on Gforth 0.7.3, and a serial path elsewhere (or when forced, for tests). A job's context is owned by the job until it is waited for. Wrong stack effects give `task-unbalanced`; stack overflows never report success (guard pages on 1.0, canary zones on 0.7.3); a worker that cannot be created is reported (`task-no-worker`). `job-stacks-cover?` tells whether the workers' stacks hold a recursion requirement, and the pool refuses to start with stack settings below the largest need modules stated (`task-stacks-small`). On Gforth 1.0 each worker owns its exception-backtrace and error-stack strings (a new task copies the creator's user area, and shared strings were corrupted by concurrent THROWs). Job rules: never parse or use `PAD` (one buffer for all tasks on Gforth 1.0), use `<# #>` text before the job yields (one buffer on 0.7.3), and restore `BASE` if a job changes it (a worker starts with the main task's). `job-wait-any ( addr n -- k )` waits for the first of several jobs (a scheduler that keeps one job per worker) and `pool-workers! ( n -- )` sets the pool's size for its next start. Loaded by the parallel scheduler (`src/kernel/env-schedule.fs`, `check --jobs`) since 2026-11-11 | New 2026-11-02; pool replaced one thread per task the same day; `tests/lib/task.fs` and `task-serial.fs` compare jobs and interleaved contexts with serial runs for 1, 2 and all workers and reach every refusal; `task-overflow.fs` and `task-overflow-serial.fs` overflow both stacks inside jobs; `tests/lib/task-bench.fs` measures speed-up |
| Line reader and UTF-8 | `src/lib/bytes.fs` | `reader:` record over a Forth-2012 file: whole lines in one heap buffer that grows for long lines up to a limit, strict framing (final line feed; `text-framed` refuses carriage returns and a byte-order mark), line numbers and double-cell file offsets; `utf8-length`, `utf8-valid?`, `utf8-decode` and `utf8-put` (RFC 3629, no overlongs or surrogates); `counted,`; `heap-claim` and `heap-release` for owned heap buffers; `fnv-step` and `bytes-mix` (an FNV-style mix of bytes into a hash, used by the checked environment's input fingerprint). Uses Gforth's native `scan` behind an adapter, with a portable loop otherwise. Loads in decimal whatever `BASE` is, and restores it | New 2026-11-02; unit-tested against an independent UTF-8 model in `tests/lib/bytes.fs`, which loads it under `HEX` and counts heap blocks to show that a second `reader-init` frees the first buffer |
| JSON reader | `src/lib/json.fs` | `json:` view record: a fail-closed, non-recursive RFC 8259 parser of one text into a growable token tape (containers know their item count and extent), escapes decoded in place, numbers kept as digit text, limits on depth, tokens, string and number length; `json-find`, `json-next`, `json-natural`, `json-u`, `digits>u` and `decimal>u` (decimal, independent of `BASE`); kind-checked `json-items-of` and `json-kind-at`. Loads in decimal whatever `BASE` is, and restores it | New 2026-11-02; malformed corpus and every limit tested in `tests/lib/json.fs`, loaded under `HEX` |
| JSON writer | `src/lib/json-write.fs` | Plan task 3.1.3. A writer record (`json-writer: ( depth room "name" -- )`, or `jw-size` and `jw-init` in memory the caller owns, such as a context member) writes one JSON text to the caller's sink xt `( c-addr u -- )`: `jw-start ( sink writer -- )`, then `jw-string`, `jw-n` (signed cell), `jw-u` (unsigned cell), `jw-digits` (integer text of any size, as `json.fs` keeps it), `jw-bool`, `jw-null`, `jw-open-object`, `jw-key`, `jw-close-object`, `jw-open-array`, `jw-close-array`, or `jw-copy ( index view writer -- )` of a value `json.fs` parsed; `jw-end ( writer -- outcome )`. Every call takes the writer last and returns nothing. Deterministic bytes: no whitespace; members in call order, and with `jw-sorted` set each object's keys must strictly increase in byte order (code point order), checked against the last key kept in a key pool of `room` bytes; integers in decimal whatever `BASE` is, `-0` written `0`; strings escaped only as `\"`, `\\`, `\b \f \n \r \t` and `\u00xx` (lowercase) for other bytes below 32, everything else, valid UTF-8 included, as itself, which are the bytes of Python's `json.dumps(v, separators=(",", ":"), ensure_ascii=False)`; with the setting `jw-lean` (2026-11-03, for the NDJSON re-exporter) the bytes of Lean 4.35.0's `Json.compress` instead, which writes backspace, tab and form feed as `\u0008`, `\u0009` and `\u000c`; no real numbers (`jw-copy` of one is unsupported). The first failing call writes nothing and its outcome sticks until the next `jw-start` (`jw-outcome` reads it): invalid for calls out of order (a close that does not match its open or follows a key, a value where a key is due, a second value, `jw-end` before the value is complete, writes before `jw-start` or after `jw-end`), invalid UTF-8, bad integer text or flags, keys out of order in sorted mode, and any call from inside the writer's own sink (`jw-reset` or `jw-init` there fails the text when the sink returns); full past the byte limit `jw-limit` (so a buffer of n bytes never overflows), the depth or the key pool. So `jw-end` gives ok only for exactly one complete JSON value, and the sink only ever receives a prefix of one. After a THROW out of a writer word the caller discards the text and calls `jw-reset` (a THROW outside the sink leaves no mark); a sink that writes over the string or view being written is unchecked. No state of its own; `jw-copy` is a loop over the value's tokens, without recursion (a container it opens records the index of the token after it, and closes there), so a few stack cells serve any depth the writer allows. Loads in decimal whatever `BASE` is, and restores it | New 2026-11-02; `tests/lib/json-write.fs` (180 assertions: every word's positive and negative cases, every limit at and one past its bound, sorted keys, keys refused as strings are, the sink rules including `jw-reset` and `jw-init` from inside the sink, a copy 10,000 containers deep and copies stopped by a failed close, two interleaved writers and a context member, 2,000 random strings and 2,000 random cells written and read back by `json.fs`, and all 138 lines of `tests/reference/*.ndjson` plus 16 lines with every other record kind of lean4export 3.1.0, `tests/lib/json-write-corpus.ndjson`, copied back byte for byte in both key modes; Lean's escapes for every byte below 32, keys, copies and `jw-limit`, 2026-11-03), loaded and partly run under `HEX`; `tests/lib/test_json_write.py` compares 300 random values written with the writer's words and 150 non-canonical texts copied with `jw-copy` against Python's `json.dumps`, 40 copies of values nested up to 64 deep, plus 50 refusals with their exact prefixes; 21 planted faults each caught, and after the independent review (2026-11-02) 6 more, one per fix reverted or broken, on Gforth 0.7.3 and 1.0 |
| Packed 32-bit fields | `src/lib/u32.fs` | `u32@ ( addr -- u )` and `u32! ( u addr -- )` read and write an unsigned 32-bit field; `u32s ( n -- au )` sizes *n* fields; `u32-mask` is the 32-bit mask on any cell size. Gforth's `l@`/`l!` where the host has them and a load-time check (`u32-sound?`) shows they are unsigned 32-bit access: a value with bit 31 set comes back unchanged, and the four characters after the field keep their values; otherwise, or when `lf-u32-portable` is defined first, the Forth-2012 `u32-bytes@`/`u32-bytes!` (four characters, least significant first, an order the module fixes; public for the tests only). `u32!` keeps the low 32 bits; on a 32-bit host a value of 2³¹ or more reads back as a negative cell, so compare with `U<`. Loads in decimal whatever `BASE` is, and restores it. The layout of packed records is defined by arithmetic on the values, never by byte order, and packed memory is never written to a file as it is (the little-endian block words `u32s>le`, `le>u32s`, `u32-le!`, `u32-le@` convert, for sectioned files). The only non-text module allowed byte access (`scripts/check-portable-forth.py`) | New 2026-11-02 for the compact store ([ADR 0016](../adr/0016-compact-store.md), accepted 2026-11-03); not loaded by `lib.fs`; used since 2026-11-03 by the compact store's modules ([below](#the-compact-store)); both versions tested on every host in `tests/lib/lib.fs`, which loads it under `HEX` and asserts that Gforth's words are in use, shows the check refusing a sign-extending fetch and a cell-wide store, and loads it again under `BASE` 8 with `lf-u32-portable` defined to get the Forth-2012 version; after the independent review (2026-11-02) 6 planted faults each caught |
| Wordlist modules | `src/lib/module.fs` | The two library wordlists of [ADR 0010](../adr/0010-wordlists.md) (accepted), `lf-lib` (public, pushed onto the search order once) and `lf-lib-private` (helpers), and its four words `order+`, `order-`, `module-open`, `module-close` | New 2026-11-03; used by the compact store's library modules below, `sha256.fs`, `text-rule.fs`, `text-run.fs` and, since 2026-11-12, `context.fs` (the ADR's migration converts the others); tests reach helpers with `lf-lib-private order+` |
| Portable 32-bit hashing | `src/lib/hash32.fs` | `hash-fmix` (Murmur3's finaliser), `hash-step ( h x -- h' )` and `hash-bytes ( addr u -- h )` (FNV-1a), every product masked to 32 bits, so 32- and 64-bit hosts give the same values ([below](#the-compact-store)) | New 2026-11-03; `tests/lib/hash32.fs` against values computed in Python |
| Growable heap stores | `src/lib/slab.fs` | Plan task 1.1.5. `slab-init ( unit limit slab -- outcome )`: units of any size in one heap block that doubles by `RESIZE` up to a limit; `slab-room`, `slab-claim`, `slab-commit`, `slab-at`, `slab-top`, `slab-trim`, `slab-clear`; marks `slab-mark`, `slab-rollback`, `slab-mark-valid?` with `store.fs`'s refusals ([below](#the-compact-store)) | New 2026-11-03; `tests/lib/slab.fs` |
| Stable sorting | `src/lib/sort.fs` | `sort-records ( a-addr n sorter -- outcome )` sorts n records of any size in place by the caller's order `( a-addr1 a-addr2 -- n )`, or by their keys (`sorter-key!`; `sorter-cells` and `sorter-u32s` order values); stable: insertion up to `sorter-short` (32) records, above that a bottom-up merge from runs of one record through a scratch (the caller's, `sorter-buffer!`, or the heap's: full when refused, nothing changed), its comparisons call for call those of `level-normalize.fs`'s `lf-lnorm-sort`; no recursion; invalid for a bad count, a sorter not accepted or busy, and an order or key word that changes the stack depth; a THROW out of the order is passed on, the scratch freed ([below](#sorting)) | New 2026-11-12 (the kernel refactor's batch C2 waited for it); not yet used by any module (the snapshot's three insertion sorts wait for the owner's approval of the kernel change); `tests/lib/sort.fs`, 23 planted faults each caught |
| Hash tables | `src/lib/htab.fs` | Open addressing over 32-bit slots, hooks for rehashing and comparing, growth at 3/4, removal by Algorithm R, `htab-spread` and `htab-presize` ([below](#the-compact-store)) | New 2026-11-03; `tests/lib/htab.fs` |
| Hash-consed sets in two tiers | `src/lib/cons.fs`, `src/lib/pools.fs` | Each distinct record once, named by a number; a sealed input set shared read-only and scratch sets over it whose numbers continue; marks, resets, sealing; interned lists of 32-bit numbers (tuples, no fixed length) and texts ([below](#the-compact-store)) | New 2026-11-03; `tests/lib/cons.fs` |
| Compact store | `src/core/compact.fs` and `compact-tier.fs`, `compact-names.fs`, `compact-levels.fs`, `compact-exprs.fs` | ADR 0016's Lean layer: names, levels, universe lists, literals and 16-byte expression records in input and scratch tiers ([below](#the-compact-store)) | New 2026-11-03; not yet used by the kernel; `tests/core/compact.fs`, round trips of the reference exports and of `Init` |
| Big natural numbers | `src/lib/bignum.fs` | Arbitrary-precision naturals for Lean's `Nat` literals ([below](#big-natural-numbers)): numbers in an arena the caller provides (`/big-arena`, `big-arena-init`; `big-mark` and `big-release` give back what was made since a mark), one-cell limbs whose width is counted (`limb-bits`), decimal reading and printing (`decimal>big`, `big>decimal`), conversion to and from a cell (`u>big`, `big>u`), comparison (`big-compare`, `big=`, `big<=`), and the operations Lean 4.35.0's kernel computes on literals (`big+ big- big* big/ big-mod big-gcd big-and big-or big-xor big-lshift big-rshift big-pow`, each `( a b arena -- c outcome )`). Schoolbook multiplication with Karatsuba from 48 limbs, Knuth's algorithm D, Lehmer's gcd. Outcomes ok, invalid (a malformed or released number, text or arena) and full (no room, or more bits than the arena's limit, by default Lean's 2^30). No state; loads in decimal whatever `BASE` is | New 2026-11-02 (plan task 5.2.3, library part); not yet used by the kernel (task 5.1.4); `tests/lib/bignum.fs` reaches every outcome; `make test` compares 37,585 cases with Python's integers on the running Gforth and catches 22 planted faults; review fixes of 2026-11-03 (printing overwrote the number below its text, stale operands, two speed fixes) with guarded-arena sweeps; `make check` has 984 of them computed by pinned Lean's kernel |
| Signed big integers | `src/lib/bigint.fs` | Lean 4.35.0's `Int` over `bignum.fs` ([below](#signed-big-integers)): an integer is a sign cell (-1, 0, 1) followed by a bignum magnitude, made at the top of a bignum arena; `bigint+ bigint- bigint* bigint-ediv bigint-emod` `( a b arena -- c outcome )` (Lean's `/` and `%` on `Int` are `Int.ediv` and `Int.emod`), `bigint-bmod` and `bigint-pow` `( x m arena -- c outcome )` with a natural number `m`, `bigint-negate`, `bigint-gcd`, `bigint-natAbs` and `bigint-toNat` (natural-number results), `bigint-compare`, `bigint-sign`, `bigint-magnitude` (in place), `nat>bigint`, `n>bigint`, `bigint>n`, `decimal>bigint`, `bigint>decimal`, `bigint-valid?`. Outcomes ok, invalid, full as `bignum.fs`'s. Standalone: requires `bignum.fs`, `bounds.fs`, `outcome.fs`, `portability.fs` and `module.fs`; helpers private (ADR 0010); no state; no host recursion of its own; loads in decimal whatever `BASE` is | New 2026-11-13 (plan step FE1i-4, for `by-omega` and `by-decide`); tested alone, on branch `fe1i4-bigint`; no tactic uses it yet. `make test-bigint`: unit tests of every word and outcome, every room from 0 cells up, no heap use; 9,906 pairs against a model of Lean's definitions; the header's example and exact interface from outside the project. `make reference-bigint`: 17,906 pairs (10,000 random) equal pinned Lean's own `Int`, line for line, and 300 kernel-decided equations. 17 planted faults (`fe-bigint-…`) each caught; Forth review 2026-11-13 not blocking, its M1, L1, L2, S1 fixed |
| SHA-256 | `src/lib/sha256.fs` | FIPS 180-4 SHA-256, incremental ([below](#sha-256)): `sha256:` (or `/sha256` address units of the caller's memory), `sha256-init ( sha -- )`, `sha256-update ( c-addr u sha -- )` with pieces of any size, `sha256-final ( c-addr sha -- )` for the 32-byte digest, `sha256-hex ( c-addr1 c-addr2 -- )` for its 64 lowercase hexadecimal digits. One word per FIPS function (`sha-rotr`, `sha-shr`, `sha-ch`, `sha-maj`, `sha-big-sigma0`, `sha-big-sigma1`, `sha-small-sigma0`, `sha-small-sigma1`), the plain round and schedule built from them, and on cells of 64 bits or more a fast round and schedule with the functions written out in place. Standalone: requires only `portability.fs` and `module.fs`; helpers private in `lf-lib-private` (ADR 0010); no state of its own; nothing fails. Loads in decimal whatever `BASE` is | New 2026-11-03 (plan task 3.2.6, for the export manifests); the program track's flagship verification target; `make test-sha256`: NIST vectors, every split of messages up to 200 bytes, the functions against independent models, the fast round against the plain one, 306 random messages against Python's `hashlib` on both paths, the header's example and the exact public interface checked from a folder outside the project; 14 planted faults each caught |
| Visible text | `src/lib/text-rule.fs` | `tr-rule? ( c-addr u -- flag )`: valid UTF-8 with no control, format, line or paragraph separator or surrogate character (Unicode Cc, Cf, Zl, Zp, Cs); `tr-banned? ( code -- flag )`: a code point no such text holds; `tr-shown? ( c-addr u -- flag )`: also a character that is seen, not a space, a blank-looking filler, a combining mark or a default-ignorable code point. The rule of program receipts 0.2 and of run records; tables generated from Unicode 15.1 by `scripts/text_rule_tables.py`. Requires `bounds.fs`, `bytes.fs` and `module.fs`; helpers private; no state | New 2026-11-03 (run records, plan task 2.2.5); `tests/lib/text-rule.fs` on its own; every code point compared with the run-record schema's patterns by `tests/core/test_run_records.py` |
| Portability adapter | `src/lib/portability.fs` | Forth-2012 definitions of `>=`, `<=`, `0<=`, `0>=`, `-rot`, `max-n`, `cell` and the structure words, compiled only where the host lacks them. `scripts/check-portable-forth.py` refuses a module under `src/` that uses one of them without loading this file, directly or through the files it loads | New 2026-11-02; defines nothing under Gforth except `max-n`; `cell` and the load check added 2026-11-02 |
| Diagnostics | `src/core/diagnostics.fs` | One record per checker context explaining the first failure of a check: a reason code, the site (module and word, a counted string) and two numbers; first failure wins until `lf-diag-clear`; `lf-diag@`, `lf-diag.`; helpers `lf-diag-walk`, `lf-diag-frames` and `lf-diag-store` explain a walk's, a pass's or a store's failure. Never changes an outcome; catalogue in [DIAGNOSTICS.md](../programming/DIAGNOSTICS.md) | New 2026-11-02 (plan 6.7, first form); every core and kernel module records its full and exhausted sites; `tests/core/diagnostics.fs` |
| Expression store | `src/core/terms.fs` | Index-based nodes for sorts, bound variables, application, λ, Π and constants; nodes refer to earlier indices, so a term is a DAG with sharing | A heap store per checker context whose capacity is a setting (default 64, `lf-term-capacity!`), grown by doubling; per-term side data in growable columns (`store-columns.fs`); constructors check ranges only |
| Universe-level store | `src/core/levels.fs` | Level DAGs: zero, succ, max, imax, parameters | A heap store per checker context, capacity a setting (default 64, `lf-level-capacity!`); columns as for terms |
| Name interning | `src/core/names.fs` | Lean structured names (string and numeric components) stored once and referred to by index | A heap store (default 64 entries, a setting) and 2,048 bytes, found by a linear scan; or, attached to a sealed compact input tier (`lf-name-attach`), that tier's interned names plus one scratch tier over it |
| Stale-handle detection | `src/core/generation-handles.fs`, `symbolic-session.fs` | Handles carry a generation number so a handle from before a reset is rejected | Works; tests found one unguarded path |
| Constant references | `src/core/constant-references.fs`, `constant-term-*.fs` | A constant's name plus universe arguments, with syntax and scope audits | 32 references per checker context |
| DAG walkers | `mixed-shift`, `mixed-instantiate`, `mixed-beta`, `mixed-compare`/`mixed-convert`, `mixed-infer` in `src/kernel/` | Bounded traversals with explicit work stacks and fuel, rolling back on failure | Current; the earlier plain and `tagged-` variants were retired 2026-11-02 (roadmap Q9) |
| Level algorithms | `level-scope`, `level-value`, `level-compare`, `level-substitute`, `mixed-level-substitute` | Scope checks, evaluation, conservative equality and simultaneous substitution of levels | Current |
| Signature index | `mixed-signature-probe.fs`, `mixed-signature-audit.fs` | Candidate signatures of constants, specialised to universe arguments | 32 entries; unchecked assumptions |
| Record staging | `src/import/load.fs` | Copies already-decoded expression records into the term store | Not a parser; stages concrete Sorts, which no current checker pass accepts; kept with its round-trip tests until the Forth NDJSON reader replaces it |
| NDJSON export reader | `src/import/ndjson.fs`, `ndjson-count.fs`, `ndjson-emit.fs` | Decodes every record kind of lean4export format 3.1.0 into decoded-record layouts and hands each to a handler per kind; checks exact field sets, dense indices and earlier references; a counting tool; a re-exporter that writes every record back in the exporter's exact bytes (plan task 3.2.4) | New 2026-11-02; untrusted, fail-closed; equal to Python on all of Mathlib; the re-exporter (2026-11-03) gives `Init`, `Std` and all of Mathlib back byte for byte; see [NDJSON_READER.md](NDJSON_READER.md) |
| Presentation side table | `src/present/binder-table.fs` | Binder names and kinds, source record IDs and declared constant types, keyed by term index and stamped with the term's identity and the name store's generation, so a reset makes entries read as absent; never read by the checker | New 2026-11-02; one context record; 64 term entries, 32 declarations; `tests/present/term-printer.fs` |
| Term printer | `src/present/term-printer.fs` and `print-job.fs`, `print-names.fs`, `print-tokens.fs`, `latex-text.fs`, `print-levels.fs`, `print-analysis.fs` | Prints terms, levels and names to a caller's sink xt in Lean's notation, ASCII or LaTeX (and Markdown math): capture-free binder names, ∀/→ and binder grouping, hidden implicit arguments and minimal parentheses as Lean's delaborator; fuel, and one `frames` record (`src/lib/frame.fs`) on whose growable stack every recursive printing word runs as a chain of steps, so no depth is tied to the host's stacks; a growable scope and name pool; exhausted without fuel, full when the heap refuses room or a caller's nested-visit limit is reached | New 2026-11-02; agrees with Lean on 49 cases and the five pinned fixtures (`make test-printer-differential`); [user guide](../user/TERM_PRINTER.md) |
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
| `bigint.fs` (signed integers) | yes, written to this rule (2026-11-13); Lean only in comments: its semantics are Lean's `Int`, which is also ordinary Euclidean division | requires `bignum.fs`, `bounds.fs`, `outcome.fs`, `portability.fs` and `module.fs`; helpers in `lf-lib-private`, 20 public words (`bigint…`, `nat>bigint`, `n>bigint`, `decimal>bigint`); an example in its header, run with the exact interface checked from a folder outside the project by `make test-bigint` |
| `json.fs` (RFC 8259 reader), `json-write.fs` | yes | `json.fs` requires `bytes.fs`, which requires the whole `lib.fs` (contexts, walk records, frames) although it uses little of it; helper names public |
| `bytes.fs` (bounded line reader, UTF-8) | yes, with strict framing rules chosen for Lean's exports (no carriage return, no byte-order mark, final line feed) | requires all of `lib.fs`; the framing rules should become options |
| `u32.fs` (32-bit access) | yes | none beyond `portability.fs` |
| `store.fs`, `node.fs`, `walk.fs`, `frame.fs` (bounded stores, records, explicit-stack walks) | yes | the shared outcome vocabulary |
| `context.fs`, `task.fs` (per-task contexts, job pool) | partly: a general job pool and context mechanism, designed around the checker's per-check state | the checker's context model (ADR 0009) |
| `outcome.fs` (ok, invalid, exhausted, unknown, rejected, unsupported, full) | LeanForth's shared result vocabulary | deliberately shared: one vocabulary for every module |
| `sections.fs` (sectioned binary files) | yes, written to this rule (2026-11-11): requires `portability.fs`, `module.fs`, `outcome.fs`, `u32.fs`, `sha256.fs`; helpers private; 14 public words, all `sections…`; an example in its header, run with the interface checked from a folder outside the project by `make test-sections` |
| `sha256.fs` (SHA-256) | yes, written to this rule (2026-11-03) | requires only `portability.fs` and `module.fs`; helpers in `lf-lib-private`, 17 public words (the hashing interface and FIPS 180-4's functions), all named `sha-…` or `sha256…`; an example in its header and [below](#sha-256), run with the interface checked from a folder outside the project by `make test-sha256` |
| `sort.fs` (stable sorting) | yes, written to this rule (2026-11-12) | requires `portability.fs`, `bounds.fs`, `outcome.fs`, `u32.fs` and `module.fs`; helpers in `lf-lib-private`, 11 public words, all named `sort…` or `sorter…`; an example in its header, run by `tests/lib/sort.fs` without the checker |
| `text-rule.fs` (visible text) | yes, written to this rule (2026-11-03): a UTF-8 hygiene rule with nothing of Lean | requires `bounds.fs`, `bytes.fs` (and through it `lib.fs`) and `module.fs`; helpers in `lf-lib-private`, three public words (`tr-banned?` since 2026-11-04, for callers that decode text themselves); an example in its header; `tests/lib/text-rule.fs` runs without the checker |
| coming: the compact store (ADR 0016) | written to this rule from the start | — |

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

## SHA-256

`src/lib/sha256.fs` (2026-11-03, plan task 3.2.6): SHA-256 exactly as
FIPS 180-4 defines it, in portable Forth-2012, for the export manifests
([NDJSON_READER.md](NDJSON_READER.md#manifests)), which hash a whole export
during its single read. A standalone library under the owner's rule
([above](#reusability-the-libraries-as-standalone-forth-code)): it requires
only `portability.fs` and `module.fs` and knows nothing of LeanForth; any
Forth-2012 system with cells of at least 32 bits and 8-bit characters can
load it. Its public words, in the word list `lf-lib`, are the hashing
interface below and FIPS 180-4's functions; every helper (the round, the
schedule, the compression, padding, the record's fields) is in
`lf-lib-private` (ADR 0010), which tests and proofs open with
`lf-lib-private order+`; every name starts `sha-` or `sha256`. Untrusted
until reviewed; the program track's flagship target is to prove it equal
to FIPS 180-4 ([plan](../project/PLAN_DRAFT.md), "Flagship program
target").

```forth
require src/lib/sha256.fs
sha256: hasher                \ a record holding one hash in progress
create digest 32 allot  create text 64 allot
hasher sha256-init
s" ab" hasher sha256-update  s" c" hasher sha256-update
digest hasher sha256-final  digest text sha256-hex  text 64 type
```

prints `ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad`,
the SHA-256 of `abc`, however the message is split into updates (pieces of
any size, 0 bytes included). `/sha256` address units of the caller's
memory serve as well as `sha256:`; separate records are independent. After
`sha256-final` a record must be given to `sha256-init` again. Nothing
fails: every byte string is a message. A message must be shorter than
2^64 bits (FIPS 180-4, 5.1.1).

| Public word | Stack effect | Does |
| --- | --- | --- |
| `/sha256`, `sha256:` | `( -- u )`, `( "name" -- )` | the record's size; a named record |
| `sha256-init` | `( sha -- )` | starts a hash |
| `sha256-update` | `( c-addr u sha -- )` | adds bytes to the message |
| `sha256-line` | `( c-addr u sha -- )` | adds a line of text, then a line feed (10) |
| `sha256-final` | `( c-addr sha -- )` | writes the 32-byte digest |
| `sha256-hex` | `( c-addr1 c-addr2 -- )` | the digest as 64 lowercase hexadecimal digits |
| `sha-digest-bytes` | `( -- 32 )` | the digest's size |
| `sha-w32`, `sha-shr`, `sha-rotr` | `( x -- u )`, `( u n -- u' )` | 3.2: modulo 2^32, SHR^n, ROTR^n |
| `sha-ch`, `sha-maj` | `( x y z -- u )` | 4.1.2: Ch, Maj |
| `sha-big-sigma0`, `sha-big-sigma1`, `sha-small-sigma0`, `sha-small-sigma1` | `( u -- u' )` | 4.1.2: Σ0, Σ1, σ0, σ1 |

**Design.** One word per FIPS function, each with the section it
implements: `sha-shr` and `sha-rotr` (3.2), `sha-ch` and `sha-maj` (4.2,
4.3), `sha-big-sigma0`, `sha-big-sigma1`, `sha-small-sigma0`,
`sha-small-sigma1` (4.4–4.7). A 32-bit word is a cell holding 0 to 2^32−1
on any cell size; every step that can set a bit above bit 31 is masked
(`sha-w32`), which is the addition modulo 2^32 of 3.2. The eight working
variables are not moved each round: a table of 68 rows holds W(t), K(t)
and two variables A(t) and E(t), round t reads rows t to t+3 and fills row
t+4, so FIPS's renaming `h=g, g=f, …` is the step to the next row.
`sha-round-plain` and `sha-schedule-plain` compose the named functions as
FIPS writes them. On cells of 64 bits or more, `sha-round` and
`sha-schedule-word` are the same computations with the functions written
out in place, a rotation done as one right shift of the word written twice
(`u + u·2^32`), and one mask per stored word (bits 0–31 of `+`, `xor`,
`and`, `or` depend only on bits 0–31 of their operands); elsewhere, or
when `sha256-portable` is defined before the file loads, they are the
plain words. The tests compare the two on 500 random tables.

**Speed** (this machine, 2026-11-03, `tests/lib/sha256-bench.fs`: 64 MiB in
memory, one update, three runs; the machine was shared with other work):

| Engine | Fast round (64-bit cells) | Plain definitions |
| --- | --- | --- |
| `gforth-fast` 1.0 | 0.92–0.97 s, **69–73 MB/s** | 3.45–3.72 s, 18–19 MB/s |
| `gforth` 1.0 | 4.8–5.4 s, 12–14 MB/s | — |
| `gforth` 0.7.3 | 11.7–12.0 s, 5.6–5.8 MB/s | — |
| `sha256sum` (GNU coreutils, SHA extensions) | 0.07 s with the file read, about 1 GB/s | |

Calls dominate in `gforth-fast`: the same algorithm took 2.37 s per 64 MiB
with the window's cells reached through colon words, 1.81 s with them as
constants, 1.49 s with the masks written in place, 1.11 s with the round's
functions written in place and 0.86–0.92 s with the schedule's too;
splitting the round into two words again cost about 10%. So the hot path
keeps the functions in place, with a comment, and the named words remain
for the plain path, the tests and the proofs. At 70 MB/s all of Mathlib's
6.26 GB take about 90 s to hash (measured during its read in
[NDJSON_READER.md](NDJSON_READER.md#manifests)).

**Tests** (`make test-sha256`; Gforth 1.0 and 0.7.3):

- `tests/lib/sha256.fs`, loaded under `HEX`, and `tests/lib/sha256-plain.fs`
  (the same with the plain definitions): FIPS 180-4's examples (empty,
  `abc`, the 448- and 896-bit messages) and one million `a` in 1,000
  updates; 55, 56, 63, 64, 65, 119, 120, 127, 128 and 129 bytes of `a`
  against `hashlib`'s digests; every length from 0 to 200 bytes hashed
  whole, split in two at every point, one byte per update, with an empty
  update around every byte, and split in three at each pair of 55, 56,
  63, 64 and 65; the named functions on 2,000 random words against
  independent models (rotation as one-bit rotations, the textbook Ch and
  Maj); the fast round and schedule against the plain ones on 500 random
  tables; the length's carry into its high word and its big-endian place
  in the padding; two interleaved records.
- `tests/lib/test_sha256.py`: 306 random messages (every length to 300
  bytes, and 1 KiB to 1 MiB) hashed in updates of random sizes, 0 to 139
  bytes, against Python's `hashlib`, on both paths, one also against
  `sha256sum`; and the header's example, with the library,
  `portability.fs` and `module.fs` copied into a fresh folder outside the
  project, run there as a program of its own; there too every public word
  is found and every other name the library's source defines is hidden,
  and the public names are exactly the table above.
- 14 planted faults, kept in `tests/mutants/faults.toml` (`make mutants`;
  ids `sha-…`) (a rotation's shift, Maj, a Σ1 shift and an unmasked
  store in the fast round, a σ0 shift in the fast schedule, a K constant,
  an initial hash word, the byte order, the final addition's row, the
  length's carry, the padding boundary, the buffer's room, the hexadecimal
  letters, and the helpers made public), each caught by the tests; the
  tree without a fault passes.

## Sectioned binary files

`src/lib/sections.fs` (2026-11-11, snapshot plan step SN1; untrusted until
reviewed): a container of up to 62 sections of equal-size units behind a
4,096-byte header, each section and the header checked by a SHA-256. It
knows nothing of what the sections hold. Requires `portability.fs`,
`module.fs`, `outcome.fs`, `u32.fs` and `sha256.fs`; helpers private in
`lf-lib-private`; all numbers in the file little-endian, written through
the block words added to `u32.fs` (`u32s>le`, `le>u32s`, `u32-le!`,
`u32-le@`: one block copy when the host stores a packed field in that
order, checked once while loading, field by field otherwise; the field
versions are public for the tests, and `lf-u32-fields` forces them). The
byte layout is in [the format page](../programming/SECTIONED_FILES.md).

```forth
require src/lib/sections.fs
sections: sf   create fields 3 u32s allot   create bytes 12 allot
7 fields u32!  8 fields 1 u32s + u32!  9 fields 2 u32s + u32!
fields bytes 3 u32s>le                 \ the section's bytes, little-endian
42 5 sf sections-field! .              \ caller's header field 5 = 42; 0 = ok
bytes 4 3 1 sf sections-add .          \ addr unit-size count kind
s" out.sect" sf sections-write .       \ writes out.sect atomically
sf sections-init
s" out.sect" sf sections-open .        \ checks the header and the layout
create back 12 allot  back 12 0 sf sections-read .   \ addr room i
back 4 + u32-le@ .  sf sections-close .
```

prints `0 0 0 0 0 8 0`.

| Word | Stack | Meaning |
|---|---|---|
| `sections:`, `/sections` | `( "name" -- )`, `( -- u )` | a named record; its size |
| `sections-init` | `( sf -- )` | clears a record (before writing or opening) |
| `sections-field!`, `sections-field@` | `( u i sf -- outcome )`, `( i sf -- u true \| false )` | the caller's 16 header fields |
| `sections-add` | `( addr unit count kind sf -- outcome )` | adds a section from the caller's memory; full after 62; invalid for a bad unit size, count or kind |
| `sections-write` | `( c-addr u sf -- outcome )` | writes `FILE.partial`, flushes it, renames it over `FILE`; any failure, including a THROW (thrown again), deletes the partial and leaves an old `FILE`; the record's table is forgotten |
| `sections-open` | `( c-addr u sf -- outcome )` | magic, header SHA-256, version, byte order; the header built again from the table's kinds, units and counts must equal the one read, ending at the file's size |
| `sections-count`, `sections-info` | `( sf -- n )`, `( i sf -- kind unit count length )` | what the table says |
| `sections-read` | `( addr room i sf -- outcome )` | copies a section into the caller's block and checks its SHA-256; the block is untrusted unless ok (zeroed on a failed read or SHA-256) |
| `sections-close` | `( sf -- outcome )` | closes the file |

Outcomes: invalid (malformed, truncated, unreadable, bad argument),
unsupported (another format version or byte order), rejected (SHA-256
mismatch), full (room, name length, 63rd section). Limits: lengths and
offsets are cells (2^31-1 bytes on a 32-bit host); a section is read whole;
padding bytes are not under a SHA-256 (they are not data). Tests
(`make test-sections`): round trips of 0, 1 and 62 sections, empty
sections and one of 2^20 units; about forty planted faults, each refused with its
outcome (wrong magic, byte order, version; truncation inside the header,
at its end, inside a section, in the padding, one byte short, one byte
long; a flipped byte in the header's fields, table, digest and padding
and in each section; a section overlapping, outside, misaligned or after
a gap; length unequal to unit times count; a 64-bit length or count
beyond the file; unit size 0; 63 sections; fewer sections than the file
holds; an all-zero file); a THROW while writing and a failed rename
leave the old file and no partial; Python reads every file written with
`hashlib` (offsets, alignment, zero padding, both SHA-256s); the block,
field-by-field and Forth-2012 u32 paths write byte-identical files; two
writes are identical; the header's example and the exact public interface
are checked from a folder outside the project.

## Sorting

`src/lib/sort.fs` (2026-11-12; untrusted until reviewed): stable sorting
of records in place. The kernel refactor review (batch C2,
[the review](forth-reviews/2026-11-12-backlog-kernel.md); I2 of
[its follow-up](forth-reviews/2026-11-12-refactor-frk.md)) found three
hand-written insertion sorts in `src/kernel/env-snapshot.fs` that should
be one library word; their results, a snapshot's bytes, depend on the
order of records with equal keys. A standalone library under the owner's
rule ([above](#reusability-the-libraries-as-standalone-forth-code)): it
requires `portability.fs`, `bounds.fs`, `outcome.fs`, `u32.fs` and
`module.fs`, knows nothing of Lean, and keeps its helpers in
`lf-lib-private`.

```forth
require src/lib/sort.fs
create by-value /sorter allot   create numbers 5 , 3 , 9 , 3 ,
' sort-signed by-value sorter-cells drop
numbers 4 by-value sort-records .     \ 0 (ok); numbers holds 3 3 5 9
create by-key /sorter allot           \ 8-byte (key, payload) pairs by the first 32-bit field
8 ' sort-unsigned by-key sorter-init drop  ' u32@ by-key sorter-key!
```

| Word | Stack | Meaning |
| --- | --- | --- |
| `/sorter` | `( -- u )` | a sorter record's size; the record is the caller's |
| `sorter-init` | `( size order sorter -- outcome )` | records of `size` address units ordered by `order ( a-addr1 a-addr2 -- n )`; invalid for a size below 1 or order 0 (every sort then refuses the sorter); clears every setting |
| `sorter-cells`, `sorter-u32s` | `( order sorter -- outcome )` | cells, or packed 32-bit fields (`u32.fs`), ordered by value: `order ( x1 x2 -- n )` |
| `sorter-key!` | `( fetch sorter -- )` | the order is given `fetch ( a-addr -- x )` of each record instead of its address |
| `sorter-buffer!` | `( addr u sorter -- )` | the caller's scratch of `u` address units, used by a merge that fits in it |
| `sorter-short` | `( sorter -- addr )` | setting: up to this many records by insertion (`sort-short`, 32, after `sorter-init`) |
| `sort-records` | `( a-addr n sorter -- outcome )` | sorts the `n` records at `a-addr` in place |
| `sort-signed`, `sort-unsigned` | `( x1 x2 -- n )` | orders of values: -1, 0 or 1 |

**The order.** It is given the earlier record first, never a record and
itself; a positive result means the earlier record goes after the later,
zero or negative leave them in their order. So the sort is stable, and
for any order that is a total preorder its result is the unique stable
one: exactly an insertion sort's, equal keys included. Any other order
(one that stops deciding when its fuel runs out, or one at random) still
leaves a permutation of the records. The order and the key word must take
their arguments and give one result; the depth is checked after every
call, before the result is used.

**Design.** Up to `sorter-short` records are sorted by insertion: each
record from the second on is compared with the earlier ones, nearest
first, while the order is positive (the comparisons of an insertion sort
by exchanging neighbours, at most n(n−1)/2) and then rotated into place;
no memory is needed, which suits the short lists the checker sorts most.
Above the cut-over, a bottom-up merge sort from runs of one record: in
each pass runs are merged in pairs from the start (a last run without a
partner stays), the right run's record first only when the order is
positive; at most n·⌈log2 n⌉ comparisons, the fewest of the stable
methods tried, and comparisons cost an `EXECUTE` or two each. These are,
call for call, the comparisons of `lf-lnorm-sort` in
`src/kernel/level-normalize.fs`, whose cut-over is also 32, so a
comparison that spends a unit of fuel spends the same. Each merge reads
its runs in the records' own memory, writes the scratch and copies the
result back in one `MOVE`: the order only ever sees addresses of the
records themselves, and at every call they are a permutation of the
input. Records move only by `MOVE` (no byte access, as
`scripts/check-portable-forth.py` requires of `src/lib`), an insertion's
rotation going through a temp of four cells in the sorter, a larger
record in several parts. No recursion: the host's stacks hold a few cells
whatever n is. The sort runs under `CATCH`, so that its scratch is freed
and the sorter ready again after a `THROW`.

**Outcomes.** ok; invalid with nothing done for a negative n, n records
whose address units would not fit a cell, or a sorter that `sorter-init`
did not accept or that is sorting already (a nested call from its own
order); invalid when the order or key word changed the stack depth, the
records then in some order (a permutation); full, nothing changed, when n
is above the cut-over and the heap refuses the n·size address units of
scratch (the caller's buffer is used instead when it holds them). A
`THROW` out of the order or key word is passed on, the records a
permutation of the input, the scratch freed and the sorter ready (a
`THROW` with the library's own code, −4131, reads as invalid). One sort
at a time per sorter; separate sorters are independent; the library has
no state of its own.

**Speed** (this machine, 2026-11-12): 100,000 cells with keys below
1,000, 1.57 million comparisons, 0.17 s with `gforth` 1.0 and 0.31 s with
0.7.3.

**Tests** (`tests/lib/sort.fs`, in `make test-lib`; Gforth 1.0 and
0.7.3; loaded under `HEX`): the public words and hidden helpers; the
orders at their edges; the sorter's settings and every refusal (nothing
compared or changed); empty, one, two, sorted, reversed, all-equal,
duplicate and paired lists of up to 1,000 cells on both paths; every
list of up to 6 cells over 3 keys and 1,000 random lists of up to 200
cells under four cut-overs, each equal record for record and comparison
for comparison to a reference insertion sort and a reference copy of
`lf-lnorm-sort`'s merge sort, and merged lists of up to 2,000 cells equal
to the insertion sort's result; records of 1, 4 (both through
`sorter-u32s` and through `sorter-key!`), a cell, 24 and 100 address
units against the reference on their positions, the words after the
sorter untouched; the snapshot's three insertion sorts, copied from
`env-snapshot.fs`, against the library byte for byte on 200 random lists
of up to 80 records each, under two cut-overs; the cut-over (no heap block held at 32 records, one
at 33); 100,000 random records against a counting sort, within
n·⌈log2 n⌉ comparisons, and 100,000 nearly sorted ones against the
insertion sort; the caller's buffer, used with the heap refusing; a
refused scratch (full, the records unchanged, nothing held, the sorter
ready); the return stack, the caller's cells and the constant depth at
which the order is called; orders whose results are large or that use
the return stack; order and key words that leave two results or none
(invalid, a permutation, nothing held); `THROW`s at three points (passed
on, a permutation, nothing held, the sorter ready); nested sorts with
the same sorter (refused) and another one; orders with a budget, equal
call for call to the references, and orders at random (a permutation);
the header's example; unsigned 32-bit values with bit 31 set. 23 planted
faults (`lib-sort-…` in `tests/mutants/faults.toml`: stability on each
path, the cut-over, a lost run rest, the output cursor, the scratch's
freeing, the busy flag, both depth checks, the buffer's size, the full
outcome, the merge width, the rotation's parts, the helpers made public,
the count's check, a zero order, the key word skipped, `sorter-u32s`
reading a cell, a swallowed `THROW`, `sort-unsigned` signed), each
caught.

**Sorts in `src/` that could use it** (2026-11-12; changing them is
kernel work under the owner's approval, or another agent's front end):

| Where | Kind | Equal keys |
| --- | --- | --- |
| `src/kernel/env-snapshot.fs` `entry-sink`, `look-sort` (213–218; also `env-layers.fs` 329) | insertion; 8-byte (key, answer) pairs by the little-endian key, unsigned | the lists are distinct by key; a stable sort keeps the bytes in any case: `8 ' sort-unsigned` with `' u32-le@ sorter-key!` |
| `env-snapshot.fs` `dep-sort` (324–330; `env-layers.fs` 326) | insertion by shifting; little-endian 32-bit slot numbers, unsigned | equal values are equal bytes: `4 ' sort-unsigned` with `' u32-le@ sorter-key!` |
| `env-snapshot.fs` `o-sink`, `o-sort` (386–391) | insertion; name numbers by content (`o-order`) | equal content is the same name: `' o-order sorter-cells` |
| `src/kernel/level-normalize.fs` `lf-lnorm-sort` (207–264) | insertion up to 32, else bottom-up merge through slab cells; one unit of fuel per comparison | only structurally equal levels tie; the library's comparisons are the same calls |
| `src/kernel/level-substitute.fs` `lf-cells-sort` (65–85; used at 256 and by `mixed-level-substitute.fs` 303) | heapsort of signed cells, no scratch, not stable | the reached node indices are distinct; the library would need scratch above 32 |
| `src/front/level-normalize.fs` `ln-insert`, `ln-sort` (121–137) | insertion by shifting; levels by `normLt` | only structurally equal levels tie |
| `src/import/ndjson-emit.fs` `member-insert`, `members-sort` (216–225) | insertion; mdata's key tokens by their text | two equal keys are refused as invalid |

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

## Signed big integers

`src/lib/bigint.fs` (plan step FE1i-4, 2026-11-13; design
[FE1I_AUTOMATION.md](../design/FE1I_AUTOMATION.md), section 5.2): Lean
4.35.0's `Int` for `by-omega`'s coefficients and `by-decide`'s `Int`
literals, over `bignum.fs`. Untrusted; the kernel does not use it (Lean's
kernel computes on `Nat` literals only, and reduces `Int` operations to
them through their definitions).

**What it computes**, as Lean's definitions in `Init/Data/Int` say (pinned
toolchain: `DivMod/Basic.lean`, `Gcd.lean`, `Pow.lean`, `Basic.lean`). Lean's
`/` and `%` on `Int` are `Int.ediv` and `Int.emod` (the `Div` and `Mod`
instances, lines 111–118); `Int.div` no longer exists in 4.35.0 (checked:
`#check @Int.div` is an unknown constant). `Int.tdiv`, `Int.fdiv` and
`Int.bdiv` are not provided: `omega` does not use them.

| Lean | Word | Result |
| --- | --- | --- |
| `a + b`, `a - b`, `a * b`, `-a` | `bigint+ bigint- bigint* bigint-negate` | as usual |
| `a / b` (`Int.ediv`) | `bigint-ediv` | ⌊a / b⌋ for b > 0, ⌈a / b⌉ for b < 0; a / 0 = 0 |
| `a % b` (`Int.emod`) | `bigint-emod` | a − b (a / b): 0 ≤ a % b < \|b\| for b ≠ 0; a % 0 = a |
| `Int.bmod x m`, `m : Nat` | `bigint-bmod` | r = x % m, then r if r < (m + 1) / 2, else r − m; x bmod 0 = x |
| `Int.gcd a b : Nat` | `bigint-gcd` | gcd(\|a\|, \|b\|) |
| `a ^ e`, `e : Nat` | `bigint-pow` | a^e; a^0 = 1 |
| `Int.natAbs`, `Int.toNat` | `bigint-natAbs`, `bigint-toNat` | \|a\|; a, or 0 for a < 0 |
| `Int.sign`, `compare` | `bigint-sign`, `bigint-compare` | −1, 0 or 1 (cells) |

The same in the three forms, for a negative dividend: mathematically
⌊−12 / 7⌋ = −2 and −12 − 7·(−2) = 2; in Lean `(-12 : Int) / 7 = -2` and
`(-12 : Int) % 7 = 2`; in Forth `s" -12" ar decimal>bigint drop s" 7" ar
decimal>bigint drop ar bigint-ediv` gives the integer −2 (the header's
example prints both).

**Design.** An integer is the address of a sign cell, −1, 0 or 1, followed
by its magnitude, a `bignum.fs` number; the sign is 0 exactly for 0, so
each integer has one form (`bigint-valid?` checks this in O(1)), and
`bigint-magnitude` is the magnitude in place. Every result is built in a
four-cell record claimed at the arena's top (the result's sign, the arena
and the operands): the magnitude is made above it with `bignum.fs`'s
operations, any intermediate numbers above that, and at the end the
magnitude is moved down so that the record's place becomes the integer
(its first field is the sign cell); a failure gives back the record and
everything above it. Natural-number results take the record's place the
same way. A negative quotient is ⌈\|a\| / \|b\|⌉ = (\|a\| − 1) / \|b\| + 1,
a negative dividend's remainder \|b\| − (\|a\| mod \|b\|) or 0, as Lean's
`negSucc` cases; `bmod` keeps r when r < m − r (both say 2r < m) and
otherwise gives −(m − r). The number 1 these steps use is made in the
arena, so the library has no data of its own. Operands are checked as
`bignum.fs`'s are (well formed, not reaching into the arena's free part,
a sound arena record) before anything is claimed, so invalid input wins
over no room; so is text read by `decimal>bigint` (review L1: text in the
free part would be overwritten by the build before it is read).

**Tests.** `tests/lib/bigint.fs` (loaded under `HEX`): the
representation, every word on signs and zero, Lean's documented examples
of `/`, `%` and `bmod`, `bmod`'s boundary 2r = m − 1, m, m + 1, carries
across limbs at 2^64, 2^300-size values, the most negative cell, every
kind of malformed text, malformed, released and straddling operands and
texts and a corrupted arena (invalid, nothing made), the bit limit, every
room from 0 to 240 cells between guard cells for every operation (from 0
to 80 for printing), no heap use (`tests/support/heap-watch.fs` refuses
the next allocation and it stays pending), both stacks balanced, operands
unchanged; every block of the module runs (289 of 289, Gforth 1.0's
`coverage.fs`). `tests/lib/bigint_differential.py` prints 13 results per
integer pair with `tests/lib/bigint-cases.fs` (7,906 edge pairs and seeded
random ones up to 3,600 bits, a quarter a = qb + r) and requires each line
to equal a model that follows Lean's definitions case by case
(`make test-bigint`: 2,000 random pairs); a self-test shows that the
comparison refuses the same lines with one value changed; then it runs the
header's example and checks the exact interface from a folder outside the
project. `make reference-bigint` runs
pinned Lean on the same 17,906 pairs (10,000 random) as a program whose
source holds them (so the Lean cache keys on them): Lean's own `Int`
gives the same lines as the Forth library and the model; then 300 of the
model's results as `example … := by decide +kernel` are all proved by
Lean's kernel and all 300 with the value changed are rejected. On
Gforth 1.0 and 0.7.3 (64-bit hosts only). Planted faults: 17 `fe-bigint-…`
entries in `tests/mutants/faults.toml`, each caught (the design's
`fe-bigint-ediv-sign` by the comparison with pinned Lean: 1,655 of 8,206
pairs differ from Lean's own `Int`).

## The compact store

[ADR 0016](../adr/0016-compact-store.md) (accepted by the owner on
2026-11-03) designs the storage that lets LeanForth hold all of Mathlib:
16-byte expression records of four packed 32-bit fields, every distinct
record stored once and found by hashing, and two tiers, a shared read-only
input and a per-check scratch space. Its prototype was measurement code;
this is the production form, made on 2026-11-03 (plan tasks 1.1.5 and
6.2.0–6.2.2, library part; ADR 0016 C9 step 1). It is untrusted and **not
yet used by the checker**: moving the term, level and name stores onto it
is C9 step 3, a [kernel] no-behaviour-change task. Measurements are in
[Measured](#measured) below.

**Two layers.** The general part is in `src/lib/` and knows nothing about
Lean (AGENTS.md: standalone libraries); each file requires only what it
uses, keeps its helpers in `lf-lib-private` ([ADR 0010](../adr/0010-wordlists.md))
and documents its interface with an example in its header:

| File | What it gives |
| --- | --- |
| `slab.fs` | **Growable heap stores** (plan 1.1.5). A slab holds units of a fixed size (records, 32-bit fields or bytes) in one heap block that doubles by `RESIZE` up to a limit. `slab-room`, `slab-claim` and `slab-reserve` give *full* when the limit would be passed or the heap has no room, with the slab unchanged; *invalid* for a negative size or a slab that is not live. A check value seals the unit size, the limit, the block and its capacity (resealed when the block grows), so corrupting any one of them, the count or the generation fails closed. Units past the count are free space where a caller builds a candidate record (`slab-top`) and keeps it with `slab-commit`. Marks: `slab-mark`, `slab-rollback` and `slab-mark-valid?` refuse, as `store.fs` does, a mark of another slab, of another generation (a `slab-clear` since), of a poisoned slab, or stale because a rollback went below it; instead of per-record identities a slab keeps a stack of marked counts, strictly increasing, each with a serial that never repeats, so a mark is valid exactly while its entry is on the stack (ADR 0016 C3), and marks at one count share an entry |
| `htab.fs` | **Hash tables**: open addressing with linear probing over 32-bit slots holding a record number plus one; the owner gives hooks to recompute an entry's hash and to compare an entry with a key. `htab-ready` doubles the table before it would pass 3/4 full; `htab-remove` deletes by Knuth's Algorithm R, so every other entry stays findable whatever the order of insertions and growth; `htab-spread` rebuilds at the smallest power of two at most half full (C4), `htab-presize` grows ahead of known insertions; finds, compared slots and doublings are counted. `htab-freeze` makes a table read-only: finds in it write nothing (not even the statistics), so any number of tasks may find in it at once, and every change is refused; `htab-live?` checks a table's block and sizes |
| `hash32.fs` | Murmur3's 32-bit finaliser (`hash-fmix`), `hash-step`, and FNV-1a over bytes (`hash-bytes`), equal on 32- and 64-bit hosts (C4) |
| `cons.fs` | **Hash-consed sets in two tiers.** A set keeps each distinct record once, named by a number; a class gives the record size, a limit of numbers and three hooks (rehash, compare, record span). Building follows one protocol: `cons-room` (room for the candidate and its text, the table ready), write the candidate at `cons-top`, `cons-find` (an equal record's number, or the empty slot), `cons-commit` (full at the class's limit; two spare units let an existing record be found at the limit) and `cons-text,`. A set can extend a *sealed* set that extends none (`cons-extend`, `cons-base?`; so at most two tiers): numbers continue after the under set's, and a find looks in the under set first, read-only (sealing froze its table; the find is counted in the extension, `cons-under-finds`), when the caller says every part of the candidate is an under record. A candidate's text goes into the set's key with `cons-key!`, which keeps it as an offset when it lies in the set's own byte slab, and `cons-room-key` finds it again after the slab moved. `cons-mark`, `cons-rollback` (which also takes the given-back records out of the table), `cons-reset` (emptying the table, or forgetting the records one by one when they are few, so a large table costs nothing per check) and `cons-seal` (read-only; the table spread, the slabs trimmed). Loading a set from a file (a snapshot): `cons-load-room` gives room for the records, written by the caller in order into the slab's free space, and builds the table now at its sealed size; each record, checked by the caller, is entered with `cons-adopt` (invalid for a record equal to an earlier one, full rather than a probe that never ends when the table has no room). `cons-entry?` checks a number exactly: in range and found in its table |
| `pools.fs` | Two classes: **tuples**, interned lists of 32-bit numbers of any length, built in steps (`tuple-start`, `tuple-add`, `tuple-end`; plan 6.2.0's variable-length universe and parameter lists, no fixed limit), and **texts**, interned byte strings (`text-intern`, `text@`) |
| `module.fs` | ADR 0010's `lf-lib` and `lf-lib-private` wordlists and `module-open`/`module-close` |

The Lean layer is in `src/core/compact*.fs` (Lean's data model, so not in
`lib/`). A **tier** (`compact-tier.fs`) groups five sets: names, levels,
tuples (universe arguments and parameter lists), texts (literals) and
expressions. `tier-init` (`compact.fs`) makes an input tier whose number 0
is the anonymous name and level zero; `tier-seal` makes it read-only;
`tier-extend` makes a scratch tier over it; `tier-mark`, `tier-rollback`
(checking all five marks before changing anything) and `tier-reset` work
on scratch tiers. Records are ADR 0016 C1's: `/quad` with the fields
`quad-head` (tag in bits 0–4, payload in 5–31), `quad-a`, `quad-b`,
`quad-data`, read and written only through `u32@` and `u32!`. Builders —
`name-str`, `name-num`, `level-succ`, `level-max`, `level-imax`,
`level-param`, `expr-bvar`, `expr-sort`, `expr-const`, `expr-app`,
`expr-make` (any kind but `letE`, with `lam-head`, `pi-head`, `proj-head`),
`expr-let`, `expr-nat`, `expr-str`, `expr-fvar` — check every record when it
is built (C8: children are records of the tier, unused fields are 0, fields
fit 32 bits, a constant's list holds only levels) and compute its data word
as Lean's `Expr.mkData` does (loose bound-variable range, universe-parameter
and free-variable flags, depth capped at 1023). A constant's payload is kept
out of its key, for the declaration C4 resolves at sealing. Limits, each
*full*: 2²⁷ names, a bound variable's range of 2²⁰ − 1 (Lean's), 2³² − 1
numbers per family, name components under 2²⁷ bytes and numeric components
up to 2³² − 1. Accessors (`expr-tag@`, `expr-a@`, `expr-body@`,
`name-text@`, `level-params?`, …) are unchecked; `expr-valid?`,
`name-valid?` and `level-valid?` check a handle.

```forth
require src/core/compact.fs
create input /tier allot   create check /tier allot
16 input tier-init drop
name-anonymous s" Nat" input name-str drop
s" succ" input name-str drop constant nat-succ
input tier-tuples tuple-start drop
input tier-tuples tuple-end drop constant no-levels
nat-succ no-levels input expr-const drop constant succ
0 input expr-bvar drop constant x
succ x input expr-app drop constant succ-x
input tier-seal drop  input check tier-extend drop
succ x check expr-app drop succ-x = .
succ succ-x check expr-app drop .
succ-x check expr-data@ data-range .
check tier-reset drop  check tier-free  input tier-free
```

prints `-1 3 1`: rebuilding `Nat.succ #0` in the scratch tier finds the
input's own record, a new term gets the scratch tier's first number (the
input holds 3 expressions), and `#0` is loose in it. Each word gives an
outcome, dropped here; a caller checks every one.

**Speed and the generic layer.** The library calls the class's hooks
through `EXECUTE`, about once per record compared; the Lean layer checks
each candidate through a table of one word per tag, given the candidate's
address. A first version that recomputed the candidate's address in every
helper was 1.6 to 2.5 times slower than the prototype; passing the address
and computing the data word on the stack brought it to the prototype's
speed or within 22% of it (below).

**The importer stage** (C9 step 2, 2026-11-03; plan 3.2.1, 3.3.1 in
part): `src/import/stage.fs` and `stage-records.fs` read an export through
the NDJSON reader, checked against its manifest by default, into an input
tier, with every declaration as a 32-byte record (C2: kind and flags,
name, universe parameters, type, value, height, a tuple of the kind's
other data such as `all`, an inductive type's counts and constructors or
a recursor's rules, and the previous declaration of the same name), the
name-to-declaration array (C4), and constants resolved when the tier is
sealed (C4: a constant's payload names its declaration when exactly one
has its name; a constant no declaration names makes sealing invalid). A
failed read rolls the stage back to empty; a byte limit makes it stop as
*full*; an `mdata` expression, a kind the store does not support yet, is
staged without its data under its own tag, and every declaration that
holds one is marked. Its interface, outcomes and measurements are in
[NDJSON_READER.md, "Staging"](NDJSON_READER.md#staging-into-the-compact-store).
`src/main.fs` loads it; the checker does not read it yet (C9 step 3).
A scratch tier owns heap memory, so as a checker-context member it needs
a teardown word (below, *Rules for converted modules*); since 2026-11-03
`context.fs` has that hook. `tests/support/compact-load.fs`, the test
loader, now loads through the stage.

**Not yet.** Caches and substitution memos (C4, plan 6.4) are C9 step 6;
moving the checker's term, level and name stores onto the compact store
is C9 step 3.

### Tests

- `tests/lib/hash32.fs`, `slab.fs`, `htab.fs`, `cons.fs` and
  `tests/core/compact.fs` (in `make test`, loaded under `HEX`): every
  limit at and one past its bound, every refusal of a mark, every sealed
  field corrupted, growth keeping contents, collisions forced (a hook with
  one hash for all entries; texts, names and lists with equal hashes:
  `costarring`/`liquid` and `glbvs`/`yacxa` under FNV-1a, two two-item
  lists found by search), rollbacks taking entries out, invalid handles,
  data words and depth caps; randomized models of slabs (60,000 steps),
  tables (8,000), sets in two tiers with a four-valued hash (15,000) and
  applications in two tiers (9,900).
- The round trip (`tests/core/compact-verify.sh`): an export is staged
  into an input tier by the importer stage (with its manifest, or
  `--unchecked` for a fixture without one) and every record, the
  metadata, names, levels, expressions and declarations, is printed back
  from the store, references turned into export indices; the lines must
  equal the reader's own dump (`tests/core/ndjson-dump.fs`), family by
  family, and the dump may hold nothing else. `make test` runs it on the
  five pinned reference exports and the six other fixture exports of
  `tests/`, `make check` on `Init` exported by the pinned `leanexport`
  (`tests/core/compact-init.sh`, which writes its manifest). The stage's
  own tests are in [NDJSON_READER.md](NDJSON_READER.md#staging-into-the-compact-store).
- `tests/core/compact_faults.py` (`make check`): 27 faults planted in a copy
  (operands ignored by hash-consing, texts or lists compared by length or
  hash only, a rollback that keeps the count or the table entries, a reset
  that keeps old marks valid, two off-by-one 32-bit fields, growth losing
  contents, Algorithm R moving an entry home, a body range not lowered, an
  uncapped depth, Lean's bound-variable limit off by one, a constant's
  payload in its key, a scratch build never looking in the input, a `letE`
  body record taken as a child, a sealed set accepting records, a class
  limit off by one; and, after the review of 2026-11-03, a set over a
  sealed extension (three tiers), a find counting in a frozen table,
  sealing without freezing, an own-slab text keeping its old address, an
  unclamped slab limit, a bound-variable index compared after `1+`, a list
  span that wraps, a commit past the limit): each is caught. The review's
  eight are also in `tests/mutants/faults.toml`.
- Since the review, the tests also show that lookups and builds through a
  scratch tier leave every byte of the sealed input's records and table
  slots as they were; that a sealed scratch tier cannot be extended; that
  a component or text taken from the tier's own byte slab is read again
  after the slab moved (moved by hand, the old block overwritten); and the
  arithmetic at the bounds a 32-bit host reaches at 2³² (a class whose
  limit times its record size passes the cell, a commit at and past the
  class's limit, a bound-variable index of 2³² − 1 read as the cell −1,
  a list length of 2³² − 1). No 32-bit host was available to run them on.

### Measured

2026-11-03, this machine (10 logical cores, WSL2) shared with other agents'
test runs (load average 2–4), `gforth-fast` of Gforth 1.0 unless stated,
one thread; times vary by about ±20% between runs. The loader was the
first version of `tests/support/compact-load.fs` (`compact-measure`),
before the importer stage: names, levels and expressions only, no
manifest. The expression table is pre-sized where stated
(`htab-presize`), every other table grows from 2¹²; `/usr/bin/time` gives
wall time and peak memory. The prototype's figures are ADR 0016's. The
importer stage's figures, with declarations and the manifest check, are
in [NDJSON_READER.md](NDJSON_READER.md#staging-into-the-compact-store).

| | Prototype | Library |
| --- | ---: | ---: |
| `Init`: load and seal, tables growing | 14.4 s | 15.5 s |
| `Init`: load and seal, expression table pre-sized (2²⁴) | 12.1 s (2²³) | 11.1 s |
| `Init`: peak memory, growing / pre-sized | 228.6 MB (whole run) | 249 MB / 213 MB |
| `Init`: input tier, bytes in use | 142.8 MB | 175.3 MB ¹ |
| `Init`: every declaration's name looked up by its text | 0.032 s | 0.087 s ² |
| `Init`: round trip of names, levels, expressions (SHA-256) | `062a404d…`, `a37233ac…`, `83d1d3ca…` | the same three |
| Mathlib: load and seal, expression table pre-sized (2²⁸) | 256 s | 221 s |
| Mathlib: load, tables growing | 328–383 s | not run |
| Mathlib: input tier, bytes in use | 2.94 GB ³ | 2.94 GB |
| Mathlib: peak memory | 3.32 GB pre-sized load; 4.16 GB whole run | 3.36 GB |
| Mathlib: 729,263 declaration names looked up by text | 0.61–0.69 s | 1.18 s, all found ² |

¹ ADR 0016 C4 seals the expression table at most half full: 2²⁴ slots
(36%), 33.5 MB more than the prototype's 2²³ (73%).
² Each lookup goes component by component through a scratch tier over the
sealed input, building each component as a candidate (room, head, hash)
before the read-only find: about 0.35 µs per component against the
prototype's 0.14. Lookups by text are not on the checker's path, since
constants are resolved when the input is loaded (C4).
³ The prototype's figure includes its declarations and name-to-declaration
array (40 MB), which the library does not have yet; the library's name
table is 2²⁴ slots (25% full) where the prototype's was 2²³.

Mathlib's families after the load (records, text, table): names 4,241,559
(67.9 MB, 19.8 MB, 67.1 MB), levels 47,806 (0.8 MB, table 0.5 MB), lists
152,089 in 703,180 fields (2.8 MB, 2.1 MB), literals 24,845 (0.2 MB,
3.2 MB, 0.3 MB), expressions 105,894,257 in 106,136,340 records
(1,698 MB, 1,074 MB at 39%). Inserting every expression into the
pre-sized table compared 0.33 occupied slots per insertion.

**Building an expression** in a scratch tier over a loaded, sealed `Init`
(`tests/core/compact-bench.fs`, the prototype's `bench.fs` cases, input
table 2²⁴ slots, 36% full; nanoseconds per build):

| Build | Prototype | Library |
| --- | ---: | ---: |
| app(a, f): input children, so the input's table first (mostly a miss), then the scratch table; new | 646 | 626 |
| app(previous, f): a scratch child, so the scratch table only; new | 245 | 252 |
| app(f, a): found in the input | 351 | 427 |

Each build checks its record (C8), computes its data word and, for a new
record, keeps it; the prototype did the same work without the checks.

## Missing for a usable checker at Mathlib scale

- **Capacity and memory.** Since ADR 0016 C9 step 3 (2026-11-03) the
  checker's term, level, name, reference and input stores are heap stores
  (`store-heap-init`, below) whose capacities are settings of each context
  (`lf-term-capacity!` and the like; defaults 64, 64, 64, 32 and 32), and
  per-index side data lives in columns that grow with them
  (`src/lib/store-columns.fs`). A staged export's names stay in its
  shared input tier (`lf-name-attach`); since compact-store plan step S5
  its expressions are read in place too (the term store's input view,
  `src/core/terms.fs`; lets and projections too since its parts 4-5),
  only an mdata expression and the terms above one copied, while its
  levels and declarations are copied into the context's stores
  (`src/import/feed.fs`; the copy of every expression, about 80 bytes per
  term node with the columns, is gone). Walk stacks, frames and binder contexts
  grow in the heap (plan task 6.2.0): no pass recurses on the Forth stacks,
  and `lf-walk-room` is only a walk's first room.
- **Hashing and hash-consing.** Under a name view the checker's names are
  the input tier's, interned and found by hash; the environment finds a
  name's declarations through the input's name index. Terms and levels of
  the checker's own stores are not shared by content (their identities and
  stamps are what handles check; ADR 0016 C9 step 6).
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
task has an owner token, `lf-owner`: 0, or the job it is running, or
`context-check-owner` while it runs a check outside the job pool (the
checked environment's serial driver; `context-in-job?` counts such a
check as a job). A task may select only a context whose owner is its own
token, so the main task uses only idle contexts, a job only its own and
such a check none; an owned context cannot be freed. Contexts are made,
freed, claimed and released only outside jobs: inside a job or such a
check, `context-new`, `context-free` and `context-release` abort, and
`context-claim ( owner context -- flag )`, which the job pool uses to
give a job its context, gives false without reading the address. Running
a word with `context-catch ( i*x xt -- j*x ior )` is `CATCH` that
restores the current context afterwards, whatever the word selected or
threw; it does not restore the owner token. A context's address is its handle,
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
| a frames record set up with `frame-init` after its visitor, such as `' lf-mbeta-visit lf-mbeta-frames frame-init` | `' lf-mbeta-visit context-frames: lf-mbeta-frames` (declared after the visitor, which reaches the record through its frames argument; its stack is freed with the context) |
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
- A member may own heap memory only with a teardown word (the release
  hook, since 2026-11-03; [ADR 0009, Amendment 1](../adr/0009-reentrant-state-and-parallel-checking.md#amendment-1-2026-11-03-context-members-that-own-heap-memory)):
  `' name-free context-teardown`, declared while loading like a member.
  `context-free` runs every teardown word, newest first, in the context it
  frees, then frees the context; `context-new` runs them when a setup word
  fails. A teardown word frees exactly what its member holds, also after a
  `THROW` and on a member still zeroed (free only the blocks you find,
  zero what you freed), and selects, makes and frees no context. Each runs
  balanced under `CATCH`; one that throws or leaves the stack changed
  makes `context-free` give its code, after every other teardown has run
  and the context is freed. Before 2026-11-03 members held no `ALLOCATE`d
  memory at all.

  ```forth
  /tier context-record: check-scratch          \ a scratch tier (ADR 0016 C3)
  : check-scratch-free ( -- ) check-scratch tier-free ;
  ' check-scratch-free context-teardown
  ```
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

- A pass on a frames record (`frame.fs` above) holds a constant number
  of host-stack cells whatever its depth: its loop, one step and what the
  step calls, and the few loops a step may nest (beta's runs
  instantiate's, which runs shift's). A module states that need while it
  loads with `context-need ( data-cells return-cells --
  )` (`lib/context.fs`; the largest of each is kept, `context-needs` gives
  them, and a need stated after the layout is sealed aborts).
  `pool-start`, and so the first `job-submit`, refuses with
  `task-stacks-small` (-4101), starting nothing, unless `job-stacks-cover?
  ( data-cells return-cells -- flag )` holds for that need: the workers'
  depths less `task-slack-cells`, or on the serial host the host's stack
  sizes less the slack (a host that does not report a size through
  `ENVIRONMENT?` is not checked). So lowering `task-data-cells` or
  `task-return-cells` with `TO` below the need is caught whichever of
  `task.fs` and the kernel loads first. The checker states three needs:
  beta with its nested instantiate and shift passes (`mixed-beta.fs`,
  1,216 return and 960 data cells), Lean's normalize in a level
  comparison (`level-normalize.fs`, 576 and 384: at most 7 return and 3
  data cells per node of the level store, 6.5 and 2.5 measured, and 1
  and 2 per name component, plus 64), and inference, which can nest
  either at its deepest level, never both (`mixed-infer.fs`, 1,728 and
  1,280: at most 8 return and 5 data cells per level, measured by stack
  painting along its five recursion paths and the two of its rejection
  analysis (plan task 2.2.1; the D5 path needs 8) on Gforth 0.7.3 and
  1.0, which agree, times `lf-term-capacity` levels, plus the larger
  nested need, beta's; the definition probe nests no deeper;
  `tests/core/level-deep.fs` and `tests/core/infer-deep.fs` paint the
  deepest normalize, alone and at the deepest inference: 408 and 149
  cells for 62 levels alone, 368 and 136 added to an inference of 229
  and 85). The test job's 500-frame pass used 1,004 return-stack and
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

# Forth library inventory

What reusable Forth facilities exist, how mature they are, and what the
product will need that does not exist yet. Everything listed is untrusted
experimental code unless stated otherwise; none is a reviewed kernel
component. Measured 2026-11-02 at commit `4779924`; library entries updated the same day. Modules are in
`src/core/` (data model) or `src/kernel/` (checker passes) unless named
with another folder ([source layout](../../src/README.md)); the superseded
variants were retired on 2026-11-02.

## What each library documents (owner, 2026-11-13)

Every library's section here gives, as [Sorting](#sorting) does: **algorithm** (what it does and why that method);
**genericity** (what the caller supplies: comparison or key words, record sizes, capacities; what it assumes of the
data); **scaling** (cost for small and large inputs, cut-overs, scratch memory, recursion or host-stack depth);
**measured speed** at a small and a large size, with the machine and Gforth version; and **callers and their mix**
(each calling module and the sizes it passes, measured on a real run such as Init or Mathlib, updated when a caller
is added). The library audit of 2026-11-13 (plan 9.4.8) listed which libraries lacked which part; since
2026-11-18 every library has all five, in [Measured profiles](#measured-profiles-2026-11-18) (`make lib-bench`
re-measures the speeds).

## What exists

| Facility | Module(s) | What it is | State |
| --- | --- | --- | --- |
| Bounded record stores | `src/lib/store.fs` | `store:` defining word: a fixed number of fixed-width records with an allocation count, a reset generation that saturates to a poisoned state, an identity per record that never repeats, and a sealed shape so header corruption fails closed. `store-size` and `store-init` make the same store in memory obtained at run time (`ALLOCATE`, or a region of a context); `store-plan?` also refuses a size that would not fit in a cell. **Marks** (plan task 1.1.3): `store-mark ( mark store -- outcome )` records the store, its generation, serial and count in a `/store-mark` record the caller provides (fields `mark-store`, `mark-generation`, `mark-serial`, `mark-count`); `store-rollback ( mark store -- outcome )` restores the count, giving back every record allocated since, and never rewinds identities; `store-mark-valid? ( mark store -- flag )` tells whether it would. A rollback is refused, invalid with nothing changed, for a mark of another store, from another generation (a reset since), above the current count, of an invalid or poisoned store, or stale: records below its count must be older than the mark and the one at its count newer, so a mark below which an earlier rollback went and records were allocated again is refused. Marks are not capabilities: a forged record that passes these checks is accepted. **Heap stores** (plan task 1.1.5, ADR 0016 C9 step 3, 2026-11-03): `store-heap-init ( capacity width base store -- outcome )` puts the header in the caller's memory (it may move, as a context member does) and the block of identities and records on the heap; `store-grow ( store -- outcome )` doubles the block, at least 16 more records, up to the limit, when every record is in use (full at the limit, with no heap, or when the test hook refuses; nothing changed then); `store-limit! ( limit store -- outcome )` sets the limit (at least the count; a larger block shrinks); `store-most ( width -- n )`, the most records of a width that fit with their identities and the header in max-n bytes, the limit of a store that grows as the heap allows (reuse-d, 2026-11-19: was `author/form.fs`'s `lfa-store-limit` and `front/mvars.fs`'s `mv-limit`; one division); `store-heap-free`. The block and the limit are sealed shape fields; marks stay valid while the block grows; an address from `store-slot` is valid only until the next growth; `allocate0 ( u -- addr ior )`, ALLOCATE of zeroed memory, is `blocks.fs`'s (moved from `context.fs` in reuse-out-2, then beside `block-zeroed` in ROUT3), which this file requires | New 2026-11-02; used by the term, level and name stores; heap stores (the checker's five stores) tested in `tests/lib/lib.fs` (growth, limit, marks across growth, shrinking, freeing); unit-tested in `tests/lib/lib.fs`, run-time stores in `tests/lib/context.fs`; marks 2026-11-02 in `tests/lib/store-mark.fs` (every refusal, and 20,000 random operations against a model that kills a mark when the count drops below it or the store is reset), used by the checked environment's input (`src/core/input.fs`); the hand-written count saving in the existing modules is not converted yet |
| Tagged nodes | `src/lib/node.fs` | `BEGIN-STRUCTURE` record of tag and two fields, with whole-node `node!`/`node@` and `node-new`/`node-read` on a store | New 2026-11-02; terms and levels |
| Range checks | `src/lib/bounds.fs` | `between?` and `upto?` (inclusive, signed, never wrapping) and `cells-zero?`; `index? ( i n -- flag )` (0 ≤ i < n, false for every i when n ≤ 0, where `0 n within` takes any i ≥ 0), `cells-index ( x addr n -- i true \| false )` and `cells-has? ( x addr n -- flag )` (the first of n cells holding x); `cells= ( a-addr1 a-addr2 n -- flag )` (n cells compared cell by cell) and `in-ranges? ( x a-addr n -- flag )` (x within one of n (lo, hi) pairs, a character class) ([below](#stacks-outcome-loops-and-index-checks)); `cell-counted, ( c-addr u -- )` lays down a cell-counted text (its length in a cell, then its bytes; moved here from `bytes.fs` in ROUT3, beside its reader) and `cell-count ( addr -- addr' n )` reads one back, as `count` (reuse-out-2: four and nine copies); `cell-counted! ( c-addr u addr room -- flag )` puts a text into such a buffer of room bytes (false, nothing changed, when it is longer) and `cell-counted+! ( c-addr u addr -- )` appends one (ROUT3: the run record's and the replay's text buffers, six readers and five writers); `cell-counted-left ( addr room -- n )` (the bytes still free) and `cell-counted+? ( c-addr u addr room -- flag )`, an append only when it fits (false, nothing changed, otherwise), so the caller drops, clips or fails (reuse-b, 2026-11-19, review R3 of the third whole-code pass: the progress line's `ck-pl+`, the IR line's `pv-copy`, `pv-clipped` and `pv-append`, the snapshot information's `cli-info+`; one `MOVE` of u bytes, no memory, no recursion; reuse-c, 2026-11-19: also the step log's `lsl-pos+` (24 bytes) and the run record's `rr-name-sink` (1,024 bytes), and both bounded writers compare a length unsigned, so a u with the top bit set never fits, Forth review of reuse-b, 8); the array words `cell-at@ ( i a-addr -- x )`, `pair-at ( i a-addr -- addr )` and `record-at ( i size a-addr -- addr )` (reuse-d, 2026-11-19, plan 9.4.8k: element i of a cell array, the address of pair i or of record i; unchecked, one multiply and add, no memory; callers the front end's variable and parameter arrays, `ac-x`, `ib-x`, `in-x`, `lp-name`, `lp-arg`, `lbd-sname@`, its level and spine pair arrays, `lmap-at`, `mv-head-cell`, and the command line's path and layer records, `cli-path`, `ck-layer-id`, each at most a few hundred entries in a check of Init), `cell-pair@ ( addr -- x1 x2 )` and `cell-pair! ( x1 x2 addr -- )` (two adjacent cells in memory order, the reverse of `2@` and `2!`: a record's neighbouring fields read or written together where one is also used alone or the layout is fixed; cleanup-families-2, 2026-11-19, [below](#stacks-outcome-loops-and-index-checks)), `cell-triple@ ( addr -- x1 x2 x3 )` and `cell-triple! ( x1 x2 x3 addr -- )` (the same for three adjacent cells), `cell-tally ( i a-addr -- )` (one more in cell i of an array of counts: the elaboration data's record counts, `print-lf.fs`'s refusal counts), `first-nonzero ( x1 x2 -- x )` (the first failure of two steps that give 0 for success: the contexts' and the job pool's iors, `assign-check.fs`'s images; was `ior-earlier`, `ior-first`, `ac-first-fail`), `first-or-second ( x1 x2 n -- x )` (x1 for n = 1, else x2: a binary node's part by number, the log view's `lf-lv-part-of`, and a choice between two levels, the kernel's `lf-lmk-pick`; extracted from their exact copies by `check-duplicates.py --extract`, cleanup-families-1, 2026-11-19), `one-of2? ( x a b -- flag )` and `one-of3? ( x a b c -- flag )` (x equal to one of two or three values, 36 callers; cleanup-families-3, profiled below the pair and triple words) and `epoch+ ( generation -- generation' )` (a generation one step on, saturating to -1; moved from `store.fs`, and `slab.fs`'s copy `slab-epoch+` gone; callers the store and slab resets, the level scope and the signature probe) | New 2026-11-02; `index?`, `cells-index`, `cells-has?` 2026-11-13 (plan 9.4.8a) in place of 9 `0 n within` checks and 5 cell searches; `cells=` and `in-ranges?` 2026-11-13 (batch `reuse-out`, plan 9.4.8k) in place of `memo-cells=`, the kernel's `lf-mls-cells=`, `lfa-pairs=`, `tr-among?` and `nt-among?`; `tests/lib/lib.fs` |
| Outcome vocabulary | `src/lib/outcome.fs` | ok, invalid, exhausted (out of fuel), unknown, rejected, unsupported and full (out of room: a store, work stack, frame, depth or size limit) (ADR 0008), with `ok?`, `outcome-sane`, `flag>outcome` and `room>outcome` (a validity or room flag as ok, else invalid or full), `visit-outcome` (the one rule for a visit bounded by fuel and room: no fuel is exhausted whatever the room, then no room is full), the continue-on-ok steps `ok-then?`, `ok-then2?`, `ok-then3?`, `ok-keep?` and `ok-keep2?`, `outcome-and` (two outcomes as one, the first failure), `outcome-steps` (a 0-ended list of steps run to the first failure; review FRI B6), `ok-and` and `ok-with` (a step run only while the outcome so far is ok, on the values below or on a value kept below; review FRK A), `no-result`, `no-result-flag ( outcome -- -1 false outcome )` (a failure of a step that gives a result and a flag; review ops-c1 B1, 2026-11-20: 45 uses in `src/front`, in place of reduce-nat.fs's `rn-failed` (2 calls, deleted), 30 of whnf.fs's 32 `wc-fail` calls, 5 of synth.fs's 8 `sy-none` calls, 6 of the 10 inline `-1 false rot` and discr-keys.fs's two `no-result false swap`; the 12 copies left, on refusal paths no unit test reaches yet (kabstract.fs's `kab-none`, two `wc-fail`, three `sy-none`, four `-1 false rot`), and the kernel's `-1 0 rot` are plan 9.4.8l AX), `outcome-text` (each outcome's name, for reports), the loops `ok-each ( i*x n xt -- i*x outcome )` and `ok-fold ( x n y xt -- x' outcome )` (a step for k = 0 … n-1 to the first failure), the tests over every index `all? ( i*x n xt -- i*x flag )` and `ok-all? ( i*x n xt -- i*x flag outcome )` (to the first false or failure) with their stop test `ok-true? ( flag outcome -- true | false outcome false )`, the tests over some index `any? ( i*x n xt -- i*x flag )` and `ok-any? ( i*x n xt -- i*x flag outcome )` (to the first true or failure, stop test `ok-found?`), `any-in? ( i*x lo hi xt -- i*x flag )` (the same over lo .. hi-1; ROUT3: the binder and note-label searches from an index), `outcome-first! ( outcome a-addr -- )` (a first failure kept in a cell), `ok-store ( x a-addr outcome -- outcome )` (a step's result stored only on ok), `ok-or-none ( x outcome -- x outcome \| -1 outcome )` (a result kept only on ok), `ok-apply ( x outcome xt -- result outcome )` (a step on a value made so far, -1 and the outcome otherwise; reuse-d, 2026-11-19: `elab-data.fs`'s `ed-body-name`, `infer.fs`'s two level reads, `unfold.fs`'s `uf-delta-beta` and the kernel's `lf-rn-named` (`core/nat-ops.fs`'s `lf-nat-named` since plan S3a), [kernel] in form; one test, one EXECUTE; cleanup-families-2, 2026-11-19: the refusal tail `ok-then? if X else no-result then` replaced by `['] X ok-apply` in 38 more words of the front end, the kernel's `whnf.fs`, `iota.fs`, `mixed-infer.fs` and `reduce-nat.fs` and `runs.fs`, and `infer.fs`'s steps chained on it), `ok-apply2 ( x1 x2 outcome xt -- result outcome )` (the same for a step of two values, both dropped on a failure, in place of `ok-then? if X else nip no-result then`: 25 uses, the kernel's `lf-whnf-delta-of`, `lf-whnf-reapply` and `lf-minfer-put-closed` among them; cleanup-families-2; speed, measured by the review of cleanup-families-2 (10^7 calls, Gforth 1.0.0): on `gforth` the same as the hand-written tail within noise, 77-90 ms both; on `gforth-fast` `ok-apply` about 1.7 ns more a call than the tail, 50-53 against 33-36 ms, `ok-apply2` 0-1 ns more; the kernel's sites run once per delta unfolding, closed instantiation or Nat step, each doing lookups and allocations), `ok-apply3 ( x1 x2 x3 outcome xt -- result outcome )` (the same for a step of three values, all three dropped on a failure, in place of the mid-word guard `ok-then? 0= if nip nip no-result exit then` before a step; cleanup-families-3, 2026-11-19: the front end's `ac-lam`, `lf-dt-cons`, `ed-entry-below`, `et-of-nat-value`, `fi-run`, `if-pi`, `sy-out-arg`, `lv-renamed-at` and `me-finish`, and the import's `ly-fam-expr-of`; tests against the hand-written guard for every outcome, faults `cf3-ok-apply3-keeps-one` and `cf3-ok-apply3-runs-anyway`) and `room-result ( x true \| false -- x outcome )` (a store's room flag as ok, or -1 and full), `2dup-under ( x1 x2 k -- x1 x2 x1 x2 k )` (a loop step's two values copied above its index) ([below](#stacks-outcome-loops-and-index-checks)) | New 2026-11-02; every core and kernel module uses it; the per-module status aliases were removed; the loops and `outcome-first!` 2026-11-13 (plan 9.4.8a) in place of 30 hand-written loops, the combinators `aux-each`, `aux-fold` (`fold-with`), `aux-then` and `and-then`, and 7 first-failure cells outside `src/kernel/`; `all?`, `ok-all?` and `ok-true?` 2026-11-13 (review reuse-1a B2) in place of 8 flag loops and 2 all-while-ok loops outside `src/kernel/`; `any?`, `ok-any?`, `ok-or-none`, `room-result` 2026-11-13 (batch `reuse-out`) in place of 6 any-loops outside the front end, 3 kernel any-while-ok loops, 2 `ok-or-none` and 10 `room-result` copies, with about 45 kernel loops moved onto `ok-each`, `all?`, `any?`, `ok-all?` (under the owner's [kernel] approval), and after review reuse-out (B1) 13 more kernel loops; `2dup-under` (S1) in place of 26 `>r 2dup r>` outside the front end; `ok-store` 2026-11-14 (review s2-unfold-a re-check L1) in place of 4 store-on-ok copies (`memo!`, `slab-push`, elab-data.fs's node fields, `ctor-idx.fs`'s binder name) |
| DAG walks | `src/lib/walk.fs` | `walk:` defining word: fuel, current node, one visitor cell and a bounded work stack in one record; `walk-run` drives a visitor and `walk-visit` reads and dispatches a node. A push without room is full whatever fuel is left (checked where the push happens), and a root that cannot be pushed means a corrupted capacity, which is invalid. `walk-size`/`walk-init` and `walk2-size`/`walk2-init` make the same records at run time. The walk words keep no state of their own; each module's walk records are members of the checker context, one set per context; `walk-context? ( walk -- x|0 )` (a paired walk's context, 0 otherwise) and `walk-children-unless ( first second walk xt -- outcome )`: children pushed unless a memo holds them checked (reuse-out-2: the audit's and the level substitution's copies; its helpers `walk-push-unless`, `walk-push2-unless` and `walk-children?` private since ROUT3, `walk-children` on `walk-children?`) | New 2026-11-02; level scope, Sort representation, session and handle audits use it |
| Passes on an explicit stack | `src/lib/frame.fs` | A frames record: fuel, visits in progress, the visitor (set once), a context cell (such as a binder depth), a job cell, and the pass's stack, a heap block that grows by doubling (plan task 6.2.0). A visit is a chain of steps `( ... frames -- ... frames next )` run by a loop (`frame-run`, `frame-loop`, `frame-steps`), never nested on the host's stacks: a step either asks for a child's visit with `frame-call` or `frame-under` (one context level deeper), naming the step that continues with the child's `( result outcome )`, or returns `( result outcome frames 0 )`; values kept across a child's visit go on the pass's stack (`frame-save`, `frame-restore`, `frame-pick`, `frame-drop`; up to `frame-spare` cells a visit, all its steps together; a save past the block throws `frame-overrun`, -4111, instead of writing outside it, for 0.5% more instructions on the trial workload). `frame-admit` says why a visit cannot open: an unsound stack is invalid, then no fuel left is exhausted, then a stack the heap cannot grow full (the fuel decides first); `frame-under` is full at context `max-n`. `frame-open` opens a visit of another kind (mixed-infer.fs: inference and the rejection analysis share one record), and `frame-open-or ( frames cont xt refuse -- frames xt | ... )` opens it after `frame-admit`, else runs the pass's refusal on the outcome (ROUT3: defeq.fs's and whnf.fs's copies), and a step may run a loop of its own on the same record. A busy record refuses a new budget or pass; `frame-reset` recovers after a THROW; `frame-free` gives the stack back. Host-stack use is a constant whatever the depth | New 2026-11-02, explicit stack 2026-11-04; the kernel's shift, instantiate, beta and opening passes, inference and the analysis, normalize, is_geq and level evaluation use it; unit tests and a randomized model test |
| Checker contexts | `src/lib/context.fs` | One `ALLOCATE`d record per worker for all of a check's mutable state ([ADR 0009](../adr/0009-reentrant-state-and-parallel-checking.md)), reached through the `USER` variable `lf-context` (a plain variable on hosts without Gforth's `USER`). Modules declare members while they load: `context-record:`, `context-store:`, `context-walk:`, `context-walk2:`, `context-frames:` (a frames record, set up with `frame-init`), and `context-setup` for set-up words; a refused declaration changes nothing. Each member's name is a colon definition that adds its offset, a literal, to `lf-context @`. Modules also state how deep their checks nest on the host stacks (`context-need`), which the job pool checks. `context-new`, `context-use` and `context-free` make, select and free contexts. Each context is idle or owned by one job; each task has an owner token `lf-owner` and may select only contexts it owns (the main task: idle ones); owned contexts cannot be freed. `context-in-job?` says whether the current task runs a job or a check; the checked environment's serial driver gives a check the token `context-check-owner`, so every in-job guard refuses it too. `context-claim` and `context-release` (the job pool's) are refused there as well. `call-balanced ( x xt -- )` runs a word above a cell and throws `context-unbalanced` (-4096) when the word changed the stack depth or that cell (the checked environment's serial driver uses it; `task.fs`'s `job-call` still has its own copy); `context-catch ( i*x xt -- j*x ior )` is `CATCH` that restores the current context afterwards. `context-slab:` declares a growable array member and `context-teardown` a word that frees a member's heap blocks with its context. The header lists the interface and gives an example; every other word is private (`lf-lib-private`, since 2026-11-12) | New 2026-11-02; ownership, frames members and atomic declarations 2026-11-02 after an independent review; every module of `src/core/` and `src/kernel/` keeps its state in it since 2026-11-02 (see the design below); tested in `tests/lib/context.fs`, including a randomized model with context switches at every step, and with real checker work in `tests/core/contexts.fs` |
| Job pool | `src/lib/task.fs` | `job-submit ( context xt -- job ior )` and `job-wait ( job -- ior )`: a fixed pool of long-lived workers (at most one per logical core, setting `task-workers`) fed from a bounded queue; POSIX threads with a mutex and two condition variables on Gforth 1.0, the cooperative `tasker.fs` on Gforth 0.7.3, and a serial path elsewhere (or when forced, for tests). A job's context is owned by the job until it is waited for. Wrong stack effects give `task-unbalanced`; stack overflows never report success (guard pages on 1.0, canary zones on 0.7.3); when the host refuses a worker (near its process limit) the pool runs with those it made, and is refused (`task-no-worker`) only when it made none (`spawn-limit!` makes the host refuse in tests); `job-wait` refuses job 0, a refused submission's handle. `job-stacks-cover?` tells whether the workers' stacks hold a recursion requirement, and the pool refuses to start with stack settings below the largest need modules stated (`task-stacks-small`). On Gforth 1.0 each worker owns its exception-backtrace and error-stack strings (a new task copies the creator's user area, and shared strings were corrupted by concurrent THROWs). Job rules: never parse or use `PAD` (one buffer for all tasks on Gforth 1.0), use `<# #>` text before the job yields (one buffer on 0.7.3), and restore `BASE` if a job changes it (a worker starts with the main task's). `job-wait-any ( addr n -- k )` waits for the first of several jobs (a scheduler that keeps one job per worker) and `pool-workers! ( n -- )` sets the pool's size for its next start. `task+! ( n addr -- )` adds to a cell that jobs on several workers add to without losing an addition (Gforth 1.0's `atomic+!@`, a locked `xadd`; its `+!@` is not atomic), a plain `+!` on the other hosts (2026-11-18, re-entrancy audit L1: the checker's test-build counter `lf-i2-misses`); test-only, a program that defines `task-cores-test ( -- n )` before the file loads gets n cores (`tests/cli/test_parallel_stress.py`: more workers than cores). Loaded by the parallel scheduler (`src/kernel/env-schedule.fs`, `check --jobs`) since 2026-11-11 | New 2026-11-02; pool replaced one thread per task the same day; `tests/lib/task.fs` and `task-serial.fs` compare jobs and interleaved contexts with serial runs for 1, 2 and all workers and reach every refusal, a host that refuses all or some workers among them; `task-overflow.fs` and `task-overflow-serial.fs` overflow both stacks inside jobs; `tests/lib/task-bench.fs` measures speed-up |
| Line reader and UTF-8 | `src/lib/bytes.fs` | `reader:` record over a Forth-2012 file: whole lines in one heap buffer that grows for long lines up to a limit, framing rules set by `reader-rules!` (2026-11-18: ordinary text by default; `reader-strict`, Lean's exports' framing, requires a final line feed and keeps carriage returns and a byte-order mark in the line for `text-framed` to refuse; only a line feed ends a line, so in ordinary text a file ending in a line feed and a lone carriage return has one more, empty, line, as Python's universal newlines read it), line numbers (`reader-line#`, 2026-11-18) and double-cell file offsets (`reader-position`); `utf8-length`, `utf8-valid?`, `utf8-decode` and `utf8-put` (RFC 3629, no overlongs or surrogates); `counted,` and `counted-next` (the next counted string of a table of them; `manifest.fs`'s copy `key-next` gone, reuse-d) and `counted-nth ( c-addr n -- c-addr' )` (the n-th, from 0: n steps, no memory; callers the elaboration data's messages and kind names and the manifest's record kinds, tables of at most 60 names); `fnv-step` and `bytes-mix` (an FNV-style mix of bytes into a hash, used by the checked environment's input fingerprint); `heap-claim` and `heap-release` now live in `blocks.fs`, which it requires. Uses Gforth's native `scan` behind an adapter, with a portable loop otherwise. Loads in decimal whatever `BASE` is, and restores it; `counted-or-empty ( c-addr|0 -- c-addr u )` (reuse-out-2 and ROUT3: five copies); `cell-counted,` moved to `bounds.fs` beside its reader `cell-count` | New 2026-11-02; unit-tested against an independent UTF-8 model in `tests/lib/bytes.fs`, which loads it under `HEX` and counts heap blocks to show that a second `reader-init` frees the first buffer |
| JSON reader | `src/lib/json.fs` | `json:` view record: a fail-closed, non-recursive RFC 8259 parser of one text into a growable token tape (containers know their item count and extent), escapes decoded in place, numbers kept as digit text, limits on depth, tokens, string and number length; `json-find`, `json-next`, `json-natural`, `json-u` (on `decimal.fs`'s `digits>u`, which it requires; `digits>u` and `decimal>u` moved there 2026-11-13); kind-checked `json-items-of` and `json-kind-at`; `json-kind-at? ( index view kind -- flag )`, whether the token at any index is of a kind, false outside the tape (reuse-d, 2026-11-19, Forth review of reuse-c finding 2: one bounds test and one comparison; callers the elaboration data's null, integer and object tests, `elab-data.fs`, the manifest's natural and commit members, `manifest.fs`, the NDJSON reader's object, array, real-number and list tests, `ndjson.fs`, the replay's format test, `run-replay.fs`, and `json-string-at?`); `json-string-at? ( index view -- flag )` and `json-string-of ( index view -- c-addr u true \| false )`, a token at any index that is a string and its text (reuse-c, 2026-11-19, plan 9.4.8n (12): one kind test, no scan, no memory; callers the elaboration data's eight string tests, `elab-data.fs`, the manifest's members, `manifest.fs`, the NDJSON reader's text fields, `ndjson.fs`, and the replay's verdicts, `run-replay.fs`, each on one token at a time). Loads in decimal whatever `BASE` is, and restores it | New 2026-11-02; malformed corpus and every limit tested in `tests/lib/json.fs`, loaded under `HEX` |
| JSON writer | `src/lib/json-write.fs` | Plan task 3.1.3. A writer record (`json-writer: ( depth room "name" -- )`, or `jw-size` and `jw-init` in memory the caller owns, such as a context member) writes one JSON text to the caller's sink xt `( c-addr u -- )`: `jw-start ( sink writer -- )`, then `jw-string`, `jw-n` (signed cell), `jw-u` (unsigned cell), `jw-digits` (integer text of any size, as `json.fs` keeps it), `jw-bool`, `jw-null`, `jw-open-object`, `jw-key`, `jw-close-object`, `jw-open-array`, `jw-close-array`, or `jw-copy ( index view writer -- )` of a value `json.fs` parsed; `jw-end ( writer -- outcome )`. Every call takes the writer last and returns nothing. Deterministic bytes: no whitespace; members in call order, and with `jw-sorted` set each object's keys must strictly increase in byte order (code point order), checked against the last key kept in a key pool of `room` bytes; integers in decimal whatever `BASE` is, `-0` written `0`; strings escaped only as `\"`, `\\`, `\b \f \n \r \t` and `\u00xx` (lowercase) for other bytes below 32, everything else, valid UTF-8 included, as itself, which are the bytes of Python's `json.dumps(v, separators=(",", ":"), ensure_ascii=False)`; with the setting `jw-lean` (2026-11-03, for the NDJSON re-exporter) the bytes of Lean 4.35.0's `Json.compress` instead, which writes backspace, tab and form feed as `\u0008`, `\u0009` and `\u000c`; no real numbers (`jw-copy` of one is unsupported). The first failing call writes nothing and its outcome sticks until the next `jw-start` (`jw-outcome` reads it): invalid for calls out of order (a close that does not match its open or follows a key, a value where a key is due, a second value, `jw-end` before the value is complete, writes before `jw-start` or after `jw-end`), invalid UTF-8, bad integer text or flags, keys out of order in sorted mode, and any call from inside the writer's own sink (`jw-reset` or `jw-init` there fails the text when the sink returns); full past the byte limit `jw-limit` (so a buffer of n bytes never overflows), the depth or the key pool. So `jw-end` gives ok only for exactly one complete JSON value, and the sink only ever receives a prefix of one. After a THROW out of a writer word the caller discards the text and calls `jw-reset` (a THROW outside the sink leaves no mark); a sink that writes over the string or view being written is unchecked. No state of its own; `jw-copy` is a loop over the value's tokens, without recursion (a container it opens records the index of the token after it, and closes there), so a few stack cells serve any depth the writer allows. Loads in decimal whatever `BASE` is, and restores it | New 2026-11-02; `tests/lib/json-write.fs` (180 assertions: every word's positive and negative cases, every limit at and one past its bound, sorted keys, keys refused as strings are, the sink rules including `jw-reset` and `jw-init` from inside the sink, a copy 10,000 containers deep and copies stopped by a failed close, two interleaved writers and a context member, 2,000 random strings and 2,000 random cells written and read back by `json.fs`, and all 138 lines of `tests/reference/*.ndjson` plus 16 lines with every other record kind of lean4export 3.1.0, `tests/lib/json-write-corpus.ndjson`, copied back byte for byte in both key modes; Lean's escapes for every byte below 32, keys, copies and `jw-limit`, 2026-11-03), loaded and partly run under `HEX`; `tests/lib/test_json_write.py` compares 300 random values written with the writer's words and 150 non-canonical texts copied with `jw-copy` against Python's `json.dumps`, 40 copies of values nested up to 64 deep, plus 50 refusals with their exact prefixes; 21 planted faults each caught, and after the independent review (2026-11-02) 6 more, one per fix reverted or broken, on Gforth 0.7.3 and 1.0; callers include, since reuse-b (2026-11-19, review R2), the snapshot information of `check --save-snapshot` (`cli/leanforth.fs`, six members into a 1,024-byte cell-counted buffer, a text over 128 bytes as null) |
| Packed 32-bit fields | `src/lib/u32.fs` | `u32@ ( addr -- u )` and `u32! ( u addr -- )` read and write an unsigned 32-bit field; `u32s ( n -- au )` sizes *n* fields; `u32-mask` is the 32-bit mask on any cell size. Gforth's `l@`/`l!` where the host has them and a load-time check (`u32-sound?`) shows they are unsigned 32-bit access: a value with bit 31 set comes back unchanged, and the four characters after the field keep their values; otherwise, or when `lf-u32-portable` is defined first, the Forth-2012 `u32-bytes@`/`u32-bytes!` (four characters, least significant first, an order the module fixes; public for the tests only). `u32!` keeps the low 32 bits; on a 32-bit host a value of 2³¹ or more reads back as a negative cell, so compare with `U<`. Loads in decimal whatever `BASE` is, and restores it. The layout of packed records is defined by arithmetic on the values, never by byte order, and packed memory is never written to a file as it is (the little-endian block words `u32s>le`, `le>u32s`, `u32-le!`, `u32-le@` convert, for sectioned files). The only non-text module allowed byte access (`scripts/check-portable-forth.py`) | New 2026-11-02 for the compact store ([ADR 0016](../adr/0016-compact-store.md), accepted 2026-11-03); not loaded by `lib.fs`; used since 2026-11-03 by the compact store's modules ([below](#the-compact-store)); both versions tested on every host in `tests/lib/lib.fs`, which loads it under `HEX` and asserts that Gforth's words are in use, shows the check refusing a sign-extending fetch and a cell-wide store, and loads it again under `BASE` 8 with `lf-u32-portable` defined to get the Forth-2012 version; after the independent review (2026-11-02) 6 planted faults each caught |
| Wordlist modules | `src/lib/module.fs` | The two library wordlists of [ADR 0010](../adr/0010-wordlists.md) (accepted), `lf-lib` (public, pushed onto the search order once) and `lf-lib-private` (helpers), and its four words `order+`, `order-`, `module-open`, `module-close` | New 2026-11-03; used by the compact store's library modules below, `sha256.fs`, `text-rule.fs`, `text-run.fs` and, since 2026-11-12, `context.fs` (the ADR's migration converts the others); tests reach helpers with `lf-lib-private order+` |
| Tables of execution tokens | `src/lib/xt-table.fs` | `xt-table: ( n default "name" -- )` makes a table of n execution tokens, each the default; `xt-table! ( xt i table -- )` sets entry i and aborts outside the table, so a table filled while loading never writes beside it; `xt-table@ ( i table -- xt )` gives entry i, or the default for any other index, so an index read from data (a node's tag, a log step's rule) needs no check of its own. `?execute ( i*x xt|0 -- j*x )` runs an optional hook (ROUT3: four copies of `?dup if execute then`: the snapshot's renumbering, the scheduler's tick, the carry note). Helpers private (ADR 0010); no state of its own | New 2026-11-13 (plan task 9.4.5, the item-2 Forth review's L5); the printers' and the step list's tag and rule tables (`src/present/term-printer.fs`, `print-forth.fs`, `log-view.fs`); tested in `tests/lib/lib.fs` |
| Portable 32-bit hashing | `src/lib/hash32.fs` | `hash-fmix` (Murmur3's finaliser), `hash-step ( h x -- h' )` and `hash-bytes ( addr u -- h )` (FNV-1a), every product masked to 32 bits, so 32- and 64-bit hosts give the same values ([below](#the-compact-store)) | New 2026-11-03; `tests/lib/hash32.fs` against values computed in Python |
| Growable heap stores | `src/lib/slab.fs` | Plan task 1.1.5. `slab-init ( unit limit slab -- outcome )`: units of any size in one heap block that doubles by `RESIZE` up to a limit; `slab-room`, `slab-claim`, `slab-commit`, `slab-at`, `slab-top`, `slab-data ( slab -- addr n )` (unit 0's address and the count: the units in use, whose block a reader in place watches; 2026-11-18, replacing `import/snapshot-tier.fs`'s copy `tf-slab-data`, callers `env-snapshot.fs` and `cli/check-run.fs`'s watch of a `--jobs` run's input), `slab-trim`, `slab-clear`; `slab-since ( k slab -- n )` (the units added since the slab held k, its count less k: a span's length from a mark kept as a count; cleanup-families-2, 2026-11-19, in place of `slab-count ... -` in `elab-app.fs`'s `ea-xn`, `ea-paramidx`, `ea-insts#`, `elab-data.fs`'s `ed-params-read`, `ed-types-span`, `ed-span-close`, `elab-pending.fs`'s `ep-defs#`, `ep-goals#`, `tactic-run.fs`'s `lfg-entries`, `runs.fs`'s `rn-from`, `snapshot-tier.fs`'s `pool-left` and `slab.fs`'s own `slab-rest`, and after the review of cleanup-families-2 (B1) `defeq.fs`'s `de-post#` and `de-bind-n`, `elab-pending.fs`'s `ep-c#`, `ep-kept` and `ep-tail`, `whnf.fs`'s `wc-rest` and `wc-alt-apply`, `author/errors.fs`'s `lfa-.detail` and `core/string-literals.fs`'s `lf-str-fields?`; one subtraction; speed (2026-11-19, Gforth 1.0.0, WSL2, load about 8, 10^7 calls): 4.6 ns a call on `gforth`, 2.2 ns for the hand-written `slab-count k -`, and 2.4 against 1.4 ns on `gforth-fast`; faults `cf2-slab-since-reversed`, `cf2-span-close-whole`, `cf2-rn-from-whole`, `cf2-pool-left-one-short`); `slab-cut ( n slab -- )`, back to a count kept earlier (0 ≤ n ≤ count, else it throws `slab-bad-cut`, -4133), and `slab-remove ( i slab -- )`, unit i taken out of the middle ([below](#stacks-outcome-loops-and-index-checks)); marks `slab-mark`, `slab-rollback`, `slab-mark-valid?` with `store.fs`'s refusals ([below](#the-compact-store)); a slab as a stack: `slab-push`, `slab-pop`, `slab-2push`, `slab-2pop`, `slab-last`, `slab-drop`, a pop of an empty slab throwing `slab-underflow`; worklists `slab-all?` and `slab-2all? ( slab xt -- flag outcome )` ([below](#stacks-outcome-loops-and-index-checks)); copies kept as a stack, a choice point's saved state: `slab-keep ( slab store -- outcome )` pushes a copy of a slab's units and their count onto a store of the same unit (at least a cell; one claim, so full or invalid changes nothing), `slab-restore ( slab store -- outcome )` makes them the slab's again and drops the copy, `slab-forget ( store -- )` drops it, `slab-kept ( undo? slab store -- outcome )` either (each copies the slab's bytes once; a keep and a restore together, measured 2026-11-18 on gforth and gforth-fast: 0.45 and 0.24 µs for 4 cells, 0.58 and 0.55 µs for 1000 cells, two `MOVE`s of the bytes) | New 2026-11-03; stacks 2026-11-13 (plan 9.4.8a) in place of 21 hand-written pushes, pops and tops, and 4 more after review reuse-1a (B1); the worklists 2026-11-13 (B2) in place of `lf-meta-pairs-all` and `pq-lrun`; `slab-cut` 2026-11-13 (review s1-synth-b B2) in place of 10 hand-written negative `slab-commit`s in 8 front-end files (the kernel's `env-schedule.fs` copy waits for its [kernel] batch); `slab-remove` 2026-11-14 (review s1-elab B2) in place of 3 hand-written removals in the elaborator; `slab-keep`, `slab-restore`, `slab-forget`, `slab-kept` 2026-11-18 (fix-batch-3, reviews C2 and N4) for the tactic saves of `trw-mvars`, the induction blocks and the pending instance list (a few units each: one rule's metavariables, the open with-blocks and their cases, one declaration's pending problems); `tests/lib/slab.fs` |
| Runs (sequences that never change) | `src/lib/runs.fs` | A run is a handle (0 the empty run) to a stretch of a slab of cells, which are only appended, never changed, so runs share cells and a saved run is its handle: `run-push ( run x -- run' outcome )` (in place when the run ends at the top of the cells, else after a copy of it), `run-take` and `run-after ( run n -- run' outcome )` (no copy), `run-cat ( run1 run2 -- run outcome )` (in place when run2 begins where run1 ends), `run-count`, `run@ ( run i -- x )`, `run-valid?`, `run-each ( i*x run xt -- i*x outcome )` (a step on each cell, in order, to the first failure), `run-filter ( run xt -- run' outcome )` (the cells a test keeps, as a new run; invalid when the test appends cells), `runs-reset`, `runs-epoch` (changes with each reset), `runs-cells`; invalid for a handle that names no run or a count out of range, full when a slab cannot grow (no run made); its two slabs are members of the checker context (`context.fs`), so each context has its own runs | New 2026-11-13 (plan FE1g-1; the front end's local contexts and goal lists, `src/front/lctx-views.fs`, `goals.fs`); `run-each` and `run-filter` 2026-11-13 (review s1-synth-b B1) in place of instance search's walks of waiters, answers and subgoals (`synth.fs`), `goals.fs`'s unsolved-goals filter and `goal-print.fs`'s goal list ([profile](#runs)); `tests/lib/runs.fs` (its example, every refusal, every heap refusal inside an operation, 400 random operations against a model, filters among them), planted faults `fe-goal-run-no-copy` and four `lib-runs-…` caught |
| Stable sorting | `src/lib/sort.fs` | `sort-records ( a-addr n sorter -- outcome )` sorts n records of any size in place by the caller's order `( a-addr1 a-addr2 -- n )`, or by their keys (`sorter-key!`; `sorter-cells` and `sorter-u32s` order values); stable: insertion up to `sorter-short` (32) records, above that a bottom-up merge from runs of one record through a scratch (the caller's, `sorter-buffer!`, or the heap's: full when refused, nothing changed), its comparisons call for call those of `level-normalize.fs`'s `lf-lnorm-sort`; no recursion; invalid for a bad count, a sorter not accepted or busy, and an order or key word that changes the stack depth; a THROW out of the order is passed on, the scratch freed ([below](#sorting)) | New 2026-11-12 (the kernel refactor's batch C2 waited for it); used since 2026-11-13 (plan 9.4.8a) by the front end's `Level.normalize` (`src/front/level-normalize.fs`), the re-exporter's mdata members (`src/import/ndjson-emit.fs`) and getInstances' priority sort (`src/front/instances.fs`, branch `s1-synth`); since branch `reuse-k1` (2026-11-13, awaiting the owner's [kernel] approval) the kernel's six sorts use it: the snapshot's three lists, Level.normalize's arguments and both level substitutions' reached nodes ([below](#sorting)); `tests/lib/sort.fs`, 23 planted faults each caught |
| Tables of texts | `src/lib/texts.fs` | `texts-begin`, `texts+ ( "text ..." -- )`, `text,`, `texts-end` lay a table of counted texts in the dictionary; `texts-find ( x xt table -- entry \| 0 )` searches it with the caller's test, `texts-index ( x xt table -- i \| -1 )` gives the hit's index ([below](#tables-of-texts)) | New 2026-11-18 (front reuse pass part A); `texts-index` 2026-11-19 (review s3a-decide B4); `front/meta-env.fs`, `front/nat-offset.fs`, `core/nat-ops.fs`; `tests/lib/texts.fs` |
| Keyed memo tables | `src/lib/memo.fs` | `memo-init ( kcells vcells memo -- outcome )`: keys and values of fixed numbers of cells, entries in a slab found by an `htab.fs` table; `memo-find`/`memo-put` (keys by address), `memo-at`/`memo-claim`/`memo@`/`memo!` (keys of one or two cells), `memo-clear`, `memo-empty` (a large table made small again), `memo-cut` (newest first), a check hook (a stale value is a miss) and an admit hook (an entry may be refused); every memo's table shares one read-only hooks record (review reuse-k1 M1) ([below](#keyed-memo-tables)) | New 2026-11-13 (branch `reuse-k1`); the checker's result caches (`caches.fs`), Lean's replace memo (`replace-memo.fs`) and the NDJSON reader's index maps use it; `tests/lib/memo.fs`, 12 planted faults each caught |
| Decimal numbers | `src/lib/decimal.fs` | `in-base ( i*x xt base -- j*x )` and `in-decimal ( i*x xt -- j*x )` (BASE set, restored after a `THROW` too); `u>decimal`, `n>decimal`, `ud>decimal`, `d>decimal ( … -- c-addr u )`, `.decimal`, `u>hex`; `decimal>number ( c-addr u -- ud c-addr' u' )`, `decimal-digits?`; `digits>u` (leading zeros skipped), `decimal>u` and `cell-digits` moved from `json.fs`, `skip-zeros` from `bignum.fs` ([below](#decimal-numbers-bits-and-heap-blocks)); `decimal-digit? ( c -- flag )` (from `json.fs` and `bignum.fs`, and four module copies), `hex-byte! ( byte c-addr -- )` (from `json-write.fs` and `sha256.fs`; its digit `hex-char` private since ROUT3), `type-right` and `type-left ( c-addr u width -- )`, text padded on the left or the right to a column (reuse-out-2; `type-left` moved from `ndjson-count.fs` in ROUT3, and the timings' column) | New 2026-11-13 (batch `reuse-out`, plan 9.4.8d) in place of 23 hand-written BASE switches and number readers in 15 modules, kernel included; after review reuse-out (B2) also of the three hexadecimal copies (`name-text.fs`, `log-view.fs`, `latex-text.fs`) and `ir-run.fs`'s digit count and number text; `tests/lib/decimal.fs`, 9 planted faults each caught |
| Bits and binary search | `src/lib/bits.fs` | `cell-bits` (a constant, counted, never `1 cells 8 *`), `log2-ceiling` (public, from `htab.fs`), `bits>cells`, `bit@`, `bit-on ( i a-addr -- … )` (no caller clears a bit: `bit-off` was dropped after review reuse-out), `lower-bound ( i*x lo hi xt -- i*x k )` (the first index whose element is not below, by the caller's test, over any signed range) ([below](#decimal-numbers-bits-and-heap-blocks)) | New 2026-11-13 (batch `reuse-out`, plan 9.4.8d) in place of 7 cell-width counts (`bignum.fs`'s `limb-bits` since review reuse-out B2), 3 log2 loops, 3 bit sets and 2 binary searches; `tests/lib/bits.fs`, 5 planted faults each caught |
| Heap blocks in a cell | `src/lib/blocks.fs` | `allocate0 ( u -- addr ior )` (ALLOCATE of zeroed memory, from `store.fs` in ROUT3; `store.fs`, `htab.fs`, `context.fs`, `task.fs` and three modules call it), `block-zeroed ( u a-addr -- outcome )` (on `allocate0`), `block-resize ( u a-addr -- outcome )` (full leaves the cell as it was), `heap-claim`, `heap-release` (moved from `bytes.fs`) ([below](#decimal-numbers-bits-and-heap-blocks)); `block-reused ( u a-addr -- flag )` and `block-free ( a-addr -- ior )`, a module's block kept for reuse and given back (reuse-out-2: log-view.fs and proof-outline.fs) | New 2026-11-13 (batch `reuse-out`, plan 9.4.8b) in place of 13 hand-written allocate-erase-store and resize-or-allocate copies, kernel included (`env-layers.fs`'s `starts-grow` since review reuse-out B2); `tests/lib/blocks.fs`, 3 planted faults each caught |
| Priority queues | `src/lib/pqueue.fs` | `pq-init ( order pq -- outcome )`, `pq-push`, `pq-pop`, `pq-min`, `pq-count`, `pq-clear`, `pq-free`: a binary min-heap of cells on a slab by the caller's order ([below](#priority-queues)) | New 2026-11-13 (branch `reuse-k1`); the parallel scheduler's two ready queues (`env-schedule.fs`); `tests/lib/pqueue.fs`, 6 planted faults each caught |
| Hash tables | `src/lib/htab.fs` | Open addressing over 32-bit slots, hooks for rehashing and comparing, growth at 3/4, removal by Algorithm R, `htab-base ( htab -- addr )` (the slots' block, new after any growth, `htab-spread` or `htab-renew`: `cli/check-run.fs` watches it in a `--jobs` run, 2026-11-18), `htab-spread` and `htab-presize` ([below](#the-compact-store)); `htab-renew ( htab xt -- )`, a reset that clears a table of at most `htab-small-slots` (1,024) slots and makes a larger one again by xt, with its test `htab-small? ( htab -- flag )` ([below](#resetting-a-hash-table); reuse-out-2 and ROUT3: the term, level and reference tables, the audit's pair set, the comparison's pair set; `memo.fs`'s `memo-small` is the same constant) | New 2026-11-03; `tests/lib/htab.fs` |
| Hash-consed sets in two tiers | `src/lib/cons.fs`, `src/lib/pools.fs` | Each distinct record once, named by a number; a sealed input set shared read-only and scratch sets over it whose numbers continue; marks, resets, sealing; interned lists of 32-bit numbers (tuples, no fixed length) and texts ([below](#the-compact-store)) | New 2026-11-03; `tests/lib/cons.fs` |
| Compact store | `src/core/compact.fs` and `compact-tier.fs`, `compact-names.fs`, `compact-levels.fs`, `compact-exprs.fs` | ADR 0016's Lean layer: names, levels, universe lists, literals and 16-byte expression records in input and scratch tiers ([below](#the-compact-store)); telescopes (reuse-c, 2026-11-19, plan 9.4.8n (12)): `expr-pis ( e tier -- n )`, `expr-pi-end ( e tier -- e' )`, `expr-pi-after ( e tier k -- e' tier )` and `expr-domain ( e tier k -- e' true \| false )`, Lean's getForallArity and bindingDomain! of binder k without unfolding, a loop over the leading Pis (linear in the binders passed, no memory, no recursion; k unsigned), in place of `constructions.fs`'s `pi-count`/`nth-pi`/`pi-end`, `lib-decode.fs`'s `lf-tier-domain` and `elab-data.fs`'s `ed-pis+`/`ed-lead`; callers pass Init's telescopes, 198 binders over the 49 types of the constructions slice, which `tests/front/constructions.fs` compares with the old copies | New 2026-11-03; not yet used by the kernel; `tests/core/compact.fs`, round trips of the reference exports and of `Init` |
| Big natural numbers | `src/lib/bignum.fs` | Arbitrary-precision naturals for Lean's `Nat` literals ([below](#big-natural-numbers)): numbers in an arena the caller provides (`/big-arena`, `big-arena-init`; `big-mark` and `big-release` give back what was made since a mark), one-cell limbs whose width is counted (`limb-bits`), decimal reading and printing (`decimal>big`, `big>decimal`), conversion to and from a cell (`u>big`, `big>u`), comparison (`big-compare`, `big=`, `big<=`), and the operations Lean 4.35.0's kernel computes on literals (`big+ big- big* big/ big-mod big-gcd big-and big-or big-xor big-lshift big-rshift big-pow`, each `( a b arena -- c outcome )`). Schoolbook multiplication with Karatsuba from 48 limbs, Knuth's algorithm D, Lehmer's gcd. Outcomes ok, invalid (a malformed or released number, text or arena) and full (no room, or more bits than the arena's limit, by default Lean's 2^30). No state; loads in decimal whatever `BASE` is | New 2026-11-02 (plan task 5.2.3, library part); not yet used by the kernel (task 5.1.4); `tests/lib/bignum.fs` reaches every outcome; `make test` compares 37,585 cases with Python's integers on the running Gforth and catches 22 planted faults; review fixes of 2026-11-03 (printing overwrote the number below its text, stale operands, two speed fixes) with guarded-arena sweeps; `make check` has 984 of them computed by pinned Lean's kernel |
| Signed big integers | `src/lib/bigint.fs` | Lean 4.35.0's `Int` over `bignum.fs` ([below](#signed-big-integers)): an integer is a sign cell (-1, 0, 1) followed by a bignum magnitude, made at the top of a bignum arena; `bigint+ bigint- bigint* bigint-ediv bigint-emod` `( a b arena -- c outcome )` (Lean's `/` and `%` on `Int` are `Int.ediv` and `Int.emod`), `bigint-bmod` and `bigint-pow` `( x m arena -- c outcome )` with a natural number `m`, `bigint-negate`, `bigint-gcd`, `bigint-natAbs` and `bigint-toNat` (natural-number results), `bigint-compare`, `bigint-sign`, `bigint-magnitude` (in place), `nat>bigint`, `n>bigint`, `bigint>n`, `decimal>bigint`, `bigint>decimal`, `bigint-valid?`. Outcomes ok, invalid, full as `bignum.fs`'s. Standalone: requires `bignum.fs` (and through it, since 2026-11-13, `bits.fs` and `decimal.fs`), `bounds.fs`, `outcome.fs`, `portability.fs` and `module.fs`; helpers private (ADR 0010); no state; no host recursion of its own; loads in decimal whatever `BASE` is | New 2026-11-13 (plan step FE1i-4, for `by-omega` and `by-decide`); tested alone, on branch `fe1i4-bigint`; no tactic uses it yet. `make test-bigint`: unit tests of every word and outcome, every room from 0 cells up, no heap use; 9,906 pairs against a model of Lean's definitions; the header's example and exact interface from outside the project. `make reference-bigint`: 17,906 pairs (10,000 random) equal pinned Lean's own `Int`, line for line, and 300 kernel-decided equations. 17 planted faults (`fe-bigint-…`) each caught; Forth review 2026-11-13 not blocking, its M1, L1, L2, S1 fixed |
| SHA-256 | `src/lib/sha256.fs` | FIPS 180-4 SHA-256, incremental ([below](#sha-256)): `sha256:` (or `/sha256` address units of the caller's memory), `sha256-init ( sha -- )`, `sha256-update ( c-addr u sha -- )` with pieces of any size, `sha256-final ( c-addr sha -- )` for the 32-byte digest, `sha256-hex ( c-addr1 c-addr2 -- )` for its 64 lowercase hexadecimal digits. One word per FIPS function (`sha-rotr`, `sha-shr`, `sha-ch`, `sha-maj`, `sha-big-sigma0`, `sha-big-sigma1`, `sha-small-sigma0`, `sha-small-sigma1`), the plain round and schedule built from them, and on cells of 64 bits or more a fast round and schedule with the functions written out in place. Standalone: requires `portability.fs`, `bits.fs` (`cell-bits`), `decimal.fs` (`hex-byte!`) and `module.fs`; helpers private in `lf-lib-private` (ADR 0010); no state of its own; nothing fails. Loads in decimal whatever `BASE` is | New 2026-11-03 (plan task 3.2.6, for the export manifests); the program track's flagship verification target; `make test-sha256`: NIST vectors, every split of messages up to 200 bytes, the functions against independent models, the fast round against the plain one, 306 random messages against Python's `hashlib` on both paths, the header's example and the exact public interface checked from a folder outside the project; 14 planted faults each caught |
| Name tables | `src/lib/name-table.fs` | `name-table: ( "name" -- )`, an empty read-only table (two cells: its first and last entry); `name-entry ( c-addr u table -- )` links an entry of that name (at most 255 bytes) and the caller lays its data after it; `name-table-find ( c-addr u table -- entry \| 0 )` by exact bytes, the first in order; `name-entry-name`, `name-entry-data`, `name-table-each ( table xt -- )` ([below](#name-tables)). Requires `bytes.fs` and `module.fs`; helpers private; no state | New 2026-11-18 (branch `fix-cli-present`, review R4 of 2026-11-18 author-cli and R9 of the present pass); callers `src/present/name-text.fs`'s tokens (139 names) and, since reuse-b (2026-11-19, review R1), the command line's options (25) and commands (11), `print --statement`'s forms (5) and the progress line's parts (9, walked with `name-table-each`); `tests/lib/name-table.fs` on its own |
| Visible text | `src/lib/text-rule.fs` | `tr-rule? ( c-addr u -- flag )`: valid UTF-8 with no control, format, line or paragraph separator or surrogate character (Unicode Cc, Cf, Zl, Zp, Cs); `tr-banned? ( code -- flag )`: a code point no such text holds; `tr-shown? ( c-addr u -- flag )`: also a character that is seen, not a space, a blank-looking filler, a combining mark or a default-ignorable code point. The rule of program receipts 0.2 and of run records; tables generated from Unicode 15.1 by `scripts/text_rule_tables.py`. Requires `bounds.fs`, `bytes.fs` and `module.fs`; helpers private; no state | New 2026-11-03 (run records, plan task 2.2.5); `tests/lib/text-rule.fs` on its own; every code point compared with the run-record schema's patterns by `tests/core/test_run_records.py` |
| Running text | `src/lib/text-run.fs` | The interpreter's settings saved and restored (`run-settings-save`, `-restore`), a whole file read once as bytes (`text-file-slurp`), lines (`text-line-end`, `text-cr-drop`), the plain-text rule (`text-plain-at`), the float stack's depth (`floats-depth`, `floats-drop-to`); `text-scan ( c-addr u xt -- n )`, the offset of the first character for which the test `xt ( char -- flag )` holds (u when none), and `text-any? ( c-addr u xt -- flag )`, whether any does (`text-any? 0=`: none does); `text-trim ( c-addr u -- c-addr' u' )`, the text without the spaces at its start (`text-from`) and end (standard `-TRAILING`), new 2026-11-20 (slice S3a-ops) for its one caller, `src/front/reader.fs`'s `lfn-mode-spells?`, which compares a notation word with the notation table's spellings (`" <= "`, `"¬"`: 1 to 9 bytes, 22 words while loading), tested in `tests/lib/text-run.fs`, fault `lib-text-trim-keeps-start`. *Algorithm*: one pass with `/STRING`, stopping at the first match, so offsets count characters on any host; *genericity*: any per-character test; *cost*: one call of the test per character up to the first match, no memory, two return-stack cells; *speed* (Gforth 1.0 `gforth`, 2026-11-14, load average about 0.1, `.claude/work/ROUT4/`): `text-any?` with no match 8 ns a character at 10 characters, 6 ns at 10^6. Requires `portability.fs`, `outcome.fs`, `module.fs`; helpers private; no state | New 2026-11-03 (program verifier); `text-any?` 2026-11-14 (ROUT4, review reuse-out-2 rc3 B2) in place of five of eight hand-written character loops: print-forth.fs's `lf-pf-odd?`, `lf-pf-blank-in?`, `lf-pf-note?` (names, labels and notes, a handful of bytes each), cli/leanforth.fs's `cli-plain?` (a snapshot's information texts, under 40 bytes), import/manifest.fs's `hex-text?` (40- and 64-digit commits and digests); of the other three, author/source.fs's `lfa-digits?` went onto `decimal-digits?`, `lf-pf-among?` and `cli-quote-at` onto `bytes.fs`'s `byte-scan`; `tests/lib/text-run.fs`, faults `r4-text-any-last` and the callers' `r4-*` |
| Portability adapter | `src/lib/portability.fs` | Forth-2012 definitions of `>=`, `<=`, `0<=`, `0>=`, `-rot`, `max-n`, `cell` and the structure words, compiled only where the host lacks them; `ndrop ( xn .. x1 n -- )`, a common extension that Gforth lacks: the n cells below n dropped (n >= 0; a loop of n `drop`s, constant scratch, no recursion). Callers (review tactic-move B1, 2026-11-19, in place of two hand-written loops): `tactic-run.fs`'s `lf-tac-detail-n` (a detail's 1 to 3 cells, dropped once an error is recorded) and `text-run.fs`'s `run-settings-depth` (the search order's word lists, a handful). A third copy, `src/program/ir-run.fs`'s `irx-discard`, stays until the clamp receipt's evidence, which pins that file's hash, is next recorded (plan 9.4.8l (T)). `scripts/check-portable-forth.py` refuses a module under `src/` that uses one of them without loading this file, directly or through the files it loads | New 2026-11-02; defines nothing under Gforth except `max-n` and (since 2026-11-19) `ndrop`; `cell` and the load check added 2026-11-02 |
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
| Test support | `tests/support/tester.fs`, `checks.fs`, `term-cases.fs`, `composition.fs`, `heap-watch.fs`, `meta-sweeps.fs` | Adapter for Gforth's bundled tester that fails the run on the first error; shared checks and fixtures; resource sweeps of a front-end pass on one term, every heap allocation or every term refused in turn (`meta-sweeps.fs`, 2026-11-19); `ALLOCATE` and `FREE` that count the heap blocks held, in a word list of their own, for tests that show a module frees what it allocates | Test-only |

## Reusability: the libraries as standalone Forth code

**Rule** (owner, 2026-11-03; `AGENTS.md`): general-purpose libraries are
written so that other Forth programs can use them, not coupled to
LeanForth, unless coupling gains a lot. Audit of `src/lib/` on 2026-11-03:

| Library | General purpose? | What ties it to LeanForth today |
| --- | --- | --- |
| `bignum.fs` (natural numbers) | yes; no Lean code (Lean only in comments) | needs `outcome.fs`, `bounds.fs`, `portability.fs` (104 lines), and since 2026-11-13 `bits.fs` (`cell-bits`) and `decimal.fs` (`skip-zeros`, with its `module.fs`); naturals only (subtraction stops at 0, as Lean's `Nat`); since 2026-11-18 its 34 public words are named in the header with a runnable example and the helpers are in `lf-lib-private`. Shown working from an unrelated folder on both Gforths |
| `bigint.fs` (signed integers) | yes, written to this rule (2026-11-13); Lean only in comments: its semantics are Lean's `Int`, which is also ordinary Euclidean division | requires `bignum.fs`, `bounds.fs`, `outcome.fs`, `portability.fs` and `module.fs`; helpers in `lf-lib-private`, 20 public words (`bigint…`, `nat>bigint`, `n>bigint`, `decimal>bigint`); an example in its header, run with the exact interface checked from a folder outside the project by `make test-bigint` |
| `json.fs` (RFC 8259 reader), `json-write.fs` | yes | since 2026-11-18 (plan 1.1.8, branch `lib-tidy`) each requires exactly what it uses (`portability.fs`, `bounds.fs`, `outcome.fs`, `store.fs`, `blocks.fs`, `bytes.fs`, `decimal.fs`, `module.fs`); helpers in `lf-lib-private`; the public words and a runnable example in each header |
| `bytes.fs` (bounded line reader, UTF-8) | yes | since 2026-11-18 requires `portability.fs`, `bounds.fs`, `outcome.fs`, `store.fs`, `blocks.fs` and `module.fs`, not `lib.fs`; the framing rules are options (`reader-rules!`): a zeroed reader reads ordinary text (a last line without a line feed, CRLF ends, a leading byte-order mark dropped), `reader-strict` is Lean's exports' framing, which the NDJSON and elaboration-data readers pass; helpers private |
| `u32.fs` (32-bit access) | yes | none beyond `portability.fs` |
| `store.fs`, `node.fs`, `walk.fs`, `frame.fs` (bounded stores, records, explicit-stack walks) | yes | the shared outcome vocabulary; since 2026-11-18 (branch `lib-tidy-2`) `frame.fs`'s eleven helpers (the stack's growth, the steps that open and end a visit) are private, its other words public; since branch `lib-tidy-3` the public words of all four are filed in `lf-lib`, as every library's (`store.fs`, `walk.fs` and `frame.fs` had put them in the loader's compilation word list, `node.fs` had no module) |
| `context.fs`, `task.fs` (per-task contexts, job pool) | partly: a general job pool and context mechanism, designed around the checker's per-check state | the checker's context model (ADR 0009); since 2026-11-18 `task.fs` requires `portability.fs`, `blocks.fs`, `context.fs` and `module.fs`, not all of `lib.fs`; since branch `lib-tidy-3` its 29 public words are the pool's interface (`job-submit`, `job-wait`, `job-wait-any`, the pool's start, stop and size, its settings, the host and the THROW codes, listed in its header) and its other 115 words (the pool and job records, the queue, the host's lock and conditions, the workers) are private |
| `outcome.fs` (ok, invalid, exhausted, unknown, rejected, unsupported, full) | LeanForth's shared result vocabulary | deliberately shared: one vocabulary for every module; its words, and `blocks.fs`'s, are in `lf-lib` since branch `lib-tidy-3` (neither has a helper to hide) |
| `sections.fs` (sectioned binary files) | yes, written to this rule (2026-11-11): requires `portability.fs`, `module.fs`, `outcome.fs`, `u32.fs`, `sha256.fs`; helpers private; 14 public words, all `sections…`; an example in its header, run with the interface checked from a folder outside the project by `make test-sections` |
| `sha256.fs` (SHA-256) | yes, written to this rule (2026-11-03) | requires `portability.fs`, `bits.fs`, `decimal.fs` and `module.fs`; helpers in `lf-lib-private`, 17 public words (the hashing interface and FIPS 180-4's functions), all named `sha-…` or `sha256…`; an example in its header and [below](#sha-256), run with the interface checked from a folder outside the project by `make test-sha256` |
| `runs.fs` (sequences of cells that never change) | yes, written to this rule (2026-11-13) | requires `bounds.fs`, `outcome.fs`, `slab.fs`, `context.fs` and `module.fs` (its state is two context members, so one copy per checker context); helpers in `lf-lib-private`, 10 public words, all named `run…` or `runs…`; an example in its header, run by `tests/lib/runs.fs` without the checker |
| `sort.fs` (stable sorting) | yes, written to this rule (2026-11-12) | requires `portability.fs`, `bounds.fs`, `outcome.fs`, `u32.fs` and `module.fs`; helpers in `lf-lib-private`, 11 public words, all named `sort…` or `sorter…`; an example in its header, run by `tests/lib/sort.fs` without the checker |
| `memo.fs` (keyed memo tables) | yes, written to this rule (2026-11-13) | requires `portability.fs`, `bounds.fs`, `outcome.fs`, `u32.fs`, `hash32.fs`, `slab.fs`, `htab.fs` and `module.fs`; helpers in `lf-lib-private`, 17 public words, all named `memo…`; an example in its header, run by `tests/lib/memo.fs` without the checker |
| `pqueue.fs` (priority queues) | yes, written to this rule (2026-11-13) | requires `portability.fs`, `outcome.fs`, `slab.fs` and `module.fs`; helpers in `lf-lib-private`, 8 public words, all named `pq…` or `/pqueue`; an example in its header, run by `tests/lib/pqueue.fs` without the checker |
| `text-rule.fs` (visible text) | yes, written to this rule (2026-11-03): a UTF-8 hygiene rule with nothing of Lean | requires `bounds.fs`, `bytes.fs` and `module.fs`; helpers in `lf-lib-private`, three public words (`tr-banned?` since 2026-11-04, for callers that decode text themselves); an example in its header; `tests/lib/text-rule.fs` runs without the checker |
| coming: the compact store (ADR 0016) | written to this rule from the start | — |

**Packaging them as standalone libraries (plan task 1.1.8).** They were
built just in time for the checker, with correctness and fail-closed
behaviour first. Since 2026-11-18 (branches `lib-tidy` and `lib-tidy-2`):
every file loads alone, with exactly the files it requires, from a folder
outside the project, and every file requires each library file whose
words it uses (an audit of words against `require` lines found none
required and unused); every header has an example ending in what it
prints, run as written by `make test-lib-standalone` on both engines; the
helpers of every file are private (ADR 0010), and since branch
`lib-tidy-3` every public word is filed in `lf-lib`; and every
library's speed is measured at two sizes with its callers' real sizes
([below](#measured-profiles-2026-11-18)). Since `lib-tidy-3` the
standalone test loads each file with `BASE` 7 and a source check reads
every number in decimal, `tests/lib/test_requires.py` checks the direct
`require` lines, and `tests/scripts/test_lib_index.py` checks that each
header's interface list names every public word.

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

## Measured profiles (2026-11-18)

The five parts of [each library's profile](#what-each-library-documents-owner-2026-11-13),
for every file of `src/lib` (plan task 1.1.8). `memo`, `pqueue`, `sort` and `cons` also
have sections of their own below, with more detail. **Speed**: `make lib-bench`
(`tests/lib/lib-bench.fs`) on this machine (10 logical cores under WSL2, shared with
other agents, load average 3 to 5), Gforth 1.0.0, the better of two runs of at least
0.2 s each; raw output in
[measurements/lib-profiles-2026-11-18/bench.txt](measurements/lib-profiles-2026-11-18/bench.txt).
**Callers**: every call of 54 library words counted, with the sizes passed, on a check
of `Init` (59,349 declarations, `check --json --jobs 1 --save-snapshot`, 1,078 s with
the counters), by the patch of
[measurements/lib-profiles-2026-11-18/](measurements/lib-profiles-2026-11-18/README.md)
on a scratch copy; "most" gives the power of two that holds most calls.

| Library: operation (time per item) | gforth-fast, small | large | gforth, small | large |
| --- | --- | --- | --- | --- |
| sha256: hash a message (a byte) | 64: 29.9 ns | 1 MiB: 12.8 ns | 160.1 ns | 68.8 ns |
| json: parse objects (a byte) | 64: 14.2 ns | 1 MiB: 12.4 ns | 53.0 ns | 55.9 ns |
| json-write: an array of integers (a value) | 8: 83.0 ns | 100,000: 75.7 ns | 242.0 ns | 254.9 ns |
| bignum: multiply n by n limbs (a call) | 2: 150 ns | 1,000: 772 µs | 549 ns | 2,765 µs |
| bignum: divide 2n by n limbs (a call) | 2: 244 ns | 1,000: 2,165 µs | 781 ns | 8,084 µs |
| bigint: ediv, -2n by n limbs (a call) | 2: 550 ns | 1,000: 2,340 µs | 1,723 ns | 7,678 µs |
| htab: insert, then find (an operation) | 1,000: 55.2 ns | 10^6: 87.0 ns | 179.8 ns | 244.6 ns |
| memo: put, then find (an operation) | 1,000: 157.9 ns | 10^6: 393.5 ns | 404.5 ns | 749.2 ns |
| slab: push, then pop (an operation) | 1,000: 28.0 ns | 10^6: 24.5 ns | 63.9 ns | 67.4 ns |
| sort: random cells, with their copy (a cell) | 16: 185.7 ns | 10^6: 698.6 ns | 433.4 ns | 1,823.9 ns |
| pqueue: push, then pop (an operation) | 1,000: 207.7 ns | 10^6: 491.5 ns | 492.8 ns | 1,068.4 ns |
| bytes: utf8-valid? (a byte) | 64: 6.0 ns | 1 MiB: 5.7 ns | 24.2 ns | 25.0 ns |
| bytes: reader, lines of 80 bytes (a byte) | 10 lines: 7.5 ns | 50,000: 0.8 ns | 9.1 ns | 1.5 ns |
| decimal: u>decimal of n digits (a call) | 2: 24.7 ns | 20: 114.7 ns | 76.4 ns | 310.8 ns |
| decimal: u>decimal, then digits>u (a call) | 2: 30.2 ns | 20: 120.2 ns | 92.1 ns | 341.4 ns |
| sections: write, open, read one section (a byte) | 1 KiB: 279.5 ns | 4 MiB: 27.8 ns | 1,107.6 ns | 144.9 ns |
| hash32: hash-bytes (a byte) | 64: 2.1 ns | 1 MiB: 2.2 ns | 3.9 ns | 3.7 ns |
| bounds: cells-index, absent (a cell) | 16: 1.2 ns | 10^6: 0.9 ns | 5.0 ns | 3.6 ns |
| bits: lower-bound over n cells (a search) | 16: 29.1 ns | 10^6: 131.6 ns | 106.1 ns | 522.0 ns |
| u32: u32! then u32@ (a field) | 1,000: 1.4 ns | 10^6: 1.4 ns | 3.2 ns | 3.1 ns |
| pools: text-intern of distinct texts (a text) | 1,000: 230.0 ns | 10^6: 573.4 ns | 585.1 ns | 1,232.3 ns |
| pools: tuples of two (a tuple) | 1,000: 424.2 ns | 10^6: 597.6 ns | 1,170.0 ns | 1,491.7 ns |
| runs: run-push (a cell) | 1,000: 108.7 ns | 10^6: 109.0 ns | 305.1 ns | 321.6 ns |
| store, node: node-new, growing (a node) | 1,000: 32.8 ns | 10^6: 37.3 ns | 106.3 ns | 106.9 ns |
| walk: a chain of n nodes (a visit) | 1,000: 23.2 ns | 10^6: 23.4 ns | 80.7 ns | 83.0 ns |
| frame: a tree of n levels (a visit) | 10 (177 visits): 44.3 ns | 25 (242,785): 44.3 ns | 158.8 ns | 156.6 ns |
| context: new, then free (a context) | 1: 147.4 ns | 100: 155.7 ns | 334.0 ns | 341.0 ns |
| text-rule: tr-rule? (a byte) | 64: 6.2 ns | 1 MiB: 5.6 ns | 24.2 ns | 24.3 ns |
| text-run: text-any?, no match (a byte) | 10: 3.2 ns | 1 MiB: 2.4 ns | 7.7 ns | 6.1 ns |
| xt-table: xt-table@ in n entries (a lookup) | 16: 3.0 ns | 4,096: 3.5 ns | 7.6 ns | 10.6 ns |
| blocks: allocate0 and free of n bytes (a call) | 64: 20.3 ns | 1 MiB: 8.8 µs | 23.7 ns | 8.1 µs |
| outcome: ok-each (a step) | 16: 3.1 ns | 10^6: 2.9 ns | 6.1 ns | 5.1 ns |
| task: empty jobs, 8 in flight (a job) | 1: 47.9 µs | 1,000: 32.2 µs | 50.6 µs | 33.5 µs |

| Library | Algorithm, and why | Generic over | Cost as inputs grow | Callers on `Init` (counted) |
| --- | --- | --- | --- | --- |
| `sha256.fs` | FIPS 180-4's compression of 64-byte blocks, incremental; a 68-row window instead of moving eight variables, the round functions written in place on 64-bit cells ([above](#sha-256)) | any bytes, in pieces of any size; cells of 32 bits or more | linear: 64 rounds a block, plus one or two padding blocks at the end, so a 64-byte message costs 2.3 times a long one's rate; no heap, no recursion | 12.9 million updates, 479 MB: the manifest hashes each of the export's 6.45 million lines (most 32 to 63 bytes) and its line feed; the snapshot's 17 sections (up to 97.8 MB) |
| `json.fs` | one pass, no recursion, into a token tape; numbers kept as digit text; fails closed | any RFC 8259 text; limits on depth, tokens, string and digit length | linear in bytes; the tape grows by doubling, /token bytes a token, to the token limit; a depth stack of one cell a level | 6.45 million texts (each export line), 339 MB; most 32 to 63 bytes, largest 3,272 |
| `json-write.fs` | writes straight to the caller's sink; a stack of open containers and, sorted, a pool of each object's last key; jw-copy a loop | any sink, depth, key room; Python's or Lean's escapes | linear in output; memory fixed by depth and key room | one text, the 7.5 MB `--json` report |
| `bignum.fs` | schoolbook with Karatsuba from 48 limbs, Knuth's algorithm D, Lehmer's gcd: Lean's `Nat` operations ([below](#big-natural-numbers)) | one-cell limbs of any width; the caller's arena | + linear; * n^1.58 above 48 limbs; / n·m; recursion log n (Karatsuba, powers) | 148,179 operations, all of one or two limbs; 91,717 comparisons; 277 literals read (at most 20 digits) |
| `bigint.fs` | sign and magnitude over `bignum.fs`, Euclidean division as Lean's `Int` | as `bignum.fs` | `bignum.fs`'s, plus a copy of the operands | none yet (planned: `by-omega`, `by-decide`) |
| `htab.fs` | open addressing, linear probing, doubling at 3/4 full, Knuth's Algorithm R to delete | the owner's rehash and compare hooks; records live elsewhere | a few probes whatever the size (1.19 slots a find on p1m); 4 bytes a slot, 1.3 to 2.7 slots an entry; a doubling rehashes all | 1.54 billion finds; 17,406 tables; most finds in tables of 2^17 slots, the largest 2^24 |
| `memo.fs` | entries in a slab, found by `htab.fs` ([below](#keyed-memo-tables)) | key and value cells; check and admit hooks | as `htab.fs`, plus the key compare | 380 million finds and 215 million puts on 14 memos, most holding 2^8 to 2^12 entries, the largest 469,297 |
| `slab.fs` | one heap block doubled by RESIZE, with seals and a stack of marks | any unit size and limit | push amortized constant; up to twice the memory while doubling; a growth may move the block | 17,665 slabs; 143,787 growths, most below 1,024 units, the largest from 4,194,304; 3.6 million pushes |
| `sort.fs` | insertion up to 32 records, bottom-up merge above ([below](#sorting)) | record size, the caller's order or key | n^2/4 below 32, n log n above, n records of scratch | 16.3 million sorts, 61% of 0 or 1 record, 92% below 32 (insertion), the largest 2,259 |
| `pqueue.fs` | binary min-heap on a slab ([below](#priority-queues)) | the caller's order of cells | log n a step | only with `--jobs` above 1: one push a declaration (59,349 on `Init`) |
| `bytes.fs` | the reader keeps whole lines in one buffer grown to a limit and finds line ends with Gforth's `scan`; UTF-8 decoded by hand, no tables | any file; framing rules; UTF-8 per RFC 3629 | linear; the buffer the longest line; a refill moves the tail | 6.45 million lines; 476,742 UTF-8 checks, most 4 to 15 bytes, the largest 230 |
| `decimal.fs` | pictured numeric output and digit loops inside `in-base`, which restores `BASE` even after a THROW | any `BASE` at the caller | linear in digits | 20.3 million `digits>u` (export indices, most 4 to 7 digits); 13,011 numbers written |
| `sections.fs` | a 4,096-byte header, each section and the header under a SHA-256; written to a partial file and renamed | any sections of units | linear, dominated by SHA-256 and the file system; about 0.29 ms a file fixed | one snapshot: 17 sections, 133 MB |
| `task.fs` | a fixed pool of POSIX threads fed from a bounded queue under one mutex and two condition variables; tasker on Gforth 0.7.3 | any word as a job, in its own context | about 32 µs a job with 8 in flight, 48 µs alone: a job should take milliseconds | only with `--jobs` above 1 (the scheduler, `env-schedule.fs`); not counted |
| `hash32.fs` | Murmur3's finaliser for cells, FNV-1a for bytes, masked to 32 bits: the same values on 32- and 64-bit hosts | any bytes or cells | linear in bytes | 580,577 texts hashed, most 2 to 7 bytes |
| `bounds.fs` | signed range checks; linear searches of cells | any cells | constant; searches linear | 77.5 million `cells-index`, most of 0 to 3 cells, the largest 62 |
| `bits.fs` | binary search (Knuth's algorithm B), bit sets in cells | the caller's test; any cell width | log2 n tests | 147 million searches, most over 16 to 31 elements, the largest 2,259 |
| `u32.fs` | Gforth's `l@`/`l!` when a load-time check shows them sound, else four bytes; little-endian block copies for files | any cell size | constant | not counted (every packed field of the compact store); the snapshot's 4 conversions, 24 million fields |
| `cons.fs`, `pools.fs` | hash-consing in a slab found by `htab.fs`, in a read-only tier and a scratch tier ([below](#the-compact-store)) | record classes with their own hooks | as `htab.fs`; records and bytes in slabs | 6.46 million records added (the input tier grows to 6.1 million), 30.4 million finds; 178,671 tuples, 2,099 texts |
| `runs.fs` | append-only cells shared between runs; a push in place at the top, else a copy | cells | constant, a copy when not at the top | the `.lf` front end only; none on an export |
| `store.fs`, `node.fs`, `store-columns.fs` | fixed-width records with identities and a sealed shape; heap stores double (at least 16); columns grow with their store | record width, base, limit | constant a record; a growth copies | 13 heap stores (capacity 16 to 64 at first), 1.3 million growths; 222,310 nodes; 18 column growths |
| `walk.fs` | depth-first walk on a bounded, growable work stack, with fuel | the visitor; node or (node, context) items | one visit a node a path, host stacks constant | 68.7 million walks |
| `frame.fs` | each visit a chain of steps on a growable stack, so no pass recurses on the host | the visitor; a context cell | a few cells a visit; host stacks constant | 31.8 million passes, 325 million child visits; the stack grew 54 times |
| `context.fs` | one ALLOCATEd record a worker, members declared while loading | members of any kind | one allocation and the setup words a context | the main context only with `--jobs 1` |
| `text-rule.fs` | UTF-8 decoded, each code point looked up in range tables made from Unicode 15.1 | any UTF-8 text | linear | none on a check of an export (run records, the printer) |
| `text-run.fs` | `/STRING` loops to the first match; the interpreter's settings saved and restored | a test word per character | linear to the first match | 6 scans of at most 64 characters |
| `xt-table.fs` | a cell array with a default, indexed with one unsigned compare | any xts | constant | none counted on a check of an export (printers, the snapshot) |
| `blocks.fs` | ALLOCATE or RESIZE, then ERASE, held in a cell | any size | the erase, linear | 3.4 million zeroed blocks, 14.4 GB in all, most 4 to 8 KiB; 1,174 resizes |
| `outcome.fs` | loops that stop at the first failure | any steps | constant a step | 96 million `ok-each`, most of 2 or 3 steps, the largest 59,953 |
| `lib.fs`, `module.fs`, `portability.fs` | loading only | — | none at run time | — |

What the counts say: the hash tables and memos carry the check (1.54 billion finds; at
the benchmark's 55 to 90 ns an operation on gforth-fast, 85 to 140 s); sorts are
almost all short, so the insertion path matters, not the merge; `allocate0` zeroes
14.4 GB in 3.3 million blocks of 4 to 8 KiB (55 a declaration), worth a look; big numbers on `Init` never exceed two limbs.

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
0.7.3. Short lists (2026-11-13, `gforth-fast` 1.0, while a two-job check
ran): 8 random cells in 0.6 µs a sort, 32 (the cut-over, by insertion)
in 7.7 µs; `gforth` 1.0: 2 µs and 22 µs.

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

**Callers** (2026-11-13). The front end's and the re-exporter's (plan
9.4.8a): `src/front/level-normalize.fs`
(`ln-sort`, a max's arguments by `normLt`, through a sorter in its
context record; the heap's scratch above 32, full when refused) and
`src/import/ndjson-emit.fs` (`members-sort`, mdata's key tokens by their
text, the scratch of data-most cells in its module record, so never
full). Sizes met: the front end's tests sort 2 to 200 arguments
(`tests/front/meta.fs`'s max of 200 metavariables, `meta-heap.fs`'s of
40 with every heap refusal); `leanforth check` never runs the front end
on Init. Init's export (lean4export 3.1.0 of Lean 4.35.0) has no mdata
record, so the re-exporter sorts members only in its tests (up to
data-most, 256, in reverse order). Mathlib's sizes are not measured
yet (plan 9.4.8g). `src/front/instances.fs`
(branch `s1-synth`): getInstances sorts its candidate values (one cell
each) by priority with `sort-signed` and `sorter-key!`, as Lean's
`insertionSort`; on Init, S1's six instance problems pass lists of 1 to
26 values ([S1_INTERFACE.md](../design/S1_INTERFACE.md) §9's counts),
all on the insertion path; a class with more than 32 candidates would
take the merge.

The kernel's (branch `reuse-k1`, under the owner's [kernel] approval):
the sizes are those passed on one check of all of `Init`
(`bin/leanforth check --jobs 1 --save-snapshot`, 59,349 declarations),
counted by a temporary counter in each caller, since removed:

| Caller | Records and order | Sorts on Init | Of n: 0–1 / 2–8 / 9–32 / 33–256 / more; largest | Why the result is the one before |
| --- | --- | --- | --- | --- |
| `src/kernel/level-normalize.fs` `lf-lnorm-sort` (Level.normalize's arguments) | cells by `is_norm_lt`, one unit of fuel per comparison; scratch above the arguments in their stack | 24,545 | 0 / 24,524 / 21 / 0 / 0; 16 | the library's comparisons are, call for call, those of the insertion and merge sorts it replaced (same cut-over, 32), so the fuel too; only structurally equal levels tie |
| `src/kernel/level-substitute.fs` `lf-lsubst-sorted` (the reached levels) | cells, signed; scratch from the heap above 32 | 13,021,899 | 9,983,236 / 3,035,860 / 2,803 / 0 / 0; 15 | the walk lists each node once: distinct keys have one ascending order (the heapsort it replaced was not stable, which distinct keys make irrelevant) |
| `src/kernel/mixed-level-substitute.fs` `lf-mls-sorted` (the reached terms) | cells, signed; scratch: the images' cells, not written yet, so never full | 3,230,996 | 1,102 / 1,400,953 / 1,713,117 / 114,599 / 1,225; 2,259 | as above: the audit lists each term once |
| `src/kernel/env-snapshot.fs` `dep-sort` (a slot's dependencies, written and merged by `env-layers.fs`) | 4-byte little-endian slot numbers, unsigned (`u32-le@` key) | 59,349 | 1,020 / 16,147 / 31,799 / 10,383 / 0; 246 | a stable sort of a total order: the unique result of the insertion sort it replaced |
| `env-snapshot.fs` `look-sort` (a slot's lookups, when it has names beyond the input) | 8-byte (key, answer) pairs by the little-endian key, unsigned | 8 | 0 / 0 / 8 / 0 / 0; 32 | as above (the keys of a list are distinct) |
| `env-snapshot.fs` `o-sort` (a slot's names beyond the input) | cells by `o-order`, the names' content | 8 | 0 / 0 / 8 / 0 / 0; 9 | as above: equal content is the same name |

All six share the one `sort-short` cut-over; the snapshot's three share
one sorter in the writer's record (`snap-outers`), one sort at a time,
and the others one sorter each in their job's record. A sort above the
cut-over that needs heap scratch the heap refuses is full: the snapshot's
save or merge then fails full, and a level substitution is full,
recorded as a full work stack (the insertion sorts and the heapsort they
replaced needed no memory). On all of `Init`, checked with the branch and
with `main` (`--jobs 2`, and `--jobs 1` with the counters), every verdict,
every fuel count (654,719,715 in all) and the saved snapshot's bytes are
the same.

## Keyed memo tables

`src/lib/memo.fs` (2026-11-13, branch `reuse-k1`; library audit action 2;
untrusted until reviewed): a map from keys of a fixed number of cells to
values of a fixed number of cells, for remembering results. A standalone
library under the owner's rule
([above](#reusability-the-libraries-as-standalone-forth-code)): it requires
`portability.fs`, `bounds.fs`, `outcome.fs`, `u32.fs`, `hash32.fs`,
`slab.fs`, `htab.fs` and `module.fs`, knows nothing of Lean, and keeps its
helpers in `lf-lib-private`.

```forth
require src/lib/memo.fs
create sq /memo allot   2 1 sq memo-init drop     \ keys of two cells, values of one
49 7 0 sq memo! drop   7 0 sq memo@ . .           \ -1 49
8 0 sq memo@ .                                    \ 0: no entry
sq memo-free
```

| Word | Stack | Meaning |
| --- | --- | --- |
| `/memo` | `( -- u )` | a memo record's size; the record is the caller's, and may move |
| `memo-init` | `( kcells vcells memo -- outcome )` | an empty memo of keys of `kcells` cells (at least one) and values of `vcells` (none or more), its table made: ok; full (no heap: not live, nothing held); invalid for a bad shape |
| `memo-free` | `( memo -- )` | its blocks given back; the record zero |
| `memo-live?`, `memo-count`, `memo-bytes` | `( memo -- flag \| n \| u )` | whether it may be used; entries; address units held (0 when not live) |
| `memo-find` | `( key memo -- a-addr \| 0 )` | the value cells of the key at `key` (`kcells` cells), or 0: none, refused by the check hook, not live |
| `memo-put` | `( key memo -- a-addr outcome )` | the value cells of key's entry, found or added (key copied, values zero), for the caller to write; 0 and full (no room, admit refused) or invalid (not live), nothing changed |
| `memo-at`, `memo-claim` | `( k1 k2 memo -- … )` | the same with a key of one or two cells on the stack (a memo of one key cell reads only `k1`) |
| `memo@`, `memo!` | `( k1 k2 memo -- x true \| false )`, `( x k1 k2 memo -- outcome )` | the first value cell, read or written |
| `memo-clear`, `memo-empty` | `( memo -- )` | every entry out; `memo-empty` makes a table of more than `memo-small` (1,024) slots small again, its blocks given back |
| `memo-cut` | `( n memo -- )` | the entries from the n-th on taken out, newest first |
| `memo-check!`, `memo-admit!` | `( xt memo -- )` | hooks: `check ( a-addr -- flag )` whether a found value still holds; `admit ( memo -- flag )` whether an entry may be added |

**Algorithm and why.** Entries (key cells, then value cells) in a slab
that doubles as it fills, found by an open-addressing hash table
(`htab.fs`: linear probing, doubled before it is 3/4 full, Algorithm R for
removal) whose hooks hash and compare the key cells. Every key cell is
mixed in by its low 32 bits (Murmur3's finaliser, `hash32.fs`) and by its
high bits when any are set, so 32- and 64-bit hosts find the same entries
and keys that differ only above bit 31 do not collide; keys are compared
cell by cell, never as bytes. The table keeps its hooks' address, so the
hooks are a heap block of their own and a memo record may move (a member
of a checker context does while modules load). A put first makes the
table ready (it may double, even for a key present), then finds, then
asks the admit hook, then grows the entries: the order in which the three
memos it replaced did these steps, so a check's memory meter is charged
exactly as before. Why so: the three copies it replaced (the checker's
result caches, Lean's replace memo, the NDJSON reader's index maps) were
the same table on `htab.fs` and `slab.fs`, each with its own hooks, key
record and emptying; one library with hooks for the two kernel-specific
rules (a kept node is valid only while it has the identity kept with it;
entries are charged to a check's memory limit) serves all three, and the
front end's next.

**Genericity.** The caller chooses the key and value cells, and the two
hooks; keys are given by address, or for one or two cells on the stack.
No order of entries is promised but insertion order for `memo-cut`.

**Scaling.** A find or put costs a hash of `kcells` cells and a few
probes whatever the size (table at most 3/4 full); a put that doubles the
table rehashes every entry once (amortised constant). Memory: an entry is
`kcells + vcells` cells in the slab (up to twice that while it doubles)
plus 4 to 11 bytes of 32-bit slots; at least 16 slots and the hooks'
2 cells. No recursion; a few host-stack cells.

**Speed** (this machine, 2026-11-13, `gforth-fast` 1.0, while a two-job
check ran): 16 keys of two cells put and found 100,000 times with an
`memo-empty` between, 3.2 million operations in 0.38 s (0.12 µs each);
1,000,000 distinct keys put in 0.72 s and found in 0.23 s. `gforth` 1.0:
0.93 s; 1.04 s and 0.42 s.

**Callers** (counted as for the sorts above, on all of `Init`):

| Caller | Key, value (cells) and hooks | Entries when emptied on Init: count; mean; 0–1 / 2–8 / 9–32 / 33–256 / more; largest |
| --- | --- | --- |
| `src/kernel/caches.fs`, the five result caches (inferred types ×2, whnf_core, whnf, unfolding) | (identity, 0) → (node, identity); check: the node still has the identity (`replace-memo.fs`'s `lf-kept-node?`); admit: the check's memory meter | 1,750,307 empties; 20.2; 1,284,190 / 136,440 / 158,586 / 143,520 / 27,571; 45,514 |
| `caches.fs`, the two pair caches (`m_success`, `m_failure`) | (smaller, larger identity) → none; admit as above | 701,894; 9.9; 484,870 / 80,136 / 98,224 / 34,362 / 4,302; 12,844 |
| `caches.fs`, the free-variable memo | (node, identity) → flag; admit as above | 345,757; 77.1; 187,506 / 29,688 / 47,800 / 58,830 / 21,933; 102,937 |
| `src/kernel/replace-memo.fs` (Lean's replace cache, one per pass kind and context) | (identity, offset, stamp) → (result, identity); check as above; `memo-cut` takes a call's entries out | 228,961 empties; 186; 24,860 / 45,237 / 77,995 / 62,744 / 18,125; 469,055 (stamped entries kept up to 2^20). Per call taken out: 22,299,167 calls; 5.6; 10,297,605 / 8,065,922 / 3,158,428 / 773,321 / 3,891; 4,107 |
| `src/import/ndjson.fs`, the index maps (one per record family) | index → ordinal (one cell each) | none: every index of `Init` is its own ordinal, so no map is made (`tests/core/ndjson.fs` makes them) |
| `src/front/offset-walk.fs` (the front end's instantiate1, abstract and instantiateBetaRevRange; reuse pass F2, 2026-11-18) | (node, depth) → image; no hooks; made afresh per walk, as the hash table it replaced | not measured on `Init`: the front end runs on authored text only (`.lf` checks); `tests/front/offset-walk.fs` walks up to 20,000 binders |

**Tests** (`tests/lib/memo.fs`, in `make test-lib`; Gforth 1.0 and 0.7.3;
loaded under `HEX`): the public words and hidden helpers; the header's
example; every shape refused; a memo never made, refused by the heap (its
hooks' block or its table) and freed; keys of one, two and three cells,
differing in any one cell, and in their high bits only (spread over the
table: the compared count); values written over; the check hook (a stale
value a miss, a put finding it again) and the admit hook (asked only for
a new entry, after the table is ready, before the entries grow); the heap
refusing the table's growth (for a key present too) and the entries'
growth; a moved record; cuts, clears and empties (blocks given back, hooks
kept, a refused new table); a new entry's values zero over a cut one's
memory; 4,000 random operations against a model. 12 planted faults
(`lib-memo-…`) each caught; the callers' faults `cache-identity-unchecked`,
`cache-admit-skipped`, `s6a-memo-identity-unchecked` and
`ndjson-index-repeat-ignored` caught by the checker's and the reader's tests.

## Priority queues

`src/lib/pqueue.fs` (2026-11-13, branch `reuse-k1`; library audit action
11; untrusted until reviewed): queues of cells that give back the one that
comes out first by the caller's order. Standalone: it requires
`portability.fs`, `outcome.fs`, `slab.fs` and `module.fs`, knows nothing of
Lean, and keeps its helpers in `lf-lib-private`.

```forth
require src/lib/pqueue.fs  require src/lib/sort.fs   \ sort.fs for sort-signed
create ready /pqueue allot   ' sort-signed ready pq-init drop
7 ready pq-push drop  3 ready pq-push drop  5 ready pq-push drop
ready pq-pop . ready pq-pop . ready pq-count .     \ 3 5 1
ready pq-free
```

| Word | Stack | Meaning |
| --- | --- | --- |
| `/pqueue` | `( -- u )` | a queue record's size; the record is the caller's |
| `pq-init` | `( order pq -- outcome )` | an empty queue by `order ( x1 x2 -- n )`, `sort.fs`'s convention (n > 0: x1 comes out after x2); invalid for an order of 0 |
| `pq-push` | `( x pq -- outcome )` | ok; full when the heap cannot grow, nothing changed; invalid for a queue not accepted or not live |
| `pq-min`, `pq-pop` | `( pq -- x )` | the cell that comes out first, staying or taken out (unchecked: the queue holds a cell) |
| `pq-count` | `( pq -- n )` | cells queued |
| `pq-clear`, `pq-free` | `( pq -- )` | every cell out; the block given back |

**Algorithm and why.** A binary min-heap in a slab: a push moves the new
cell up from the last place past each parent that comes out after it, a
pop moves the last cell down from the root past the child that comes out
first (the right one on a tie, as in the scheduler's heap it replaced, so
the scheduler's queues are the same cell for cell) while that child comes
out before it. A moving cell goes through a hole (each cell it passes
moves into the hole, it is stored once at the end), with the comparisons
and the result of swapping, and the hole and the moving value kept in the
record, so the words pass one item. Why so: the scheduler's queues hold
declaration numbers, pushed and popped in any order, up to one per
declaration; a heap is the simplest structure with logarithmic steps, and
no cell tied by the order is promised an order (a heap is not stable).

**Genericity.** Cells, ordered by the caller's xt (values, or numbers
naming records the order looks up).

**Scaling.** At most about log2 n comparisons for a push and 2 log2 n for
a pop; one cell per cell queued, the slab doubling from 16; no recursion.

**Speed** (as above, `gforth-fast` 1.0): 16 random cells pushed and popped
100,000 times, 1.6 million operations in 0.34 s (0.21 µs each); 1,000,000
random cells pushed in 0.09 s and popped in 1.1 s. `gforth` 1.0: 0.75 s;
0.22 s and 1.9 s.

**Callers**: `src/kernel/env-schedule.fs`, the parallel scheduler's two
ready queues (declaration numbers, `sort-signed`), pushed and popped in
the driving task only. On all of `Init` with `--jobs 2` (counted by a
temporary counter, since removed): 57,919 pushes, the queue then holding
7,049 cells on average and 17,071 at most (0–1: 45, 2–8: 179, 9–32: 293,
33–256: 1,584, more: 55,818); the serial run (`--jobs 1`) schedules
nothing. The scheduler's verdicts and snapshot are the serial run's, the
same as before the change (see [Sorting](#sorting)).

**Tests** (`tests/lib/pqueue.fs`, in `make test-lib`; Gforth 1.0 and 0.7.3;
loaded under `HEX`): the public words and hidden helpers; the header's
example; an order of 0 and a queue never made or freed; signed values,
duplicates, unsigned values with the top bit set, an order with ties;
clearing; the return stack checked; the heap refusing growth (full,
nothing changed); comparisons within 10 a push and 20 a pop for 1,000
cells; 3,000 random pushes and pops against a model and against a copy
of the scheduler's former heap, the same cell out at every pop and the
same heap cell for cell after every step. 6 planted faults (`lib-pq-…`)
each caught.

## Decimal numbers, bits and heap blocks

Batch `reuse-out` (2026-11-13, plan 9.4.8k; 9.4.8b and 9.4.8d): three
small libraries for operations that a dozen modules each wrote by hand.
Each is standalone (it requires only `portability.fs`, `module.fs` or
`outcome.fs`), keeps its helpers private where it has any, and is tested
on Gforth 1.0 and 0.7.3 outside the checker (`tests/lib/decimal.fs`,
`bits.fs`, `blocks.fs`).

```forth
hex ff u>decimal type  -10 n>decimal type  decimal   \ 255-16
s" 1234" digits>u . .                              \ -1 1234
create sorted 2 , 3 , 5 , 7 , 11 ,
: below? ( x k -- x flag ) cells sorted + @ over < ;
6 0 5 ' below? lower-bound nip .                  \ 3: the first not below 6
variable buf  0 buf !  100 buf block-zeroed .      \ 0: ok, zeroed
buf heap-release
```

**Decimal numbers** (`decimal.fs`). *Algorithm*: `in-base` runs a word
with `BASE` set under `CATCH` and restores `BASE` on both paths, passing
a `THROW` on (the hand-written copies lost `BASE` when one came out);
`in-decimal` is `in-base` with ten. The text words build pictured output
inside it, so their text is the host's transient pictured-output buffer
(`u>hex` writes hexadecimal as the host's `#` does, upper case on
Gforth); reading is by hand, digit by digit (`digits>u`, exact or false
when it does not fit a nonnegative cell, leading zeros skipped by
`skip-zeros` once the text is as long as `cell-digits`, so the short
path costs nothing more; `decimal>u`, modulo the cell size), or by
`>NUMBER` inside `in-decimal` (`decimal>number`, `decimal-digits?`). *Genericity*: cells
and double cells, signed or unsigned; any word under `in-decimal`.
*Scaling*: linear in the digits, nothing allocated. *Speed* (`gforth-fast`
1.0, this machine, 2026-11-13, while a two-job test ran): `7 u>decimal`
19 ns, `max-n u>decimal` 112 ns, `digits>u` of 19 digits 19 ns.
*Callers*: diagnostics and reports (`author/errors.fs`, `cli/check-run.fs`,
`cli/leanforth.fs`, `present/name-text.fs`, `present/print-job.fs`,
`import/manifest.fs`, `import/ndjson-emit.fs`, `import/run-record.fs`,
`program/verify-report.fs`, `program/ir-run.fs`'s printed stacks), the
readers of numbers (`import/stage.fs`'s and the kernel's `rec_` test,
`environment.fs`'s auxiliary recursor number, `program/ir-reader.fs`,
`ir-run.fs`, `lib/json.fs`), the kernel's generated names
(`check-block.fs`'s `u_k`, `inductive-nested.fs`'s `_k`), `u>hex` for the
escapes of `present/name-text.fs` and the LaTeX printers
(`present/latex-text.fs`, `statement-forms.fs`), `skip-zeros` for
`bignum.fs`'s decimal reader and `ir-run.fs`'s literals; on Init only the progress line, the report's counts and the
manifest's counts run (numbers below 10^9); sizes per call are not
measured yet (plan 9.4.8g).

**Bits** (`bits.fs`). *Algorithm*: `cell-bits` counts a cell's bits once
by shifting `max-n` right; `log2-ceiling` shifts u-1 right (the smallest
k with 2^k ≥ u); a bit set is a run of cells, bit i in cell i / cell-bits;
`lower-bound` halves lo..hi (Knuth's Algorithm B, TAOCP 6.2.1, in its
"first not below" form), asking the caller's test whether element k is
below the sought one; the midpoint takes hi − lo unsigned, so any signed
range halves (review reuse-out L1: a range wider than `max-n` ran on). *Genericity*: bit indices unchecked (the caller
keeps them in range); the test `( i*x k -- i*x flag )` sees the values
below k (as `all?` gives them), so a search may carry a key and a record;
the elements must be ordered so that the test holds for a prefix.
*Scaling*: bit words constant time; `lower-bound` ⌊log2 (hi − lo)⌋ + 1
tests, no memory, the test, lo, hi and k on the return stack. *Speed*
(`gforth-fast`, as above): `bit-on` plus `bit@` 9 ns; `lower-bound` over
32 cells 34 ns, over 100,000 cells 101 ns. *Callers*: `htab.fs` (its
largest table, its presizing), `cons.fs`, `terms.fs` (presizing the term
table from the stage's counts), `check-run.fs` (the expression table's
size from the file's), the axiom rows of `environment.fs` (a bit per
axiom of the run), the feed's copied-expression map (`feed.fs`, a bit per
stage expression; none set on Init, whose export has no metadata), the reach
tables of the author's export (`reach.fs`, a bit per term and level),
`sha256.fs`, `run-record.fs`, `ir-run.fs` and `leanforth.fs` (the cell
width), the mixed level substitution's reached list (`lower-bound` over
up to 2,259 terms on Init, as the sort's table above) and the feed's
copies (none on Init).

**Heap blocks** (`blocks.fs`). *Algorithm*: a block is named by the cell
that holds its address (0: none); `block-zeroed` allocates at least one
unit, erases and stores; `block-resize` resizes the cell's block or
allocates one for an empty cell; both leave the cell as it was when the
heap refuses (full); `heap-release` frees and zeroes the cell, so a
second release does nothing. *Genericity*: any size; the cell may be a
record field, a variable or a context member. *Scaling*: one `ALLOCATE`
or `RESIZE`, plus the erase for `block-zeroed`. *Speed* (`gforth-fast`,
as above): `block-zeroed` and `heap-release` of 64 bytes 15 ns, of 1 MB
8.8 µs (the erase). *Callers*: the import's maps (`env-import.fs`'s
`ua-new` and its layer declarations, `env-layers.fs`, `snapshot-layer.fs`),
the feed's maps and buffers (`feed.fs`), the reach tables (`reach.fs`),
the author's numbering tables (`export.fs`), the re-exporter's buffer
(`ndjson-emit.fs`), the command line's layer list (`leanforth.fs`), the
program report's text (`verify-report.fs`), and `heap-release`'s many
users (about 40, through `bytes.fs`); on Init the feed's maps (a cell
per level, a bit per expression) are its largest zeroed blocks; sizes
per call are not measured yet (plan 9.4.8g).

## Stacks, outcome loops and index checks

Plan 9.4.8a (2026-11-13; the [library audit](forth-reviews/2026-11-13-library-audit.md)'s
actions 1, 4 and 10): words that dozens of modules had written by hand,
now in `src/lib/slab.fs`, `outcome.fs` and `bounds.fs`. Copies left in
files that in-flight branches edit go in 9.4.8a's part b, the kernel's in
the [kernel] batch 9.4.8e.

```forth
create todo /slab allot   1 cells 1000 todo slab-init drop
7 todo slab-push drop  8 todo slab-push drop
todo slab-pop todo slab-pop todo slab-count      \ 8 7 0
: cell-ok ( addr k -- addr outcome ) cells over + @ 0< 0= flag>outcome ;
create counts 3 , 0 , -1 ,
counts 2 ' cell-ok ok-each nip .                 \ 0 (ok): cells 0 and 1 checked
counts 3 ' cell-ok ok-each nip .                 \ 1 (invalid): cell 2 is negative
3 4 index?  0 -1 index?  9 counts 3 cells-has?   \ true false false
: cell-pos? ( addr k -- addr flag ) cells over + @ 0> ;
counts 1 ' cell-pos? all? nip  counts 2 ' cell-pos? all? nip   \ true false
: small? ( n -- flag outcome ) dup 100 < swap 2/ ?dup if todo slab-push else outcome-ok then ;
40 todo slab-push drop  todo ' small? slab-all?    \ true 0: 40 20 10 5 2 1, all below 100
```

**Stacks on a slab** (`slab.fs`). *Algorithm*: the newest unit of a slab
is the top; `slab-push ( x slab -- outcome )` claims one unit
(`slab-claim`, so the block doubles as it fills) and stores a cell,
`slab-2push ( x1 x2 slab -- outcome )` a pair by `2!`; `slab-pop`,
`slab-2pop` read the newest unit and give it back, `slab-last` is its
address, `slab-drop` gives it back unread. A push is ok, full as
`slab-claim`, or invalid with nothing changed for a slab that is not
live or whose units are narrower than a cell (two); a pop, drop or
`slab-last` of an empty slab, of one whose count is past its capacity
or of one too narrow throws `slab-underflow` (-4132), nothing changed:
every caller tests `slab-count` first, so an empty pop is a fault in
the caller, which must neither read before the block nor leave a count
of -1 (the hand-written pops did both). A pop checks the unit's width
and 1 ≤ count ≤ capacity, which keeps the address inside the block, but
not the seal and generation again: the push that made the unit checked
them, and pops are on the hot path of every walk (review reuse-1a M1). *Genericity*: any slab whose unit holds the value (wider
units hold it at their start); a slab may mix pushes with `slab-claim`d
records, and marks and rollbacks see pushes as claims. *Scaling*: a push
or pop is constant time; growth doubles the block (amortised constant,
`RESIZE` may move it, so an address from `slab-last` is valid only until
the next push); no recursion. *Speed* (this machine, Gforth 1.0 `gforth`,
2026-11-13, load average about 6; the review's benchmarks
`.claude/work/rv-reuse1/probe/bench*.fs`, copied to
`.claude/work/reuse-1b/`): a push, a read of the top (`slab-last 2@`)
and a pop of a pair together 178 ns, against 95 ns for the unchecked
copies they replace and 223 ns while every pop checked the seal again
(before M1); the rest of the difference is the push's checks (liveness,
room, width: a push alone about 100 ns). On whole walks of the front end
(`bench-walks.fs`; median of three runs, alternated): 20,000 `Expr.eqv`
over two different 1000-binder terms 12.4 s, against 10.9 s with the
copies (+14%) and 13.7 s before M1 (+26%); 800 instantiate1 and 800
abstract over 1000 binders and 3,000 headBeta of 300 arguments within
the noise (3.3–3.9 s, 3.3–3.8 s and 0.67–0.76 s for all three trees).
Gforth 0.7.3 about twice as slow.
*Callers* (2026-11-13): the front end's level equality and unification
(`level-simp.fs`, `level-defeq.fs`: pairs still to compare), `Expr.eqv`
(`term-eqv.fs`), `Level.normalize`'s flattening (`level-normalize.fs`),
instantiate and its beta (`offset-walk.fs` for `instantiate.fs` and `beta-inst.fs`: the walks'
pending (node, depth) pairs), `isPropQuick` (`prop-quick.fs`), the goal
printer's groups (`goal-print.fs`), the tactic runner's blocks, parts and
saves (`tactic-run.fs`), and the input's inductive cells
(`core/input.fs`, one push per cell of every inductive block an import
loads: Init's 604 blocks). The front end runs on authored text only, so
its stacks' depths come from the tests (up to 10,000 nested nodes in
`tests/front/meta.fs`), not from an Init check.

**Worklists on a slab** (`slab.fs`; review reuse-1a B2). *Algorithm*:
`slab-all? ( slab xt -- flag outcome )` pops the newest value and runs
the test `xt ( x -- flag outcome )` on it, which may push more onto the
slab, until the slab is empty (true and ok), a test answers false (false
and ok) or one fails (false and its outcome, whatever its flag:
`ok-true?`); `slab-2all?` does the same with pairs and `xt ( x1 x2 --
flag outcome )`. The values not yet tested stay on the slab (the callers
clear it before the next run). A slab that is not live answers false and
invalid, no test run; a slab whose units are narrower than a cell
(`slab-all?`) or a pair (`slab-2all?`) throws `slab-underflow`, as
`slab-pop` and `slab-2pop` do. *Genericity*: any test with that stack
effect; it finds its value (pair) on top and below it the slab and, for
`slab-all?` only, the xt (`slab-2all?` keeps its xt on the return
stack), which it must leave untouched; it may push onto the same slab or
use the return stack (review reuse-1a re-check L). *Scaling*: one pop and one
test per value, newest first (depth first); the pending work lies in the
heap, so no depth needs the host's stacks; constant overhead per value.
*Speed* (as above, `bench-loops.fs`): 50–65 ns a value, the pop
included, against 45–55 ns for the hand-written loop. *Callers*
(2026-11-13): Level.beq (`level-simp.fs`'s `lf-meta-level=`, pairs of
levels), Expr.eqv (`term-eqv.fs`, pairs of terms, a constant's levels
through Level.beq) and isAlwaysZero (`prop-quick.fs`, levels); depths
from authored text (the meta tests compare 1,000-deep terms and levels
and hold 100 pairs waiting; `tests/front/meta-heap.fs` refuses every
allocation of the two pair stacks in turn).

**Loops over outcomes** (`outcome.fs`). *Algorithm*: `ok-each ( i*x n xt
-- i*x outcome )` runs `xt ( i*x k -- i*x outcome )` for k = 0 … n-1 and
stops at the first outcome that is not ok, which it gives; the values
below k are the steps' to read and replace (keeping their number), so
it serves a loop over a table, over a record kept below, and a fold of
several values. `ok-fold ( x n y xt -- x' outcome )` is a fold with a
context: x := `xt ( x k y -- x' outcome )` with the same y each time, the
failing step's x' (often -1) kept beside its outcome, so the front end's
`apply-arg`-style steps run unchanged and folds nest (the job-held step
`aux-step-xt` they replace could not). `outcome-first! ( outcome a-addr
-- )` stores an outcome only while the cell holds ok; `ok-store ( x a-addr
outcome -- outcome )` stores a step's result only on ok and gives the
outcome, x dropped on a failure (one test and a branch). Both loops keep the
xt as the index of an outer `DO` loop run once and read it with `J`, so
a step sees only its own values on the data stack, with no `>R`
juggling around it (Forth-2012 locals are not on Gforth 0.7.3). *Genericity*:
any step with the stated stack effect; n ≤ 0 runs nothing (`?DO` would
wrap round on a negative count); any value outside the vocabulary stops
the loop as a failure. *Scaling*: constant overhead per step, no
recursion; nesting costs two loop frames on the return stack per level.
*Speed* (as above): `ok-each` 6 ns a step at n = 10 and 5 ns at
n = 10^6, against 8 ns for the hand-written `?DO … ok? 0= IF UNLOOP
EXIT` loop; `ok-fold` 12 and 8 ns. *Callers* (2026-11-13): the feed of an
import into the checker (`import/feed.fs`: Init's 577 levels and about
58,000 declarations in one `ok-each` each, the 10 feed steps and 5
shares), the stage and snapshot (`stage-records.fs`, `snapshot-tier.fs`,
`snapshot-layer.fs`: sections and items), the compact store's tiers (5
families each), the scratch marks, the input's parameters, the front
end's generated definitions (`constructions.fs`, `cases-several.fs`,
`ctor-idx.fs`: per binder and argument; Init's inductive types have 0 to
19 constructors, 491 of the 604 one), goals and their printing, the
function information and assignment checks, the printers (notes,
universes, scopes), the author's printing and the CLI's workers and
layers. `outcome-first!`: the front end's walks (`instantiate.fs`,
`beta-inst.fs`, `dag-walk.fs`), the run record, the JSON writer, the
author's export and the re-exporter. `ok-store`: `memo!` (`memo.fs`),
`slab-push` (`slab.fs`), the smart-unfolding bodies' node fields
(`elab-data.fs`: Init's 389 bodies) and the binder name of each
generated `ctorIdx` definition (`ctor-idx.fs`: one call per definition).

**Tests over every index** (`outcome.fs`; review reuse-1a B2).
*Algorithm*: `all? ( i*x n xt -- i*x flag )` runs the test `xt ( i*x k
-- i*x flag )` for k = 0 … n-1 and answers false at the first false
(none runs after it), else true; `ok-all? ( i*x n xt -- i*x flag
outcome )` runs a test that may fail, `xt ( i*x k -- i*x flag outcome
)`, and answers true and ok, false and ok at the first false, or false
and the outcome at the first failure, through `ok-true? ( flag outcome
-- true | false outcome false )`, which never lets a failure read as a
plain false. Both keep the xt as `ok-each` does (`J`). *Genericity*:
any test with the stated effect, the values below k its context to read
(a table, a record, a pair of keys) and keep; a test that starts at 1
adds it to k (`lfr-steps-ok?`, `lines-ok?` pass n − 1; the name store's
`lf-name-entries-from?` passes count − k and adds k, ADR 0005 Amendment 1).
n ≤ 0 gives true (and ok). *Scaling*: constant overhead per index, no
recursion. *Speed* (as above, `bench-loops.fs`): `all?` 6 ns a step at
n = 10 and 3–4 ns at n = 10^6, against 6–7 and 5 ns for the hand-written
`?DO … 0= IF FALSE UNLOOP EXIT` loop; `ok-all?` 11–12 and 10 ns against
12 and 11 ns. *Callers* (2026-11-13): the audits of the name store
(since ADR 0005 Amendment 1, the entries made since its last pass), of a level scope (its universe parameters, pairwise or
hashed) and of a tactic record (each step), the input's universe
parameters (each declaration's), the snapshot's name tuples and
recursor rules (each declaration's) and lines (one per declaration of a
loaded snapshot: Init's about 58,000, in one `all?`), Expr.eqv's
universe arguments (`ok-all?`, each constant's) and the axiom allowlist's names (`ok-all?`, a statement's
constants). The kernel's 4 all-while-ok loops and 3 any-while-ok loops
(`check-block.fs` `lf-blk-indices-free?`, `defeq.fs`
`lf-dq-level-pairs`, `inductive-block.fs` `lf-ind-args-free?` and
`lf-ind-ctors-plain?`; `inductive-block.fs` `lf-ind-some-arg?`,
`inductive-nested.fs` `lf-nest-mentions?`, `whnf.fs`
`lf-whnf-open-args?`) wait for the [kernel] batch 9.4.8e.

**Cutting back** (`slab.fs`; review s1-synth-b B2, 2026-11-13).
*Algorithm*: `slab-cut ( n slab -- )` sets the count back to n, a count
the caller kept at a scope's start, and drops the mark-stack entries
above n, so their marks are refused from then on, as after a rollback
below them; it is a rollback without a mark. A slab that is not live, or
an n outside 0 … count, throws `slab-bad-cut` (-4133) with nothing
changed: the caller saved n, so this is a fault in the caller, never an
outcome (the hand-written `slab-count - slab-commit` it replaces could
set a count past the units claimed). *Genericity*: any slab; the units
above n keep their contents until the next claim. *Scaling*: constant
time apart from the mark entries it drops (none in today's callers);
no recursion. *Speed* (as for runs, [below](#runs)): a cut back by 50
units and the claim of 50 again together 122–134 ns. *Callers* (2026-11-13): the
metavariable context's trail and snapshots at a scope's end
(`mvars.fs`), the tactic runner's restore of blocks, parts and text
(`tactic-run.fs`), the discrimination tree's list cells, keys and texts
(`discr-keys.fs`, `elab-keys.fs`), the discrimination tree's nodes and values on a failed build (`discr-tree.fs`, since MF2+DT)
and the filtered candidates (`instances.fs`), isDefEq's cells and saved
machines (`defeq.fs`), and instance search's seven scoped slabs at each
search's end (`synth.fs`). The kernel's `lf-sch-empty`
(`env-schedule.fs`, a cut to 0) waits for its [kernel] batch. Since
2026-11-14 (review s1-elab B3) also the elaborator's ranges: its pending
list's window, scratch, default instances and goals (`elab-pending.fs`),
an application's arguments and instance metavariables (`elab-app.fs`) and
a `binop%` tree (`elab-term.fs`).

**Taking a unit out** (`slab.fs`; review s1-elab B2, 2026-11-14).
*Algorithm*: `slab-remove ( i slab -- )` moves the units after unit i
down one with `MOVE` and sets the count one less as `slab-cut` does; the
mark entries above i go (review s1-elab re-check M1: a rollback to one
would keep units that moved), a mark at i or below stays; the order of the other units
stays (a stable removal, as Lean's `List.erase` of a pending
metavariable). A slab that is not live, or an i outside 0 … count − 1,
throws `slab-bad-cut` (-4133) with nothing changed. *Genericity*: units
of any size. *Scaling*: linear in the units after i (one `MOVE`), no
scratch, no recursion; a swap with the last unit would be constant time
but would change the order the callers depend on. *Speed* (gforth-fast,
a removal from the middle and a push to keep the size): 78 ns in 4 units,
98 ns in 50, 496 ns in 5,000. *Callers* (2026-11-14), with the sizes of
the S1 files and `tests/front/s1-now.lf` (their golden traces): an entry
taken out of the pending list's window when a default instance fills it
(`elab-pending.fs` `ep-remove`, at most 4 entries), a default instance's
instance binder filled in synthesizePending (`ep-c-remove`, 1 or 2), and
an application's instance metavariable filled by
trySynthesizeAppInstMVars (`elab-app.fs` `ea-inst-drop`, 1).

**Index checks** (`bounds.fs`). *Algorithm*: `index? ( i n -- flag )` is
0 ≤ i < n by signed comparison, false for every i when n ≤ 0;
`cells-index ( x addr n -- i true | false )` a linear search for the first
cell equal to x, `cells-has?` its flag. *Genericity*: any cells; equality
by `=`. *Scaling*: `cells-index` is linear (the callers' tables hold at
most 32 entries: a declaration's universe parameters, an outline line's
sets, `exceptFVars`); a sorted or hashed set is `htab.fs`'s job.
*Speed* (as above): `index?` 3 ns; `cells-index` 51 ns for a miss in 8
cells, 35 µs for a miss in 10,000. *Callers*: `store.fs`, `walk.fs`,
`slab.fs`, `xt-table.fs` (their index checks), `core/reach.fs`,
`front/dag-walk.fs`, `present/log-check.fs`; searches in
`front/lctx-views.fs`, `core/level-scope.fs`, `author/declarations.fs`,
`present/print-forth.fs` and `proof-outline.fs`.

**Tests**: `tests/lib/slab.fs` (every push, pop and refusal, narrow and
dead slabs, a corrupted count, marks over pushes, 40,000 random
operations against a model array; worklists: order, empty, false,
failure with either flag, a full push inside a test, pairs, a dead
slab, too narrow units, return-stack use), `tests/lib/lib.fs` (each
loop's stopping, negative counts, nesting, folds, return-stack use;
`all?`, `ok-all?` and `ok-true?` with every answer; `index?` at its
edges against `within`; searches, `cells-has?`); core and front tests
of their callers (`tests/front/meta-heap.fs`: Level.beq and Expr.eqv
whose pair stacks are refused, at the first pair, in a step and inside
a Sort's levels). 35 planted faults (`lib-slab-…`, `lib-outcome-…`,
`lib-bounds-…`, `core-term-…`, `core-names-…`, `fe-lnorm-…`,
`fe-pairs-all-…`, `fe-eq-push-…`, `fe-level-seconds-…`,
`fe-rec-apply-…`, `imp-emit-…`, and for the review's other findings
`fe-assign-…`, `fe-fun-info-…`, `fe-dag-walk-…`), each caught.

## Name tables

`src/lib/name-table.fs` holds small read-only tables of names that a
module lays down while loading, each entry a name and the caller's data
after it. Its callers: the term printer's name speller (the 139 tokens of
Init's syntax it puts between « »), and since branch `reuse-b`
(2026-11-19, review R1) the command line's options (25 entries) and
commands (11), each a `/cli-entry` record of three cells
(`cli-option-table`, `cli-commands`), `print --statement`'s forms (5,
`pr-form-names`) and the progress line's parts (9, `ck-pline-parts`, each
named by the text that follows it and walked in order with
`name-table-each`). A command line is read with at most a few dozen
lookups, each one a scan of at most 25 entries.

    name-table: colours
    s" red" colours name-entry 1 ,
    s" green" colours name-entry 2 ,
    s" green" colours name-table-find name-entry-data @   \ 2
    s" blue" colours name-table-find                      \ 0

- **Interface.** `name-table: ( "name" -- )` makes an empty table, two
  cells (its first and its last entry); any two cells set to 0 serve too,
  such as a field of a module's own record (`name-text.fs` keeps its table
  in `nt-state`). `name-entry ( c-addr u table -- )` appends an entry: a
  link cell (0 for the last), then the name counted (`counted,`); the
  caller then lays down the entry's data, if any (`,`, `c,`, `allot`),
  before the next entry. Entries of one table may lie apart in the data
  space, with other definitions between them. A name over 255 bytes aborts
  (`ABORT"`, -2) before anything is linked, so the table is unchanged.
  `name-table-find ( c-addr u table -- entry | 0 )` gives the first entry,
  in the order laid down, whose name is c-addr u byte for byte;
  `name-entry-name ( entry -- c-addr u )` and `name-entry-data ( entry --
  a-addr )` its name and the aligned address of its data;
  `name-table-each ( table xt -- )` runs xt ( entry -- ) on each entry in
  order. Loads in decimal whatever BASE is and restores it.
- **Algorithm.** A linear scan of the linked entries from the first, one
  `COMPARE` per entry (most differ at the first byte), stopping at the
  first equal name. Why: the tables are tens to a few hundred names, read
  a handful of times per command or once per printed name, and a scan
  needs no index, no sorting at load time and no memory beyond the table.
- **Genericity.** The caller chooses each entry's data: none, cells, bytes
  or xts, of any size, read through `name-entry-data`; names are any bytes
  up to 255, the empty name included, compared exactly; two equal names
  may both be laid down, and the first is found.
- **Scaling.** Cost grows with the entries before the hit: n compares for
  a miss. No scratch memory, no recursion, no return-stack use beyond the
  call.
- **Measured speed** (2026-11-18, Gforth 1.0.0 `gforth`, WSL2 on the
  development machine): Init's 139 tokens, 0.74 µs per lookup that hits
  near the middle, 2.5 µs per miss or a hit at the end; a 10,000-entry
  table, 182 µs per hit at its end. A table above a few thousand names
  read in a loop wants a hash table (`htab.fs`) instead.
- **Callers.** One: `src/present/name-text.fs` (`nt-tokens`, Init's 139
  tokens, laid down once while loading; one lookup per root component of
  a name the term printer writes, through `nt-part`, and none for the
  reports' names, which are `Name.toString` with no token rule since
  review F3). Tests: `tests/lib/name-table.fs` on its own, and `make
  test-lib` loads the file alone by its full path in hexadecimal and
  checks that BASE comes back.

`find-index ( x n xt -- k true | false )` (`find.fs`, front reuse pass
part A, 2026-11-18, review F4 and the author review's R3) is `any?` giving
the place: the first k whose test xt ( x k -- x flag ) holds, x dropped.
*Algorithm*: a counted loop that stops at the first hit; the xt is kept
as the outer index of a one-pass loop, as in `any?`, so it uses no
return-stack cell of its own. *Cost*: one test per index up to the hit;
no memory. *Speed* (2026-11-18, a test that never holds, load about 1
to 8): 7 ns an index at 10 indices and 4 to 5 ns at 10^6 on `gforth`, 3
to 6 ns and 2 to 3 ns on `gforth-fast`. *Callers*: the authoring finds
of a declaration, level and constant reference (`author/constants.fs`,
`build.fs`; sizes: the declarations, levels and references of the run's
store), the first open goal (`front/goals.fs`), a metavariable mark
(`mvars.fs`), a matcher alternative (`whnf.fs`). The search for a node
to share no longer scans with it: a hash index replaced the scan of the
whole term store (`build.fs`, review reuse-front-a finding 1, 2026-11-18).
*Sizes on a real run* (`leanforth check --snapshot` of Init with
`tests/front/ps-add-comm.lf`, counted 2026-11-18): `lfa-decl-named?` 20
searches of at most 7 declarations (4.45 on average), `gl-open-at?` 33
searches of 1 goal; the other callers were not reached by that text.
Tested in `tests/lib/lib.fs` (both engines); fault
`rfa-find-index-off-by-one`.

`find-last-index ( x n xt -- k true | false )` (`find.fs`, review
tactic-a2ii B3b, 2026-11-18) is the same search from the end, k = n-1 down
to 0 (Lean's `findDeclRevM?`, `findRev?`): the last k whose test holds.
*Algorithm*: the same one-pass outer loop and a counted inner loop
stepping by -1, after a guard for n <= 0. *Cost*: one test per index from
the end down to the hit; no memory. *Speed* (2026-11-18, a test that
never holds): 5 ns an index at 10 indices and 4 ns at 10^6 on `gforth`,
3 and 2 ns on `gforth-fast`. *Callers*: the hypothesis `by-assumption`
takes (`front/meta-tactic/assumption.fs`, the goal's locals, newest first)
and a local found by its name (`front/lctx-views.fs`'s `lf-view-named`);
sizes: a goal's local context, a handful of locals in every checked
`.lf` text (at most 6 in `tests/front/tactics/`); and the last argument
of an application the term printer shows (`present/print-analysis.fs`'s
`lf-pp-last`, plan 9.4.8l Z, which replaced a forward loop that kept
the last hit; sizes: an application's arguments, not measured). Tested in
`tests/lib/lib.fs` (both engines); fault `lib-find-last-skips-last`.

`count-index ( x n xt -- m )` (`find.fs`, review tactic-move-c4 B4,
2026-11-19; `find-index`'s convention since its re-check R1, plan 9.4.8l
Z) counts the k < n whose test xt ( x k -- x flag ) holds, any nonzero
answer counting one; x, one value the test reads (a table, a record, a
code it compares with), is given to every test and dropped; n <= 0
gives 0. A test that reads no value is ( k -- flag ) under any x (0 by
custom), as for `find-index`. It replaced twelve hand-written
`0 n 0 ?do … - loop` loops (the `- loop`, `1 and + loop` and
`if 1+ then loop` spellings). *Algorithm*: the same one-pass outer loop
holding xt as `find-index`'s, and a counted inner loop that runs every
index, x staying below the count, each test given a copy of x above it
(`over i j execute nip`). *Cost*: one test per index, always n; no memory; two loop
frames on the return stack. *Speed* (2026-11-19, Gforth 1.0.0, WSL2 on
the development machine, load about 1): 5 ns an index at 10 indices and
3 to 4 ns at 10^6 on `gforth`, 2 ns at both on `gforth-fast`, whether
the test holds never or every other time. *Callers* and their sizes:
- `front/tactic-alts.fs`: an eliminator's alternatives no `|` wrote
  (`tal-unhandled#`, for Lean's orList in errors 206 and 207: 2 for
  `Nat.rec`, `Nat.recAux` and `List.rec`, the only eliminators a checked
  text reaches) and an alternative's explicit fields (`tal-explicit#`,
  error 208's count: 0 to 2);
- `front/tactics/case.fs`: the unsolved goals with a tag when `by-case:`
  finds none (`tcs-named#`, error 210's hint: 1 or 2 goals in
  `tests/front/s2w-case-*.lf`);
- `front/cases-several.fs`: the minor premises T keeps before minor i
  (`kept-before`, x the job; a few times per casesOn of a mutual or
  nested type, over the recursor's minor premises before i);
- `cli/leanforth.fs` and `cli/check-run.fs`, once per `check` run's
  report, over the input's declarations (all of Init's 59,349 for a
  snapshot of Init): the declarations a carry run checks again
  (`cli-again#`) and again for one reason (`ck-again#`, x the why code),
  the declarations checked here and taken from the snapshot
  (`ck-checked#`, `ck-saved#`, through `ck-inputs-passing#`); once per snapshot
  load, its stage's slots but block records (`ck-stage-slots`, x the
  stage), and the kernel's `env-layers.fs` the same for each layer
  loaded on it (`lay-count`, x the layer's reader; cleanup-families-2);
- `cli/check-lf.fs`: a library constant's explicit binders, the zeros of
  its binder-kinds record (`lfc-zeros`, x the record; one per name the
  natural reader looks up, the constant's binders);
- `present/print-forth.fs`: the visible binders inside binder j
  (`lf-pf-inner#`, one per variable printed as `n var#`; the binders in
  scope) and `present/print-analysis.fs`: an application's shown
  arguments (`lf-pp-shown#`, x the application; one per application
  printed, its arguments);
- `front/goal-print.fs`: the later locals renamed like local i, Lean's
  number for a tombstone (`gp-like`, x the index i, the test
  `gp-later-like?` reading local i+1+k; cleanup-families-2, replacing a
  hand-written loop over i+1 to the view's count; a handful of locals in
  a goal of `tests/front/`).

The sizes of `kept-before`, `lfc-zeros`, `lf-pf-inner#` and
`lf-pp-shown#` were not measured on a real run. Tested in
`tests/lib/lib.fs` (both engines); faults `lib-count-index-raw-flag` and
`lib-count-index-count-as-x`.

`cell-pair@ ( addr -- x1 x2 )` and `cell-pair! ( x1 x2 addr -- )`
(`bounds.fs`, cleanup-families-2, 2026-11-19, plan 9.4.8l AF) read and
write two adjacent cells in the order they lie in memory, x1 at addr:
the reverse of `2@` and `2!`, which keep the top of the stack at addr.
They serve a record's two neighbouring fields read or written together
where a field is also used alone, or where the layout is fixed (a saved
or offset-addressed record, as `constant-references.fs`'s, whose order
must not change); a pair used only whole is one `2 cells +field` read
with `2@` and written with `2!` instead (round 1 of the pair-field
family). They replaced the hand-written `dup A @ swap B @` and
`tuck B ! A !` of duplicate groups 8085, 894e and b380 and the
`2@ swap`, `dup @ swap cell+ @` and `tuck cell+ ! !` spellings.
*Algorithm*: `2@ swap`, whose cell order the standard fixes, and
`tuck cell+ ! !`. *Generic*: any two aligned adjacent cells; unchecked, as
`@` and `!`. *Cost*: constant, no memory. *Speed* (2026-11-19, Gforth
1.0.0, WSL2, load about 5, 10^7 calls): 3 ns a read and 5 ns a write on
`gforth` (a bare `2@` 2 ns), 1 ns each on `gforth-fast`. *Callers*, each
once per use of its record (no size): in the kernel, `caches.fs`
(`lf-cache-stats`, `lf-cent!`), `env-snapshot.fs` (`start@`,
`site-paired`), `env-import.fs` (`entry-same?`), `env-layers.fs`
(`lay-from`), `mixed-open.fs` (`lf-open-remember`), `replace-memo.fs`
(`lf-rmemo-kept`) and `mixed-definition-probe.fs` (`lf-mdreq-claim@`,
`-claim!`, `-value@`, `-value!`); in core, `derivation-log.fs`
(`lf-log-cut`, `lf-log-published`, `lf-log-published!`, `lf-log-at!`),
`constant-references.fs` (`lf-cref-name@`, `lf-cref-name!`,
`lf-cref-pair@`) and `statement-match.fs` (`lf-stmt-push2`,
`lf-stmt-pop2`); in import, `run-replay.fs` (`rp-saved`, `rp-restore`),
`ndjson.fs` (`export-marks`, `export-marks!`) and `ndjson-emit.fs`
(`buffer-text`, its `buffer-used` now beside `buffer-addr`); in the
front end, `elab-data.fs` (`ed-keys@`, `elab-eliminator@`,
`elab-matcher-alts`), `lib-decode.fs` (`lf-libdec-hint`,
`lf-libdec-params`), `synth.fs` (`sy-val!`), `assign-check.fs`
(`ac-set`), `beta-inst.fs` (`ib-xs!`), `instantiate.fs` (`in-xs!`),
`meta-env.fs` (`me-kinds-span`), `tactic-run.fs` (`lfr-set`, its
`trow-plan` now beside `trow-run`), `fun-info.fs` (`lf-meta-param`) and
`telescope.fs` (`lf-walk-kind`); and `bounds.fs`'s own `range-at`.
Later in the same branch, the pairs left of three-field writes:
`derivation-log.fs`'s `lf-log-publish-fields` (slot and dependencies),
`expr-remap.fs`'s `remap-set` and the kernel `defeq.fs`'s `lf-dq-doubt`
(the doubt's two terms).
Tested in `tests/lib/lib.fs` (both engines); faults
`cf2-cell-pair-fetch-as-2at` and `cf2-cell-pair-store-as-2bang`, and a
crosswise fault (`2@` or `2!` in its place) on 27 of the callers (the
other `cf2-` faults of `tests/mutants/faults.toml`), each caught by the
caller's unit test.

`cell-triple@ ( addr -- x1 x2 x3 )` and `cell-triple! ( x1 x2 x3 addr -- )`
(`bounds.fs`, cleanup-families-2, 2026-11-19) are the same for three
adjacent cells, x1 at addr: a record's three neighbouring fields. They
replaced `dup A @ over B @ rot C @` and `tuck C ! tuck B ! A !`
(duplicate groups eb75, bf71, cc68 and aa7d). *Algorithm*: `dup @ swap
cell+ cell-pair@` and `tuck 2 cells + ! cell-pair!`. *Generic*: any three
aligned adjacent cells; unchecked. *Cost*: constant, no memory.
*Speed* (2026-11-19, Gforth 1.0.0, WSL2, load about 6, 10^7 calls): 5 ns
a read and 6 ns a write on `gforth` (the hand-written read 4 ns), 1 and 2
ns on `gforth-fast`. *Callers*, each once per use of its record: in the
kernel, `env-import.fs` (`imp-layer-decls`), `env-snapshot.fs`
(`snap-layer-slots!`) and `env-signature.fs` (`lf-envsig-actuals`); in
core, `terms.fs` (`lf-sought!`, `lf-sought@`) and `derivation-log.fs`
(`lf-log-cref-head!`); in the library, `htab.fs` (`htab-stats`); in the
front end, `elab-data.fs` (`elab-instance@`, `elab-default@`,
`elab-matcher@`, `elab-alt@`, `elab-projection@`), `discr-tree.fs`
(`dt-frame!`, `dt-pop`), `level-params.fs` (`lp-set`), `step-log.fs`
(`lf-steps-write`) and `telescope.fs` (`tl-fill`); in `present/`,
`log-view.fs` (`lv-node!`, `lv-node@`) and `notation-table.fs`
(`lf-nt-places!`). Left as written, each with its reason: `node.fs`'s
`node@` and `node!` and `store.fs`'s `store-shape@` (the term and level
stores' own reads, on every checked access: a call more there is not
worth the saving), and the triples whose fields lie in another order
than the stack's (`bignum.fs`'s `arena-span`, `derivation-log.fs`'s mark
reads, `mvars.fs`'s, `synth.fs`'s and `names.fs`'s sought records,
`json-write.fs`'s `jw-push`, `sections.fs`'s `sec-enter`) and
`ir-run.fs`'s (9.4.8l T). Tested in `tests/lib/lib.fs` (both engines);
faults `cf2-cell-triple-fetch-turned` and `cf2-cell-triple-store-turned`,
and a crosswise fault on 16 callers of the pair and triple words
(`cf2-*-turned`) and on `lv-node@` (`log-view-node-fields-swapped`),
each caught by a unit test (`notation-table.fs`'s `lf-nt-places!` fills a table
while loading, so a crosswise store there stops the load).

`one-of2? ( x a b -- flag )` and `one-of3? ( x a b c -- flag )` (`bounds.fs`,
cleanup-families-3, 2026-11-19): whether x equals a or b, or one of a, b and
c, in place of the hand-written tests `dup a = swap b = or` and `dup a = over
b = or swap c = or` of a kind, tag, mode or character against constants.
*Algorithm*: the comparisons in turn, their flags or-ed (no early exit: two or
three `=` cost less than a branch); `one-of3?` is one comparison and
`one-of2?`. *Generic*: any cells compared with `=`; the flag is well formed.
*Cost*: constant, no memory. *Speed* (2026-11-19, Gforth 1.0.0, WSL2, load
about 1.5, 10^7 calls): `one-of2?` 7.7 ns a call on `gforth` (the
hand-written phrase 3.9 ns), 2.7 ns on `gforth-fast` (1.2 ns); `one-of3?` 15
ns (6.7 ns), 6 ns (1.7 ns). *Style*: the two words hold four return-stack
operations (`>r` ... `r>`, `2>r` ... `2r>`), which raise `bounds.fs`'s count
in the style ratchet from 2 to 6 (its baseline 3: a reviewed raise). So the kernel's reducer and
inner loops keep the phrase (`whnf.fs` `lf-whnf-valued?`, once per delta
step; `mixed-open.fs` `lf-open-rev?`, once per bound variable opened), and so
does `program/ir-run.fs` (its SHA-256 is evidence of the clamp receipt, 9.4.8l
T). *Callers*, each once per use, found and rewritten by `check-duplicates.py
--rewrite`: `one-of2?` in core (`derivation-log.fs` `lf-log-level-leaf`, which
check_log_isolation.py allows; `tagged-sort-boundary.fs` `lf-repr-mode?`), the
kernel (`caches.fs` `lf-short?`, shared by `lf-ci-short` and `check-declaration.fs`, `env-schedule.fs`
`lf-sch-waiting?`, `environment.fs` `lf-kind-bare?` and `lf-env-quot-open?`),
the front end (`defeq.fs`, `discr-keys.fs`, `elab-app.fs`, `elab-keys.fs`,
`infer.fs`, `instances.fs`, `lib-decode.fs` twice, `meta-env.fs`,
`tactic-syntax.fs`, `unfold.fs`), `present/` (`log-check.fs` twice,
`log-view.fs`, `print-analysis.fs`, `proof-outline.fs` twice, `latex-text.fs`
`lf-tex-angle?`), the library (`json-write.fs`'s `jw-listing?`,
`jw-value-state?`, `jw-flag?`) and `program/` (`ir-reader.fs` `ir-blank?`,
`ir-naming?`; `verify-runner.fs` `pv-settled?`): 30; `one-of3?` in core
(`input.fs` `lf-kind-valued?`), the kernel (`env-import.fs` `unrepeatable?`),
import (`feed.fs` `feed-member?`, `stage-records.fs` `valued?`), the front end
(`elab-keys.fs`, `elab-term.fs`, `lib-decode.fs`, `whnf.fs`
`wc-const-inert?` and `wc-at-most-i`) and `present/log-view.fs`: 10 (the
last four of each by hand after the review of 2026-11-19, R1). Duplicate groups 361de2c5,
9daea91f and 1f0b6202 gone. Tested in `tests/lib/lib.fs` (both engines):
each place, none, a value equal to both, the stack below kept; faults
`cf3-one-of2-both` and `cf3-one-of3-third-lost`; the callers' own faults
(nine, re-targeted by the rewrite) still caught.

`cell-spend? ( a-addr -- flag )` (`bounds.fs`, cleanup-families-3,
2026-11-19): one unit taken from the count at a-addr while it is above zero
(true), else false and the count unchanged: a fuel or work budget spent one
step at a time. It replaced three copies of `X @ dup 0> if 1- X ! true else
drop false then` (duplicate group d8a6e1b0): the front end's `wc-spend`
(whnf.fs) and `de-fuel?` (defeq.fs), and core `derivation-log.fs`'s
`lf-copier-spend` (allowed by check_log_isolation.py, whose rule 4 counts it
as a store after a field); after the review of 2026-11-19 (R1) also
`present/print-job.fs`'s `lf-pp-spend` (the printer's fuel), the front end's
`lf-meta-spend?` (meta-config.fs, a declaration's budget) and `lfr-spend?`
(tactic-run.fs, a tactic run's fuel, then the declaration's): 6. `lib/walk.fs`'s `walk-spend?` keeps its own test
(`0=`: a negative budget there is spent, not refused). *Algorithm*: fetch,
test, `+!`. *Generic*: any cell holding a signed count. *Cost*: constant, no
memory. *Speed* (2026-11-19, Gforth 1.0.0, WSL2, load about 7, 10^7 calls):
about 5 ns a call on `gforth` and 2 ns on `gforth-fast`, the same as the
colon words it replaced. Tested in `tests/lib/lib.fs` (both engines): two
units spent then refused, a negative count refused and kept, the stack
effect; faults `cf3-cell-spend-at-zero` and `cf3-cell-spend-unspent`; the
callers' faults `fe-whnf-fuel-unspent` and `fe-defeq-fuel-unspent`
re-targeted and caught.

## Tables of texts

`src/lib/texts.fs` (front reuse pass part A, 2026-11-18; review F10 and
s2-finish L1): `texts-begin ( -- table )`, `texts+ ( "text ..." -- )`
(the rest of the line), `text, ( c-addr u -- )`, `texts-end`, `text-next`
and `texts-find ( x xt table -- entry | 0 )` with the caller's test
xt ( x c-addr u -- flag ), for instance `lf-name-dotted?` or
`lf-meta-const-named?`; `texts-index ( x xt table -- i | -1 )` (review
s3a-decide B4, 2026-11-19) is the same search giving the hit's index, 0
for the first entry, counted during the one pass (a table of names that
stand for numbers). *Algorithm*: a run of counted texts in the
dictionary, searched in order: these tables hold tens of names and are
read a few times per declaration, so neither hashing nor sorting pays.
*Generic*: any one-cell key and any test; texts of 1 to 255 characters.
*Cost*: one test per text up to the first hit; the table's bytes only.
*Measured* (2026-11-18, 10^6 searches of a 13-text table with a
`compare` test, the hit last): gforth-fast 0.11 s (0.12 s for a miss),
gforth 0.16 s (0.19 s); `texts-index` (2026-11-19, 10^6 searches of
`core/nat-ops.fs`'s 14-name table with a `compare` test, the hit last,
load average 3.5): gforth-fast 0.12 s (`texts-find` 0.12 s), gforth
0.24 s (0.18 s). *Callers*: `front/meta-env.fs` (canUnfoldAtMatcher's
13 names, the UInt types and operations, Eq's ndrec names: once per
`getUnfoldableConst?` of a matcher's head), `front/nat-offset.fs`
(evalNat's 16 other operations, per arity) and, with `texts-index`,
`core/nat-ops.fs` (the 14 Nat operations' names, once per Nat.x head the
kernel's or the front end's whnf meets at two arguments). Tested in
`tests/lib/texts.fs` (both engines); faults `rfa-texts-next-skips`,
`rfa-matcher-name-lost`, `s3a-texts-index-from-one`,
`s3a-texts-index-miss-zero`.

## Runs

`src/lib/runs.fs` (plan FE1g-1; `run-each` and `run-filter` after review
s1-synth-b B1, 2026-11-13): sequences of cells that never change, the
persistent values Lean keeps a local context's declarations and a goal
list as.

```forth
0 7 run-push drop  dup 8 run-push drop   \ [7] and [7 8], one cell shared
over 9 run-push drop  rot drop           \ [7 9]: [7] copied to the top
run-cat drop                             \ [7 8 7 9]
: sum ( n x -- n' outcome ) + outcome-ok ;
: odd? ( x -- flag ) 1 and 0<> ;
0 over ' sum run-each drop .             \ 31
' odd? run-filter drop run-count .       \ [7 7 9]: 3
```

*Algorithm*: a run is a handle to a record (its first cell and count) of
one slab of cells that is only appended to, so a run never changes and
runs share cells: `run-push` appends in place when the run ends at the
top of the cells, else after a copy of it; `run-take` and `run-after`
make a record without copying; `run-cat` joins in place when the second
run begins where the first ends. `run-each ( i*x run xt -- i*x outcome
)` walks the run's cell numbers with `?DO`, the step `xt ( i*x x -- i*x
outcome )` kept as the index of an outer loop run once and read with `J`
(as `ok-each`), so a step sees only its own values, and stops at the
first outcome that is not ok. `run-filter ( run xt -- run' outcome )` is
a `run-each` whose step appends each cell the test `xt ( x -- keep? )`
keeps at the top of the cells, from the count it noted at the start, and
makes one record of them at the end (one run, not a push per cell). Its
rule: the test appends no cells, or they would join the new run's; the
step compares `runs-cells` before and after each test and answers
invalid, no run made, when they differ (review s1-synth-b re-check L-b).
*Genericity*: any cells; a step of `run-each` may make runs (cells are
only appended, so the numbers it walks stay valid) but must not reset
them; a filter's test may make runs of no new cells (`run-take`,
`run-after`) but no cells; a filter's run is new even when every cell is
kept. *Scaling*: `run-each` is constant time per cell; `run-filter` adds
one append per kept cell and two reads of the count per cell (the slab
doubles, amortised constant) and its cells stay until
`runs-reset`, as every run's do; no recursion, two loop frames on the
return stack. *Speed* (this machine, Gforth 1.0 `gforth`, 2026-11-13,
load average about 4; `bench.fs` in `.claude/work/SYB/`, two runs): `run-each` with a
step that adds 31–34 ns a cell at n = 10 and 16–19 ns at n = 10^6,
against 34 and 30–39 ns for `ok-fold` over `run@` (the walks it
replaces); `run-filter` keeping half the cells 102 ns a cell at n = 10
and 75 ns at n = 10^6 (an append per kept cell and one record), with its
rule checked 105–108 and 87 ns (2026-11-14, load average about 1.3).
*Callers and their sizes* (2026-11-13): instance search (`synth.fs`):
the waiters an answer wakes and the answers a waiting consumer is given
(`run-each`), the older answers a new one is compared with (`run-each`,
isNewAnswer) and a consumer's subgoals not yet assigned (`run-filter`,
consume); the tactic framework's unsolved goals (`goals.fs`,
`run-filter`) and the goal printer's list (`goal-print.fs`,
`run-each`); the local contexts (`lctx-views.fs`) and goal lists
(`goals.fs`) push, take and join. On Init's 30 searches of `make
reference-synth` (`runsize.fs` in `.claude/work/SYB/`, a wrapper that
counts the runs walked): 53 `run-each` calls over 21 cells in all (32 of
an empty run, 21 of one cell) and 59 `run-filter` calls over 38 cells
(21 empty, 38 of one cell): Init's searches have at most one waiter, one
answer and one subgoal left at a time. Goal lists hold the open goals of
a tactic proof (the tests' longest: a handful).

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

### The shared Nat table (`src/core/nat-ops.fs`)

Plan S3a (2026-11-19) moved the kernel's operations on literal leaves out
of `src/kernel/reduce-nat.fs` and the operation names out of
`src/kernel/whnf.fs` into `src/core/nat-ops.fs`, so that the kernel's
`reduce_nat` and the front end's `reduceNat?` (`src/front/reduce-nat.fs`)
compute the same fourteen operations alike. LeanForth-specific: it reads
literal leaves of the term store (`core/literals.fs`) and makes Lean's
constants (`Bool.true`, `Bool.false`), so it lives in `core/`, not `lib/`.

- **Algorithm.** `lf-nat-lit-op ( a b i -- node outcome )` copies the two
  literals into a scratch arena on the heap, runs the `lib/bignum.fs`
  word (`big+`, `big-`, `big*`, `big-pow`, `big-gcd`, `big-mod`, `big/`,
  the bit operations and shifts, `big=` and `big<=` for `Nat.beq` and
  `Nat.ble`), makes the result a new literal (or the Bool constant) and
  frees the arena. `lf-nat-op ( name -- i | -1 )` maps `Nat.add` ...
  `Nat.shiftRight` to the index (a `lib/texts.fs` table).
- **Generic.** Any literals; an operand that is no literal leaf is
  invalid, no node made (plan 9.4.8l AW, 2026-11-20). The callers keep
  their policies, run through `lf-nat-lits-by ( a b i xt -- node outcome )`
  only once both operands are literals: the kernel refuses a count of
  2^32 or more (`get_count_arg`), Meta answers an exponent above 256
  unsupported (`checkExponent`, plan S3b ports its warning). A result
  over Lean's 2^30 bits, an estimate over it, or a refused arena is full
  (diagnostic 93), never a value.
- **Cost.** The arena is `8 (|a| + |b|) + 64` cells for an ordinary
  operation; `pow` and `shiftLeft` size it from the result's estimated
  bits (6 cells a limb, the operands twice, 4,096 more). Time is
  `lib/bignum.fs`'s; no recursion.
- **Measured** (2026-11-19, this machine, Gforth 1.0 / gforth-fast): 10,000
  products of small literals 27 / 8 ms (about 2.7 / 0.8 µs each, the
  arena's allocation included); `3 ^ 100000` (158,497 bits) 9 / 2 ms, its
  square 13 / 3 ms, its gcd with 1000 under 1 ms. The operands' test
  (2026-11-20, plan 9.4.8l AW): two tag reads per test, made twice on the
  kernel's path (`lf-reduce-nat-binary`, then `lf-nat-lit-op`); 100,000
  kernel products of small literals, the least of 18 runs on a loaded
  machine, 236 → 273 ms on Gforth 1.0 and 90 → 96 ms on gforth-fast
  (lf-nat-lit-op alone and Nat.ble within the noise); end to end within
  the noise (`make test-kernel-reduction`, the decide check, the demos).
- **Callers.** The kernel (`kernel/reduce-nat.fs`'s `lf-reduce-nat-binary`
  through `lf-nat-lits-by`, `lf-reduce-nat-succ`, and `lf-reduce-nat-pred`
  for a literal of several limbs; that word refuses anything but a literal
  above 0 before it reads it, and `lf-reduce-nat-constructor` anything
  but a literal, review L1 of AW; `kernel/whnf.fs`'s name
  tests), every literal operation of a check (the sizes a check of Init
  passes are not measured yet); the front end's `reduceNat?`
  (`lf-meta-nat-fold` through `lf-nat-lits-by`; by-decide's group A:
  one-limb operands, `2 ^ 64` the largest result).

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

## Resetting a hash table

`htab-renew ( htab xt -- )` (`htab.fs`, reuse-out-2 and ROUT3) empties a
table that a run may have grown. *Algorithm*: a live table of at most
`htab-small-slots` (1,024) slots is cleared (`htab-clear`, its slots
erased, its size kept); a larger one, or one that is not live, is freed
and made again by the caller's xt at its first size (16 slots), so that one
large run does not leave every later run a large block to erase.
`htab-small? ( htab -- flag )` is its test; `memo.fs`'s `memo-empty`
uses the same cut-over (`memo-small` is `htab-small-slots`).
*Genericity*: any table; the xt makes the caller's table with its own
hooks. *Cost*: a clear erases 4 bytes a slot; a remake is one `FREE` and
one `ALLOCATE` of 64 bytes. *Speed* (`gforth-fast` 1.0, this machine,
2026-11-14, `tests`-style probe of 100,000 calls each): a clear of 16 slots
6 ns, of 1,024 slots 33 ns, of 2,048 slots 59 ns, of 16,384 slots 430 ns;
a free and remake of 16 slots 36 ns. So the cut-over sits where a clear
costs what a remake does, and a table that grew past it pays the remake
once instead of an ever larger erase at every reset. *Callers*: the term
table (`terms.fs`'s `lf-term-table-empty`, at each store reset), the level
table (`levels.fs`), the constant-reference table
(`constant-references.fs`), the audit's pair set
(`constant-term-boundary.fs`'s `lf-pairs-reset`, at each walk that keeps
depths) and the comparison's pair set (`mixed-compare.fs`'s
`lf-meq-reset`, at each structural equality) and the stored names' index
(`names.fs`'s `lf-name-table-empty`, at each name reset; ADR 0005
Amendment 1: one entry per stored name, 26,701 in a `.lf` check against
Init through the snapshot, so its table grows to 65,536 slots and is
made again at the next reset). *Sizes on Init* (a copy of
the branch at `6f351f80` logging each call, `bin/leanforth check --json
--no-manifest --jobs 2`, 2026-11-14; 4% of the lines, two workers writing
at once, unreadable and left out): the comparison's pair set about 1.47
million resets, every table at most 512 slots (95% of them at 512), so
always cleared; the audit's pair set 1,295 resets, at most 256 slots; the
term table 8 resets, one at 2,048 slots, remade; the level table 7, at
most 1,024 slots; the reference table 4, one at 131,072 slots, remade
instead of erasing 512 KB.

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

## The discrimination tree (front end)

`src/front/discr-tree.fs` (plan slice MF2+DT, branch `mf2-dt`, tested alone,
2026-11-18) is the index of the simp and rewriting library
([LF_LIBRARIES.md](../design/LF_LIBRARIES.md) §3, appendix B): Lean
4.35.0's `DiscrTree` over the elaboration data's keys
(`src/front/elab-keys.fs`). LeanForth-specific, so a front-end module, not
a `src/lib` library: its keys are Lean's, made by `discr-keys.fs`
(`mkPath`, `getUnifyKeyArgs`). Moved out of `src/front/instances.fs`, where
the same trie was private (FE1e3); simp's lemma sets (SP1b) are its next
caller.

- **Algorithm.** A tree record holds Lean's root map (a `lib/htab.fs`
  table of root numbers, keyed by `elab-key=` and `elab-key-hash`) and the
  tries: nodes (key, parent, children, values) and value cells in slabs.
  `insertCore` descends by the keys after the root's, making missing
  children; `insertVal` replaces an equal value in place, else appends.
  Lean keeps a node's children sorted by `Key.lt` and finds one by binary
  search; `Key.lt` needs Lean's `Name.hash`, so here children stay in
  insertion order (Lean's stored order when inserted in Lean's rank order,
  as the instance data are), the star child is kept apart, and a child is
  found through a second `htab` keyed by (node, key) (performance scan
  A5). `getUnify` gives the star root's values first (Lean's
  `getStarResult`, Main.lean:561; the star root is kept apart, so this
  is one read), then runs Lean's process from the key's root on an
  explicit frame stack: no host recursion.
- **Genericity.** Values are one cell, compared by `=`; any key of
  `elab-keys.fs`; any number of trees, each in its owner's record. A
  root can be built at its first query by the owner's builder (the
  instance table checks the root's records first; the star root is
  built at every root's first query); a failed build keeps nothing
  (nodes, cells and child-table entries since its mark). Not reentrant
  on one tree; a builder may query or fill other trees, the query's tree
  and output slab being put back after it.
- **Cost.** An insertion costs one root lookup and one child lookup per
  key (each a few probes), plus a walk of the node's values (as Lean's
  `insertVal`); a query visits the nodes whose keys may unify. Memory: 8
  cells a node, 2 a value, 2 a root, and the two tables' 4-byte slots
  (at most 3/4 full).
- **Measured** (gforth-fast, this machine; `tests/front/dt-bench.fs`, and
  `tests/front/inst-time.fs` for Init's sizes below): n
  values under one root, each with a child of its own, inserted then
  inserted again (every child found): 300 in 0.35 ms then 0.16 ms; 3,594
  (Mathlib's largest root) in 4.8 ms then 1.7 ms; 7,000 in 9.8 ms then
  2.6 ms.
- **Callers and sizes.** The instance table (`instances.fs`): on Init
  (2,938 instances and left-out ones: 277 roots), S1's 13 getInstances
  problems and 29 searches build 35 roots, 896 nodes and 579 values, the
  widest node with 114 children; Mathlib's roots hold up to 3,594 records
  (MATHLIB_FRONT appendix B; not measured here).

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
| `spawn-limit! ( n -- )` | -1 (no limit but the host's) | For tests: the host refuses every worker beyond n running, as it refuses a thread near its process limit (`ulimit -u`), so that tests reach that failure deterministically; read while the pool starts |

When the host refuses a worker (no thread near the process limit, no
memory for its stacks), the pool keeps the workers it made before and
runs with them, trying no more until it is stopped; `workers-running ( --
n )` gives how many run. Results never depend on the number of workers,
so this changes only the speed; `pool-start` (and so `job-submit`) is
refused with `task-no-worker` only when not one worker could be made. A
Gforth 1.0 task whose thread was refused has its two pipes closed (its
stacks stay allocated: Gforth has no word that frees a task that never
ran); a Gforth 0.7.3 task is freed. `job-wait` refuses job 0, the handle
a refused submission gives, with `task-refused`, and reads nothing: on
2026-11-13, near the process limit, `tests/lib/task.fs` waited for such a
0 and crashed in `job-await`.

| Refusal (job 0) | Code |
| --- | --- |
| not a context, the main context, the caller's current context, a context another job owns, or a submission inside a job (`job-wait` inside a job gives the same) | `task-refused` (-4098) |
| the queue holds `task-queue-jobs` jobs | `task-queue-full` (-4099) |
| not one worker task or thread could be created (when some could, the pool runs with those) | `task-no-worker` (-4100) |
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

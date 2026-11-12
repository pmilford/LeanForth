# Backlog Forth review FRI: src/import, src/core, src/lib (2026-11-12, main 3ac0558)

Reviewer: forth-reviewer (Opus), brief `.claude/work/briefs/FORTH-REVIEW.md`. Saved by the coordinator, condensed.
Read all 68 files, most attention on code changed since fcce360 (lib/sections.fs, import/snapshot-tier.fs,
snapshot-layer.fs, core/terms.fs, constant-references.fs, constant-term-boundary.fs, feed.fs, ndjson.fs, the
derivation-log copier). Ran (Gforth 1.0, exit 0): tests/lib lib, sections, bytes, cons, slab, htab, json; tests/core
snapshot-tier, ndjson. Not run: make test/check, Gforth 0.7.3, a 32-bit host; no block coverage (make coverage broken).

## 1. Verdict and findings

Mostly well factored with real Forth idiom: 72% of words 1-2 lines, none over 10, every word with a stack comment, no
locals, the 7 VARIABLEs are load-time registries; defining words (`shape:`, `slot-check:`, `visit:`, `nd-family`),
BEGIN-STRUCTURE, ordered step tables; lib/sections.fs (new) is a model. The debt is stack depth: 170 PICK and 4 ROLL
(42 PICKs in snapshot-layer.fs); 186 of 4,417 words take 4 or more stack items (up to 6). Also raw record offsets in
four places, ~60 copies of `dup ok? 0= if nip … exit then drop` beside the existing `ok-then?`, and IF chains where
CASE or a table belongs. Worst files: import/snapshot-layer.fs, core/constant-references.fs, core/derivation-log.fs
(copier), import/feed.fs, import/stage-records.fs. None of the findings was reproduced by running code.

- **F1 medium:** running out of memory is reported as malformed input in snapshot-layer.fs (199, 206, 281-341): outcomes
  turned into flags make a *full* from `tuple-start`/`-add`/`-end` (lib/pools.fs:76-93) an *invalid*; the header (31)
  and ADR 0008 promise full. Fails closed. Fix: return outcomes all the way (`ly-xlate`, `ly-field`, `ly-xlate-decl`).
- **F2 low-medium, 32-bit hosts only:** additions in bounds checks can wrap (`ly-bytes` 133, `ly-starts` 175 can loop
  forever, `ly-base-at` 289). Fix: `span-in? ( off len limit -- flag )` in lib/bounds.fs.
- **F3 low:** `lf-cref-unreached` (constant-references.fs:332-335) leaves `lf-cref-ungated` set if a hook THROWs;
  pass the gate in, or restore it under CATCH.
- **F4 low:** `sections-info` (sections.fs:376) does not check i < `sections-count`.
- **F5 portability:** `u<=` (ndjson.fs:458) is a Gforth extension not in portability.fs.

## 2. Refactoring batches (behaviour-preserving; fuel and verdict comparisons before and after)

- **B1** import/snapshot-layer.fs (medium, reader of untrusted files): F1; a `/ly-fam` per-family record removing
  most PICKs and every 4-item word; `ly-blame` instead of 4-input `ly-note`; one `ly-step` with a builder table for
  three identical step words; a field table for `ly-xlate-decl`.
- **B2** core/terms.fs, levels.fs, constant-references.fs (medium-high: sharing changes fuel): one `/lf-key` record for
  `lf-tin-key`, `lf-term-key`, `lf-level-key` (removes the duplicate `lf-tfields=`/`-hash`); a `/lf-ckey` record for
  the constant-reference keys (6-input words go); guarded `3dup` in portability.fs; untangle `lf-tin-given`; name
  `lf-tin-let-lam?`; F3.
- **B3** core/derivation-log.fs copier (low-medium): a `/lf-memo` record for the raw offsets; untangle
  `lf-copier-pair`.
- **B4** import/feed.fs (medium: fuel parity): `/feed-copy` record; a per-tag rule table for `feed-to-copy?`;
  `feed-leaf0!` instead of `0 3 roll`; `feed-args` without `5 pick`/`4 pick`.
- **B5** core/statement-match.fs (medium: the axiom allowlist's statements): CASE for the one-letter IF chains.
- **B6** lib/outcome.fs then every module (low per site): `ok-then3?`; one public `outcome-steps` for the three step
  runners (sec-run, steps-run, tf-* tables); `outcome-each` for ~10 copied loops.
- **B7** deep PICKs elsewhere (snapshot-tier `lines-ok?`, stage-records `tuple-item,`/`list-items,`, stage.fs:218,
  run-replay `rp-twice?`, compact-names); stage-records.fs:329 `item,` unchecked 8-cell buffer.
- **B8** core/constant-term-boundary.fs (high: the fail-closed audit; fuel pinned): `/lf-unit` record; delete the
  6-input `lf-walk-unless`.

## 3. Test gaps

import/snapshot-layer.fs is the largest: no unit test file, 8 CLI tests, 1 planted fault. Class 2 forged layers
(bytes outside or overlapping the pool, list lengths past a section, non-start list users, a let without its body,
forward/self references, nonzero payloads, wrong kind data, unknown kinds); class 5 limits during `ly-records`/
`ly-decls` must give full (fails today, F1); class 6 `ly-free` after failure, reload; class 3 stack effects → new
tests/core/snapshot-layer.fs and faults (bounds in `ly-bytes`, end check in `ly-starts`, body tag, zero payload,
start marker). No planted fault at all: lib/bytes.fs (the first trust boundary: overlong UTF-8, surrogates, BOM),
lib/sections.fs, lib/outcome.fs (`flag>outcome` with `0<>`), core/name-equal.fs, lib/u32, walk, frame, task,
core/diagnostics, import/load, ndjson-count, ndjson-emit. Class 5 cell width: no 32-bit host; add a load-time switch
forcing sections.fs's 32-bit path and `span-in?` tests with `max-n`. Before B2: sharing pins; before B3: memo
collision and truncation cases; before B5: odd tokens. Well covered: ndjson.fs, snapshot-tier.fs, sections.fs, bignum.

## 4. Libraries

Outside src/lib: a sparse cell-to-cell map (ndjson.fs:214-277) → lib/intmap.fs; structural JSON comparison
(run-replay.fs) → lib/json-compare.fs; a bit set and binary search (feed.fs:205-222); `lf-term-log2`; bounded stacks
(derivation-log.fs); the step runners (B6). No usage example in the header: json.fs, bytes.fs, u32.fs, walk.fs,
node.fs, context.fs. Tested only inside other tests: module.fs, pools.fs; bounds, node, walk, frame, outcome, u32 in
tests/lib/lib.fs. Every lib file requires only ./ files; task.fs requires Gforth's tasker.fs by design.

## 5. Portability

`u<=` (F5); bytes.fs:81-85 picks Gforth's `scan` with `environment?` outside portability.fs (portable fallback
exists); other host adapters outside portability.fs: run-record.fs:413-420, ndjson-count.fs:201-202,
ndjson-emit.fs:490-491, task.fs (up@, rp@, pause, bounds, defers). 32-bit wraps (F2); `u32s` assumes 8-bit chars.
No byte-order leaks (only `u32-le@`/`u32-le!` give fields a byte layout).

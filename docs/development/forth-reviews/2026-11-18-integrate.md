# Forth review: integration of names-index, lib-tidy-3 and reuse-front-a3 (2026-11-18)

Range `f72422c9..3d73f7e0` (merges fc1360d0, 13863054, 22120e07, plus f44a406a and 3d73f7e0). Reviewer:
forth-reviewer (Opus), independent of the integrating agent. Only what the integration wrote or resolved was
reviewed; the three branches have their own reviews ([names-index](2026-11-18-names-index.md),
[lib-tidy](2026-11-18-lib-tidy.md), [reuse-front-a](2026-11-18-reuse-front-a.md)).

**Verdict: approve with follow-ups.** 0 blocking findings, 3 low, 2 notes.

## Findings

1. Low. `src/core/terms.fs:135` `lf-tag-bit` is `1 swap 31 min lshift`: a negative (corrupt) tag shifts by a
   negative count, which Forth-2012 leaves undefined (note 8 of the reuse-front-a review, still open). Fix
   `: lf-tag-bit ( tag -- mask ) 0 max 31 min 1 swap lshift ;` under the [kernel] gate. Plan 9.4.8n.
2. Low. Fifteen faults besides the narrowed `wrapper-fault-exits-0` still run the whole
   `tests/cli/test_leanforth.py` (327 s against the fault runner's 120 s limit); three are in `bin/leanforth`
   (`wrapper-takes-host-status`, `wrapper-checked-ignored`, `wrapper-fast-beside-ignored`). Narrow each to its test
   class. Plan 9.4.8n.
3. Low, reuse. `true lf-pjob lf-pjob-full !` is in the new `lf-pp-full!` (`print-names.fs:42`) and at
   `print-job.fs:212`: define `lf-pp-full!` in `print-job.fs` beside `lf-pp-full?` and call it there. Plan 9.4.8n.
4. Note. `tests/duplicates-baseline.json` group 631a9f55bad7 still lists `lf-name-find-num` and `lf-name-find-str`,
   which names-index deleted; drop it at the next baseline update.
5. Note. Fault `ni-printer-chain-unchecked` is caught only because its test hangs and times out.

## Checks made

- `print-names.fs:26-60` (the conflict resolution): `Foo.«a.b»` prints, 11 bytes; 64 `«a b»` parts print, 65 end
  full with nothing printed; a forward prefix and a self-cycle end invalid with nothing printed and no hang.
- Library headers: `hash-3`'s example equals the steps by hand; the interface lists match the public words; the
  private helpers of `name-table.fs` and `texts.fs` are not visible after `require`; `tests/lib/test_standalone.py`
  passes over 38 files.
- The new `dw-new?` test is deterministic and tests that nothing is read past `dw-size`;
  `test_5_broken_gforth` catches `wrapper-fault-exits-0` for the right reason; `scripts/mutants.py --only` caught
  the three faults.
- reuse-front-a review: findings 1 and 2 closed on this head; 3-5 in plan 9.4.8n.
- Conflicts git would not flag: none (no name newly defined in two files; no module outside `src/lib` opens
  `lf-lib-private`; the removed linear name finds have no callers).
- Style: 72 words in the five files, 80% of one or two lines, none over five, no globals, no locals.

Not run by the reviewer: the tier (passed on this head, recorded) and Lean.

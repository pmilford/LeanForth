# Forth review: small fixes (verify-alias.fs retired, tag bits, narrowed faults) (2026-11-18)

Branch `small-fixes-1118`, range `1ed0b5b5..089d61fa`, re-checked as `089d61fa..0e426064`. Reviewer: forth-reviewer
(Opus), independent of the implementer; probes and its own planted faults on Gforth 1.0.0, no suite re-run.

**Verdict: approve** after the re-check (0 high, 0 medium, 3 low, all closed; 2 informational). No change to a trust
boundary. `src/core/terms.fs` is under the [kernel] gate in form and needs the owner's approval.

## Findings and their fixes

- **L1, closed.** `src/program/verify-semantics.fs` `pv-perform`: removing the reserved arm left a `case` default that
  would write a reserved entry as a primitive. Unreachable (the only caller refuses first), but the arm is back, a
  `reserved-design` test reaches it and fault `pv-perform-reserved-written` is caught.
- **L2, closed.** `tests/program/verify.fs`: the rethrow test could not tell whether the design's handler ran (the
  reviewer's fault dropping `pv-design-handles` from `pv-caught` survived). A `handled-design` test now expects the
  handler's own reason; fault `pv-design-handler-skipped` is caught.
- **L3, closed.** `src/core/terms.fs` `lf-tin-leaf-tags+` wrote its bit with a raw `1 swap lshift` while its reader
  used the clamped `lf-tag-bit`. Now `lf-tag-place ( tag -- i )` clamps to 0-31, `lf-tag-bit` is built on it, and
  `lf-tin-leaf-tags+` and `lf-term-unshare` both call `lf-tag-set+ ( tag a-addr -- )` on `bit-on` of `lib/bits.fs`.
  For tags 0-31 the results equal the old code's on 32-bit and 64-bit hosts; a negative tag goes to bit 0, a tag
  above 31 to bit 31. Four reviewer probes caught (the unclamped `lf-tag-set+` by a crash, not an assertion).
- **I1.** `schemas/check-report-0.5.schema.json` repeats the three rules whose faults moved to 0.4, and no planted
  fault covers 0.5 (older than this branch). Plan 9.4.8n.
- **I2.** Three stray copies left outside the repository in `/tmp` by the implementer.

## Checks made

- Retiring `verify-alias.fs`: removing reason 27 renumbers nothing (messages are found by code); nothing in `src`,
  the tests or the user documents refers to the file or its words; every reachable refusal still fails closed.
- Narrowed faults: seven re-planted by hand, each caught by an assertion on its own property; the three schema
  faults moved to schema 0.4 fail on the right cases of `test_schema_refuses`.
- Baselines: coverage and style changed only by the retired file's entries; the two duplicates groups dropped were
  stale; `check-duplicates.py` passes (251 groups, none new).
- Style: 623 words in the seven changed files, 81% of one or two lines, none over ten, no locals.

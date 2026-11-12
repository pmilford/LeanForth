# Forth and correctness review of no-label and review-bugs (2026-11-12)

Reviewer: forth-reviewer (Opus). Saved by the coordinator, condensed.

## no-label, `b4f354a..7681f56` — NOT BLOCKING (0 high, 0 medium, 2 low, 2 info)
Only the label changed: label words (cj-label, rr-label, lf-check-label, lf-ol-label) and texts removed; versions
check report 0.4 (final) / 0.5 (snapshot), run record 0.3; run-replay's member table without "label". No word deciding
a verdict, outcome, axiom set, NOT PROVED, diagnostic or fuel changed. Replay fail-closed: 0.2 records refused as
unknown-schema; a 0.3 record with a label gets unknown-field; schemas are the old ones minus the label,
additionalProperties false. L1 PROGRAM_RECEIPTS.md:100,116 and program-receipt schemas 0.1/0.2 still prescribe the
label for accepted-by-leanforth (nothing writes it yet): mark withdrawn, receipt 0.3 with the program track. L2 stale
version numbers in comments (check-json.fs:85,145,215; leanforth.fs:262). I1 no fault for cj-head, the summary line,
the snapshot line, `version`. I2 one shared `lf-check-accepted` word for check-declaration.fs:424 and
proof-outline.fs:523.

## review-bugs, `3c306b6..5f82748` — NOT BLOCKING (0 high, 0 medium, 4 low, 3 info)
No verdict, diagnostic or fuel change on valid input; each change makes a failure path stricter or keeps `full` as
full (stacks traced for every changed word: lf-sched-add, lf-sch-and, the snapshot-layer outcome words, imp-fill,
canon-key through put-lists, sl-sane?/answer-ok? against every value the writer produces, lf-cref-unreached). L1 test
gaps: lf-sch-worker-room without its ctxs check; canon-name? `1+ u<`; env-layers.fs:132 ignoring ly-name's outcome
and snapshot-layer.fs:229 accepting a nonzero payload (need FRI's class-2 forged-layer tests). L2 lf-sch-and and
ly-and are one word: `outcome-and` in lib/outcome.fs. L3 snap-warn-limit worked out by hand: derive it and assert every
lf-warn-* bit is below it. L4 put-look and put-pair take four items (a cursor record). I1 stdout/stderr fallbacks open
/dev files at load (documented). I2 fixed /tmp paths in env-import.fs:105-106 clash between worktrees. I3 FRK F2, FRI
F2, FRI F4 and the batches remain plan tasks; the stricter [kernel]/[import]/[format] checks belong in the owner's
summary.

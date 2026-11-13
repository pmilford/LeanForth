# Forth review of branch refactor-fri (62ae0e8..13e9a5c), 2026-11-12 — not blocking

Reviewer: forth-reviewer (Opus), read-only, in worktree agent-aa597329702ab5c47. Scope: batches B1-B8 of the FRI backlog review, 14 commits, 14 source files. Rules: .claude/work/briefs/REFACTOR.md. Findings: 0 high, 0 medium, 4 low, 4 info.

## Behaviour (traced, success and failure paths)
- feed.fs (checking path), all equivalent:
  - /feed-copy keeps the old layout (e at 0, the handle at cell+, 2@).
  - feed-copy+ is split into feed-copy-room and feed-copy-next with the same growth arguments.
  - feed-copy@ through feed-copy-of gives the same bounds and the same e test.
  - feed-args through feed-arg passes tuple-item ( i t cons ) and feed-pair! ( l k feed ) the same arguments, and its failure leaves ( n full ).
  - The feed-to-copy? CASE matches the old IF chain: let-tag? is exactly tag-let and tag-let-nondep (compact-exprs.fs:86), and the default arm consumes the tag and pushes 0 for ENDCASE.
  - feed-leaf0! replaces `0 3 roll`. In nat, str, projection and let, the field order (first, second, 0, e) is unchanged.
- snapshot-layer.fs ([import]), all equivalent:
  - /ly-fam per section. fam-first replaces ly-first; fam-xlate, fam-own and fam-fresh? have the same tests and order. fam-begin and fam-top are now per family; each family is begun before it is entered, so the result is the same.
  - fam-rec uses tier-unit: 16, 16, 8, 16 and /staged for names, levels, texts, expressions and declarations, the old strides.
  - fam-read, fam-alloc and ly-zeros allocate in the same order with the same failure stacks.
  - ly-starts (fam-starts with flag>outcome) and ly-list (an item address replacing idx; items-at has the old bounds).
  - fam-tuple, fam-fill and fam-adds: as before, a failed fill leaves the tuple begun and gives -1 and the outcome.
  - ly-rules, ly-more (the tables now carry their count), ly-data (the old default kept t' = t), ly-field (new argument order), ly-xlate-decl.
  - The expression path: fam-head, fam-plain, fam-let, fam-body, fam-expr-step, and span computed before the keep (a pure read).
  - ly-blame ≡ ly-note: on failure it records where and why; ok passes.
  - No leftover uses of removed words in src/, tests/ or docs/, and no redefinition warnings when src/main.fs loads.
- core:
  - /lf-sought has the old 3-cell key layout. lf-sought= is the same predicate as lf-term-key= and lf-tfields=, and lf-fields-hash is the same mix in all three tables. lf-sought-hash! stores, then hashes the stored fields, giving the same h.
  - lf-tin-given asks lf-term-findable? only when the node is reusable, as before.
  - /lf-ckey and /lf-unit have the old offsets. Inlining lf-walk-unless keeps its meaning.
  - /lf-memo has the old offsets. lf-copier-pair evaluates the second child first, as before.
  - statement-match: lf-stmt-letter# is SEARCH within letters for one-character tokens only, numbered from the end. The CASE arms give the old P/L/A/S/C, z/s/m/i and build mappings, and their defaults drop the same cells.
- stage-records (tuple-item, new order), stage.fs (exprs-walk with +LOOP: the same termination for increasing expr-next, as before), snapshot-tier lines-ok? (line-pair), manifest: all equivalent.
- Init evidence (implementer's runs, .claude/work/FRIR/runs): I compared init-base.json with init-final2.json. 59,349 declarations, with names, verdicts and fuel identical; only "measured" differs. Total fuel 654,719,715 by the implementer's note.
- CPU (from those runs): base 1047, 1242 and 1187 s user; final 1033 and 948 s. Peak memory 827 → 805 MB.
- The implementer's logs end with: make check JOBS=2 passing; make test on 0.7.3 OK; the coverage ratchet holding.

## Findings
- L1 (faults): two of the six listed gaps can be closed.
  - fri-b4-args-room-ignored: refuse the pair buffer's growth with tests/support/heap-watch.fs, as tests/core/env-import.fs refuses a layered import's allocations.
  - fri-b7-line-none-first: needs a forged one-declaration tier in tests/core/snapshot-tier.fs.
  - The other four are acceptable as gaps: two the reader's earlier checks make unreachable; one is a log memo case no test builds; and for fri-b7-exprs-walk-let-as-one, the walkers leave a body record as they found it, so it is close to equivalent — better marked `equivalent` with that reason.
- L2 (tests of changed arms):
  - Dropping the tag-let-nondep arm of feed-to-copy? (feed.fs) survives check-declaration-ndjson.fs, check-block.fs, the CLI AsCopied and Imports classes and cross_snapshot.py. Add a non-dependent let whose child is copied, and plant the fault.
  - Dropping kind-opaque from ly-names-kind? (snapshot-layer.fs) survives env-import.fs and the CLI Layers and Imports classes. No layer fixture holds an opaque declaration; add one.
- L3 (one shared vocabulary): env-schedule.fs:179 lf-sch-and is outcome-and. Replace it, and the FRK batch-A *-then copies, with the lib/outcome.fs words.
- L4 (style, ADR 0010): new generic names enter the global word list: fam-*, items-at, line-pair, unit-stamp/unit-kept, sought-*, ckey-*, memo-index/memo-ref, copy-e/copy-handle. No clash today. Prefix them per module (ly-fam-*, lf-unit-*) or keep the helpers in a private word list.
- I1: statement-match.fs is on the axiom allowlist's path. The refactor is equivalent by trace, and its 6 stmt-* faults are caught; still, mention it in the owner's summary.
- I2: two of my faults have the same effect as the original code, given their callers. feed-copy-of's e test is redundant because feed-copy@ is asked only for dirty, so copied, e. fam-xlate's map-zero test is caught later by expr-make. Plant them as `equivalent` if wanted.
- I3: snapshot-layer.fs's comment before fam-add ("then a tuple filled so, or a failure, ended") reads as if a failure ends the tuple. Say that a failed fill leaves it begun and the caller frees the stage.
- I4: outcome-steps recurses once per step, which is fine for short lists. lf-stmt-letter#'s backwards letter string is commented, but a reader must know SEARCH's result; acceptable.

## Library rules (lib/outcome.fs)
- Still "no state, no dependencies".
- ok-then3?, outcome-and and outcome-steps have stack comments and behaviour notes; outcome-steps has an example.
- tests/lib/lib.fs tests all three outside the checker, including return-stack checks (rs-checked); they pass on Gforth 1.0 and 0.7.3.
- FORTH_LIBRARY.md is updated, and sections.fs's sec-run is gone in favour of outcome-steps.

## Metrics (forth-metrics, 62ae0e8 → 13e9a5c; only changes shown)
Columns: words, 1-2 lines, 3-5, 6-10, deep shuffles, return-stack ops.
- constant-term-boundary: 128→127, 90→89.
- derivation-log: 209→210, 3-5 lines 43→44, shuffles 33→32.
- levels: 56→54, shuffles 10→5, return-stack 13→11.
- statement-match: 94→96, 6-10 lines 2→0.
- terms: 194→196, 6-10 lines 4→3, shuffles 34→28, return-stack 60→53.
- feed: 177→183, 6-10 lines 4→3, shuffles 46→42, return-stack 170→166.
- snapshot-layer: 91→117, 6-10 lines 8→3, shuffles 83→43, return-stack 146→64.
- snapshot-tier: 6-10 lines 3→2, shuffles 36→35, return-stack 137→133.
- stage-records: shuffles 39→37.
- outcome: 13→16, one 3-5 line word (outcome-steps).
- sections: 101→100.
- Total (14 files): 1641→1677 words; 6-10 lines 40→30; shuffles 403→344; return-stack ops 1039→940; globals 56, words over 10 lines 0 and long lines 9, all unchanged.
- tests/forth-quality-baseline.json changes only for the 13 changed files with a metric change, and only downward (word counts aside).

## Runs
- Gforth 1.0.0, all exit 0: tests/lib/lib.fs, core/env-import.fs, snapshot-tier.fs, terms.fs, levels.fs, constant-references.fs, env-signature.fs, check-block.fs, derivation-log.fs.
- Gforth 0.7.3, all exit 0: lib, terms, snapshot-tier, env-import, check-block, env-signature.
- `mutants --check`: 1261 entries, 0 stale.
- The 44 new faults: 38 caught, 6 survived as listed gaps.
- My 11 faults: 2 caught (line-pair shifted; the fresh top not raised, caught by the CLI test_record_twice). The other 9 survived the tests I ran: 4 equivalent or defensive (I2), 2 untested arms (L2), and 3 that are near-equivalent or covered by later checks.
- Not run: make check or test, Init. AI review is not the owner's review.

## Re-check of 13e9a5c..c92bcfe (2026-11-12): not blocking

All items fixed (L1 both gaps closed, let-as-one equivalent; L2 marks-nondep and opaque-in-layer tests, faults caught;
L3; L4 prefixes; I2; I3). Kernel edit (src/kernel/env-schedule.fs): behaviour-identical: lf-sch-and's body was
`over ok? if nip else drop then`, exactly outcome-and's body and stack effect ( outcome1 outcome2 -- outcome ); every
call site (slabs-init, turn-room, also, worker-room, sched-add) computes its arguments in the same order; faults
frk-sched-add-pushes-first and frk-sched-outcomes-ored caught. ly-none3 = the old exits. Faults changed in the range:
33 (28 caught, 2 equivalent, 2 gaps as listed); `mutants --check` 1265 entries, 0 stale. New, low, predates the range:
s6c-memo-no-identity (constant-term-boundary.fs lf-audit-same-node?) survives without being listed, also on main;
listed as a gap at the merge (a test that rolls back a term and remakes it at the same index within one audit epoch
is owed).

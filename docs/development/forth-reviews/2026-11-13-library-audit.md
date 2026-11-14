# Library-reuse audit of src/front and the 2026-11-12 library candidates, 2026-11-13

Reviewer: forth-reviewer (Opus), read-only audit, after the owner's decision "Library reuse" of 2026-11-13
([OWNER_DECISIONS.md](../../project/OWNER_DECISIONS.md), plan 9.4.8). Range: main `c1f0cd19`; branches `s1-meta-b`
`f7cb91eb` (lib-decode.fs, meta-env.fs), `s1-synth` `8ff80187` (discr-keys.fs, instances.fs), `s2-unfold` `d755b2ff`
(no new source yet). Findings: 3 high, 5 medium, 4 low (the 11 actions of (a) plus the library-profile gap). Kernel
copies (K) need the owner's [kernel] gate. The trigger is already fixed on its branch: `8ff80187` sorts getInstances
with `lib/sort.fs` (instances.fs:368-376), its first caller once `s1-synth` merges.

## (a) Library actions, most valuable first

| # | Library: interface | Copies it replaces (file:line) | Slice | Size |
|---|---|---|---|---|
| 1 H | slab.fs: `slab-push ( x slab -- outcome )`, `slab-pop ( slab -- x )`, `slab-2push ( x1 x2 slab -- outcome )`, `slab-2pop ( slab -- x1 x2 )`, `slab-last ( slab -- addr )` | about 27 copies. front: meta-spine.fs:44,73 (`lf-meta-push`/`pop`, a general word inside a Lean module), level-simp.fs:40-43, level-defeq.fs:73-76, term-eqv.fs:47-50, level-normalize.fs:124-126, instantiate.fs:139-144,211, beta-inst.fs:97-102, mvars.fs:525,532,706, goal-print.fs:171, whnf.fs:146-153, defeq.fs:167,196, tactic-run.fs:285,325. core/input.fs:414. Branches: meta-env.fs:129, lib-decode.fs:106-108, instances.fs:301-306, discr-keys.fs:89-91. K env-schedule.fs:199-201. Review fe1c-2 S2 asked for `slab-push` on 2026-11-12 | every slice; S1 synth, S2 kabstract | S |
| 2 H | new lib/memo.fs, a keyed table on htab+slab: `memo-init ( kcells vcells memo -- outcome )`, `memo@ ( k1 k2 memo -- v true \| false )`, `memo! ( v k1 k2 memo -- outcome )`, `memo-clear`, `memo-free`; and front/dag-walk.fs moved to lib/, on slab.fs, with this memo as an option and a memo kept across runs (`dw-open`, `dw-walk`, `dw-close`) | instantiate.fs:113-200 and beta-inst.fs:54-175: 37 words identical once the `in-`/`ib-` prefixes are removed (one image walk with a leaf xt would serve both). import/ndjson.fs:214-277 (imap). lib-decode.fs:166-177 reaches into dag-walk's private `dw-tables`/`dw-go` to keep its memo. dag-walk.fs:57-76 has its own doubling stack. K replace-memo.fs, caches.fs | S2 s2-unfold (edits instantiate and beta-inst), s2-tactics kabstract.fs, meta-check.fs; S1 synth tables; S4 omega | M |
| 3 H | adopt sort.fs (exists) | front level-normalize.fs:133-137 (its header admits n² cost; listed in FORTH_LIBRARY "Sorting" since 11-12, never converted). import/ndjson-emit.fs:221-225. K env-snapshot.fs:224-230,344,407-411; level-normalize.fs:217-264; level-substitute.fs:66-85 (heapsort, would need a buffer above 32 records) | S1 (done on branch), S4 | S |
| 4 M | outcome.fs: `ok-each ( i*x n xt -- i*x outcome )` with xt `( i*x k -- i*x outcome )`, `ok-fold`, `outcome-first! ( outcome a-addr -- )` | `aux-then` (constructions.fs:212) and `and-then` (import/stage.fs:116) are `ok-with`'s body word for word. `aux-each`/`aux-fold` at constructions.fs:207-218. About 130 hand-written "`?do` … `ok? 0= if` … `unloop exit`" loops: front 18, kernel 66, import 20, core 11, branches 13. First-failure cells: beta-inst.fs:54, instantiate.fs:73, dag-walk.fs:38, run-record.fs:446, json-write.fs:146, export.fs:108, ndjson-emit.fs:139; K level-normalize.fs:94, inductive-recursor.fs:108 | all | S |
| 5 M | core/terms.fs (shared word, not lib): `lf-term-app?`, `-lam?`, `-pi?`, `-binary?`, `-binder?`, `-const?`; core `lf-name-dotted? ( name c-addr u -- flag )` | About 30 one-line tag tests: instantiate.fs:74,209-210, beta-inst.fs:56-60, mvars.fs:312,648,718, tactic-basic.fs:131,188,296, goal-print.fs:136, level-params.fs:109, assign-check.fs:112, term-eqv.fs:135, whnf.fs:356,385, discr-keys.fs:211, instances.fs:106 (K 6 more). term-eqv.fs:111-123 re-implements core/statement-match.fs:101-115 for two parts only. `hb-spine` (instantiate.fs:215) and `ib-spine-fill` (beta-inst.fs:132) copy `lf-meta-spine`, though both files already require meta-spine.fs | S1, S2 | S |
| 6 M | new lib/blocks.fs: `block-zeroed ( u a-addr -- outcome )`, `block-resize ( u a-addr -- outcome )`, `block-free ( a-addr -- )`; bytes.fs's `heap-claim`/`heap-release` moved here (dag-walk loads the line reader only for `heap-release`) | dag-walk.fs:72-76, core/reach.fs:53-54, mvars.fs:786, level-map.fs:56, lib-decode.fs:317,411-414. Hand-grown arrays that should be slabs: cases-several.fs:51-56, constructions.fs:202-205, import/feed.fs:131. K env-import.fs:555, env-layers.fs:109 | S2, S4 | S |
| 7 M | new lib/decimal.fs: `u>decimal ( u -- c-addr u )`, `n>decimal`, `ud>decimal`, `digits>u` (moved from json.fs), `in-decimal ( i*x xt -- j*x )` restoring BASE after a THROW too | ctor-idx.fs:59, discr-keys.fs:135, print-job.fs:122, export.fs:236, errors.fs:391, check-run.fs:738, name-text.fs:72, manifest.fs:278, ndjson-emit.fs:481, stage.fs:242, verify-report.fs:214, ir-reader.fs:378,433, ir-run.fs:387,775. K check-block.fs:481, inductive-nested.fs:262, environment.fs:744,786 | S1 keys, S3/S4 | S |
| 8 M | adopt frame.fs (exists) in front defeq/whnf, or record why not (FRONT_END.md:593,602 and FE1G_TACTICS.md:447 named it) | defeq.fs:146-216 hand-writes its own continuation machine (registers `df-t`…`df-y`, saved activations, fuel); whnf.fs:140-155 its own frames. tactic-run.fs:123 needs only item 1 | S2 (s2-unfold edits both) | M-L |
| 9 L | new lib/bits.fs: `cell-bits`, `log2-ceiling` (made public from htab.fs:87,158), `bits>cells`, `bit@ ( i addr -- flag )`, `bit-on ( i addr -- )`, `lower-bound ( key lo hi xt -- i )` | terms.fs:568, check-run.fs:409, run-record.fs:426, feed.fs:182-208 (`1 cells 8 *` assumes 8-bit address units), core/reach.fs (one cell per flag). Binary search: feed.fs:221-230, mvars.fs:504-511. K environment.fs:1306 (htab's `cell-bits` word for word), mixed-level-substitute.fs:269-273 | S4 | S |
| 10 L | bounds.fs: `index? ( i n -- flag )` (signed 0≤i<n), `cells-index ( x addr n -- i true \| false )` | 18 `0 swap within` in 14 files, e.g. dag-walk.fs:49 (`within` accepts any i≥0 when n<0). Cell searches: lctx-views.fs:180, declarations.fs:107, level-scope.fs:59, print-forth.fs:325, proof-outline.fs:152; K mixed-signature-probe.fs:138 | all | S |
| 11 L | new lib/pqueue.fs: `pq-push ( x pq -- outcome )`, `pq-pop ( pq -- x )`, with an order xt | K env-schedule.fs:203-231 only (level-substitute's heapsort goes to sort.fs) | none yet | S |

## (b) Duplications not worth a library now

- One user each, no second one planned: the CLI option table (leanforth.fs:1455-), the progress timer (check-run.fs:295-410, Gforth's `utime`), TeX escaping (present/latex-text.fs, tied to the printer's sink). Extract when a second user appears.
- author/source.fs is already a shared module (author/ and program/). run-replay's JSON comparison and derivation-log's fixed stacks (inside the log's pools) have one user each.
- instances.fs's node trie is Lean's DiscrTree, not a general structure. The per-module `*-refuse` words that only forward to `dw-refuse` are fine.
- Not sure: discr-keys.fs:85-94 todo lists (cons cells sharing tails) might fit runs.fs; check in S1; no new library.

## (c) Why reuse failed, and a fix for each

1. Review proposals stayed notes: fe1c-2 S2 (11-12) asked for `slab-push` in lib/slab.fs; the recheck accepted "S2 left as a plan note"; no plan row was made, and the copies grew from 4 to about 27. Fix: a proposed library gets a PLAN_DRAFT row in a named slice before the review is logged, and check-forth-quality.py refuses the log entry otherwise.
2. Libraries were built for a gated caller and then parked: sort.fs targeted the kernel's sorts behind the gate; its doc listed two callers outside the gate nobody converted; bigint.fs has no caller either. Fix: a library merges only with one converted copy, and `make test` fails for a lib/ file nothing outside lib/ requires, unless an allowlist entry points to a plan row.
3. Parallel branches were never reconciled at merge: `ok-with` committed 11-12 21:29 on one branch, `aux-then` (the same body) at 21:57 on another; the front `Level.normalize` port landed 22:05, sort.fs 11-13 00:48. Fix: a duplicate detector at merge time (word bodies compared with module prefixes stripped), held as a ratchet like the style baseline.
4. Copy-and-rename hides duplicates from grep: beta-inst.fs was started from instantiate.fs (37 identical words); tag tests are redefined file by file. Fix: the same detector, and every brief states what a new module shares with existing ones.
5. Designs named libraries the code then skipped, and general helpers landed in convenient files: the designs named frame.fs but defeq/whnf/dag-walk built their own; `heap-release` sits in the line reader, `cell-bits`/`log2-ceiling` are private in htab.fs, `lf-meta-push` is in a Lean module. Fix: the review compares the design's Reuse table with the actual `require` lines, and a general helper goes to lib/ when it is first written.

## (d) Owner summary (reviewer)

- The same small building blocks were written over and over: about 27 copies of push/pop on a growing array, two nearly identical term walkers, 7 hand-written sorts, about 130 copies of one loop.
- Reviews caught part of this on 2026-11-12, but their suggestions stayed notes while parallel branches kept copying.
- Recommended: actions 1-5 now (small, mostly outside the kernel gate), before S1/S2 add more copies; the kernel copies together in one [kernel] review.
- None of the 30 libraries documents all five parts of the profile the owner asked for (table below); even sort.fs lacks a small-size timing and real-run callers.

## Library profiles (y yes / p partial / n no / – not applicable)

| File | Algorithm and why | Generic | Cost as size grows | Speed small+large | Callers on a real run | Where documented |
|---|---|---|---|---|---|---|
| bigint | y | – | p | n | n (no caller) | FORTH_LIBRARY §Signed big integers |
| bignum | y | – | y | y | n | §Big natural numbers |
| bounds | – | y | – | n | n | header, table row |
| bytes | p | p | p | p | p | row; NDJSON_READER.md |
| cons | y | y | y | y | y | §Compact store, §Measured |
| context | y | p | y | p | n | §Design: per-task contexts |
| frame | y | y | y | p | n | row, header |
| hash32 | p | y | – | n | n | row |
| htab | y | y | p | p | p | §Compact store |
| json-write | p | – | y | n | n | row, §JSON |
| json | p | – | p | p | p | row; NDJSON_READER.md |
| lib (loader) | – | – | – | – | – | src/README.md |
| module | – | – | – | – | – | ADR 0010, row |
| node | – | y | – | n | n | row |
| outcome | – | y | – | – | – | row |
| pools | y | y | p | p | p | §Compact store |
| portability | – | – | – | – | – | row |
| runs | y | y | p | n | n | row, header |
| sections | y | y | p | n | n | §Sectioned binary files |
| sha256 | y | – | y | p (large only) | y | §SHA-256; NDJSON_READER.md |
| slab | p | y | p | n | n | row, §Compact store |
| sort | y | y | y | p (100,000 only) | n (no caller on main) | §Sorting |
| store-columns | p | y | p | n | n | header, mentioned in rows |
| store | p | y | p | n | n | row |
| task | y | p | y | y | p | row, §Measured speed-up |
| text-rule | p | y | n | n | n | row |
| text-run | p | y | n | n | n | header only: no FORTH_LIBRARY row |
| u32 | y | – | – | n | n | row |
| walk | p | y | p | n | n | row |
| xt-table | – | y | – | n | n | row |

## What was run

git log, show and diff on main and the three branches; grep, sed and awk over src/ and the branch copies in
`.claude/work/lib-audit/`; a mechanical comparison of word bodies (definitions with module prefixes normalized,
compared with `comm`); `python3 scripts/forth-metrics.py --words 10` on src/front/*.fs and the four branch files (3,185
words, 72% one or two lines, none over five lines; 190 deep shuffles, 589 return-stack operations). No Gforth, Lean,
make or test run. The profile marks come from a quick reading of headers and FORTH_LIBRARY.md (approximate), the loop
counts of item 4 from a regex (approximate). An AI review does not replace the owner's review.

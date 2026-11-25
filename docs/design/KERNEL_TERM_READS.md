# Leaner reads of term nodes

Status (2026-11-25): **designed, not reviewed; no code.** The next kernel speed step after the
environment stamp ([KERNEL_VALIDITY_CHECKS.md](KERNEL_VALIDITY_CHECKS.md)), candidate 3 of the speed
measurement ([KERNEL_SPEED.md](../development/KERNEL_SPEED.md), sections 9 and 10: "node field reads
inlined"). Every number is **measured** or marked **estimate**. Shares are of the profile of Init at one
worker on main `39800cde` (2026-11-25 14:17, `.claude/work/init-profile-2026-11-25-after-stamp/` of the
main checkout, 47,027 samples, `scripts/profile-summary.py` and a caller count over the same file); a
point is 1% of the 779.5 s of Init's check phase at one worker on main `0f3b3edd` (KERNEL_SPEED.md,
section 10, "Measured again on main"; Lean 38.4 s, about 20.3 times). Source references are `file:line`
on `39800cde`.

## 0. One page for the owner

**What is slow.** Reading one field of a term node (its tag, a child, its data word) takes a chain of
four to eleven colon definitions. For a node the checker made itself, `lf-term-tag@` calls
`lf-term-input?` (is the number below the input tier's base?), which calls `lf-term-base`, which calls
`lf-term-view` (the context's input-view record: `lf-context @ offset +`); then `lf-term-slot` calls
`lf-term-base` and `lf-term-view` again, `lf-terms`, `store-slot`, `store-records` and
`store-identities` (which branches on whether the store's block is on the heap) before the one `l@`
that reads the field: 11 calls, 9 memory loads, 2 branches where C++ does one load. These small
address words alone are 12 points of Init's time (measured exclusive: `lf-term-view` 3.63,
`lf-term-base` 2.97, `lf-term-input?` 1.42, `store-identities` 1.10, `lf-terms` 0.93, `store-slot` 0.91,
...); the whole read layer is 24.5 points exclusive (measured), about 190 s of 779.5 s. Despite its
name, `lf-term-view` is not a decoded node: it is the address of a context record, recomputed at every
read, twice for a store node.

**What changes.** Slice 1 makes each read one or two words: the base and the input records' address
fetched with one context fetch and one folded offset; the term store's record origin kept as one sealed
cell of the store header (written in the same words that place or move the block), so a slot is
`index * width + origin` without a branch. Every word keeps its name, stack effect and checks. Slice 2
stops probing a hash table on every validity check of an input leaf (2.2 points, measured) when the
importer has shown, once per view, that every leaf has its entry. Slice 3 reads each node once per visit
in the instantiation pass, which today re-reads a binary node's tag four times and checks it three times
per visit.

**Why it is safe.** No check is removed or moved in slice 1: the per-read range check of ADR 0016 C8
(`store-at?`), the input node test and the header checks at every pass's root stay exactly where they
are; only the address arithmetic between them is shorter. Nothing new is cached across calls except the
record origin, which lives in the store's header beside the block address it is derived from, is
written by the same words, and joins the header's seal, so a corrupted origin is refused at the root as
a corrupted block is today. No input reaches the changed code: LeanForth never runs the export as Forth,
and every check of data read from the export stays per read. Verdicts, diagnostics and fuel are
identical by construction; section 5 lists the evidence the branch must show.

**The gain.** Slice 1: **8-12 points, about 62-94 s (estimate)**. A micro-benchmark on `gforth-fast`
(measured, section 2) puts today's store-node read at 9.3 ns and the fused one at 2.2 ns. Slices 2 and 3
add 2.5-5 points. The group: **10.5-17 points, about 82-133 s**: Init from 779.5 s to about 650-700 s,
**17-18 times Lean** instead of 20.3 (estimate).

**The cost.** About 80-145 Forth lines changed in `src/lib/context.fs`, `src/lib/store.fs`,
`src/core/terms.fs` and three kernel pass files, 160-250 test lines and 12-15 planted faults; about
1.5-2.0 M tokens for the implementer, the Forth review, the fixes, one tier and one done check (estimate).

**Risks.** (a) The store header grows by one cell, read by every store in the program: a stale origin
after growth would read the old block; a test grows a store and reads old and new nodes, a planted fault
drops the update. (b) Slice 2 rests on a fact not yet verified (every input leaf has its entry once the
importer is done, also under a shared fed input); where it cannot be shown, the probe stays and the
slice shrinks to one probe per leaf read instead of two. (c) Slice 3 touches the instantiation pass's
walk, which candidates 2 and 7 also change; it keeps every visit and every unit of fuel.

**Recommendation.** One branch, three slices in this order, one review, one tier, one done check.
Behaviour-preserving refactoring of core and kernel code under the owner's decision of 2026-11-19 (Forth
review, the full tier with every pinned-Lean comparison, reported afterwards). No Forth macros in this
group (section 2, option b: 0.3 ns more per read for a loss of profiling and of ordinary words).

## 1. The path today

The four hottest reads (chains by `file:line`; calls are colon calls; `u32@` is the primitive `l@`
through `synonym`, `src/lib/u32.fs:99-101`; `lf-context` is a USER variable, `src/lib/context.fs:152`;
a context member's address word is `lf-context @ literal +`, `context.fs:232-233`).

| Read | Chain | Calls / loads / branches | Exclusive shares of the links (points, measured) |
| --- | --- | --- | --- |
| Tag of a store node | `lf-term-tag@` (`terms.fs:463`) → `lf-term-input?` (`:216`) → `lf-term-base` (`:212`) → `lf-term-view` (`:211`); `lf-term-slot` (`:219`) → `lf-term-base` → `lf-term-view`, `lf-terms` (`:167`), `store-slot` (`store.fs:86`) → `store-records` (`:84`) → `store-identities` (`:82-83`); `u32@` | 11 / 9 / 2 | tag@ 0.84, input? 1.42, base 2.97, view 3.63, slot 0.55, terms 0.93, store-slot 0.91, records 0.31, identities 1.10 (0.85 of them via records) |
| Child a/b of an app or binder body (store) | `lf-term-first@` / `-second@` (`:468-471`): the same chain plus a field offset | 11 / 9 / 2 | first@ 0.63, second@ 0.34; the rest shared with the row above |
| Tag of an input node | `lf-term-tag@` → `lf-term-input?` → base → view; `lf-tin-tag@` (`:356`) → `lf-tin-code` (`:285-286`) → `lf-tin-at` (`:284`) → `lf-term-view`; `quad-head u32@ head-tag`; `lf-tin-entry` (`:252`, the read-only code table by tier tag and parity) | 10 / 6 / 1 | tin-code 1.98, tin-at 1.58, tin-entry 0.27, head-tag 0.12, tin-tag@ 0.14 |
| Child of an input node | `lf-term-first@` → ... → `lf-tin-first@` (`:373-375`) → `lf-tin-code` (whole chain) → `lf-tin-plain?` → `lf-tin-at` again → `quad-a u32@` → `lf-tin-child`; a leaf: `lf-tin-other@` → `lf-tin-leaf@` → `lf-tin-leaf` (`:329-330`: `hash-fmix`, `htab-find`) → `lf-tleaf` (`slab-at`, `slab-unit`) | 13-20 / 8-14 / 2-4 | tin-first@ 0.28, quad-ab@ 0.36, tin-plain? 0.11, tin-leaf@ 0.81 inclusive |
| Checked read (`lf-term-valid?`, `:437-438`) | input? chain, then store: `lf-term-base -` (view again) `lf-terms store-at?` (`store.fs:170-171`: capacity, count, two compares); input: `lf-tin-valid?` (`:353-355`) → `lf-tin-code` chain → for a leaf `lf-tin-leaf`, a hash probe | 7 / 6 / 3 (store); 8-14 / 6-12 / 3-5 (input) | valid? 1.01, store-at? 0.68, tin-valid? 0.42; the leaf probe 2.17 inclusive |
| Identity (`lf-term-identity`, `:442-445`) | `lf-term-valid?` (above), `lf-term-input?` again, `lf-term-base -`, `lf-terms store-identity` (`store.fs:87`) → `store-identities` (branch) | 13 / 11 / 4 | identity 0.81, store-identity 0.13 |

**Who pays** (the read layer's 24.45 exclusive points by the outermost read word: `lf-term-tag@` 4.09,
`lf-term-first@` 3.85, `lf-term-identity` 3.63, `lf-term-valid?` 2.23, `lf-term-data@` 2.18,
`lf-term-second@` 1.85; by the first caller outside the layer: `whnf_core`'s spine `lf-mhead-app?` 1.42 and
`lf-mhead-spine` 1.10 (`src/kernel/mixed-head.fs:39-42`, a tag and a first child per step), the replace
memo's key `lf-rmemo-key!` 1.05 (an identity per lookup and insert, `replace-memo.fs:100-102`), the term
constructor's `lf-term-pair-valid?` 0.94 and `lf-term-data-of` 0.88, then the instantiation pass:
`lf-open-word` 0.85, `lf-open-readable?` 0.82, `lf-replace-update` 0.75, `lf-open-children?` 0.66,
`lf-open-bvar?` 0.58, `lf-rebuild-tag` 0.53, `lf-rebuild-binder?` 0.52 (all measured; appendix A).
A binary node's visit in the instantiation pass makes about 15 dispatched reads, three of them checked
(appendix B).

## 2. Options

Gains are points of 779.5 s, each net of the rows above it (**estimates** from the measured shares;
the benchmark's ratios applied to the layer's words; appendix A gives the basis).

| Option | What changes | Gain (points, s) | Forth lines | Risk |
| --- | --- | --- | --- | --- |
| (a) the same words, fewer indirections | `lf-term-base` and the input records' address as one word each (one context fetch, the member's and field's offsets folded into one literal); a sealed record-origin cell in the store header, so `store-slot` has no branch and `store-identities` is `origin - capacity cells`; `lf-term-tag@`, `-first@`, `-second@`, `-data-word`, `-valid?`, `-identity` fetch the base once; `lf-tin-code` reads its record once | 8-12, 62-94 s | 40-70 | low: same checks, same loads; one new header cell |
| (b) macros (immediate words that `postpone` the fused body into the caller) | the chain compiled into each caller, no call at all | 0.5-1.5 beyond (a) | 30-60 | medium: words that cannot be ticked or run interpreted, the profiler no longer sees the reads, code grows in 40 callers |
| (c) a node read once per visit | the visit reads tag, children, data word and identity once and passes them on; validity checked once per visit | 1-2.5 beyond (a), in the instantiation pass (slice 3) | 25-45 | medium: kernel walk code shared with candidates 2 and 7 |
| (c') leaf validity without a probe | a per-view flag "every leaf has its entry", set once by the importer's check; the probe kept where the flag is not set; one probe per leaf read | 1.5-2.5 (the probe's 2.17 under `lf-tin-valid?`, 0.81 under `lf-tin-leaf@`) | 15-30 | low to medium: rests on the importer's fact |
| (d) a leaner node layout | sketch only, below | 6-10 beyond the group | 300-600 | high: a new store design, ADR 0016's in-place tier |
| (e) native code | out of scope: a new dependency under the owner's gate, and the candidates above are Forth | – | – | – |

**The micro-benchmark** (measured 2026-11-25 on `gforth-fast` 1.0.0 under `ulimit -u 500`, 10 cores,
load average 0.20 before and 0.33 after, three runs, the medians; 99 M reads each, the empty loop's
0.4 ns subtracted; a scratch copy of the chain's shape, appendix C): a store node's tag today **9.3 ns**;
(a) with only the offsets folded and the origin cell 5.7 ns; (a) fused into one word with one context
fetch **2.2 ns**; (b) the same as a macro **1.9 ns**. A visit of ten field reads: today 98 ns, fused 37
ns, decoded once into a record and fetched ten times 5.5 ns (no frame write counted). The numbers decide
two things: (a) fused takes 76% of the cost, (b) adds only 0.3 ns a read, so the macros are not worth
their cost now; (c) is worth up to 30 ns a visit beyond (a), but only on the hot pass.

**(b) portability.** `postpone`, `literal`, `immediate` and `[ ... ] literal` are Forth-2012 core and run
on Gforth 0.7.3; the project already builds member address words that way (`context.fs:232-233`).
Gforth's `]] ... [[` is not Forth-2012 and is not used. `synonym` (Forth-2012, `portability.fs` on 0.7.3)
only aliases a word: it makes `u32@` the primitive on Gforth 1.0 but cannot inline a colon definition.
Option (a) needs only `[ ... ] literal` and the existing member pattern.

**(c) does `lf-term-view` already decode?** No. It is the address of the context's input-view record
(`terms.fs:197-211`: tier, base, records, leaf tables), not a node; it is hot because every read
recomputes it, twice for a store node. A decoded view per visit would be new code in the walk.

**(d) sketch.** One node format for both tiers: the store and the input tier read by the same address
computation, no parity, no code table, no leaf table on the read path (leaf fields stored in the node).
Either the input tier is copied into store records when the view is attached (about 16 bytes a node, **estimate**: for
Init's tier a few tens of MB, for Mathlib's several GB, against ADR 0016's reading of the tier in place),
or the store adopts the tier's record format. It would remove the input dispatch and most of the
remaining 4-5 points of input decoding left after (a) and (c'), plus the identity table's indirection:
6-10 points (estimate). A separate design after this group's measurement.

## 3. Fail closed

| Check on the read path | Where | Protects against | Kind | This group |
| --- | --- | --- | --- | --- |
| index below the count (`store-at?`, unsigned; a count beyond the capacity refuses every index) | `terms.fs:438`, `store.fs:170-171` | a number the store does not hold; a corrupted count | LeanForth's own bugs (store numbers are made by the checker), kept per read by ADR 0016 C8 | stays per read, unchanged |
| the input node is a term of the view (`lf-tin-valid?`: code not 0) | `terms.fs:353-355` | an input number naming no term: an even number without a carried node, a tier tag without a code | data from the export | stays per read, unchanged |
| an input leaf has its entry (probe) | `terms.fs:355`, `:329-330` | a leaf the importer did not enter | data from the export through the importer | slice 2: replaced by a once-per-view check only where that check passed; else stays |
| input or store (`lf-term-input?`) | `terms.fs:216` | none: a dispatch | – | stays (one compare); (d) would remove it |
| header: shape, seal, generation, count | `lf-term-count-valid?`, `lf-term-root?` (`terms.fs:436-440`) at every pass's root, `store-count-valid?` (`store.fs:154-158`) | a corrupted or poisoned header | LeanForth's own bugs; tests corrupt it on purpose | stays at the root; the new origin cell joins `store-check` (`store.fs:96-98`), so it is checked there too |
| the unchecked field reads (`lf-term-tag@`, `-first@`, `-second@`) | `terms.fs:460-471` | none today (they trust an earlier checked read) | – | unchanged: still unchecked, still after a checked read |

**Nothing moves to "once per pass" in slices 1 and 3.** They cache nothing across calls: the base and
records address are still read from the context at every read (one fetch instead of three), and the
origin is a header field written with the block (`store-place`, `store-install`, `store.fs:135-136`,
`:261-262`), so it can never be stale; a store's block moves inside a pass when it grows (`store.fs:24-34`),
which rules out caching an address in the walk's frame. The environment stamp's invariant (the input
does not change inside a check) is therefore not needed; slice 2's per-view flag needs only that a view's
leaf table is complete when the flag is set and grows only by entries (to be verified in the architect
step, including a worker borrowing a fed view, `terms.fs:95`, `src/import/feed.fs`).

**Tests and faults that pin the checks** (grep of `tests/mutants/faults.toml` and `faults.d/`):
`s2-node-read-unchecked` (`faults.toml:8076`), the root faults of the same block and
`s2-level-root-range-only` (`:8100`, the term roots' texts at `:8087` and `:8095`), the ten faults naming `lf-term-valid?` in callers (`:8128`,
`:10816`, `:11222`, `:12750`, ...), `fri-b2-let-lam-mode` (`:11959`, the input code's modes),
`pub-pool-records-lost` (`:465`, `store-records` through the pool areas), the marks' input dispatch
(`:8893`, `:8909`, `:8917`, `:8957`), `faults.d/terms.toml:11` and `faults.d/reuse-d.toml:35`. A fault
whose `old` text lies in a rewritten body is updated in the slice. New faults: the origin not updated at
growth; the origin left out of the seal; `store-identities` off by the capacity; the fused read using the
records address of another field; `lf-term-valid?` without the input test; slice 2's flag set without
the importer's check, and kept after a detach; slice 3's single read taken before the visit's check.

## 4. Re-entrancy

No module-level state is added. The view record and the term store's header are context members
(`terms.fs:167`, `:211`), so each worker of a parallel run has its own base, records address and origin;
the input code table (`terms.fs:250-251`) is written only while loading and sealed (`:256-257`). Slice 2's
flag is a field of the view record; a borrowed view (`lf-tview-borrowed`, `:206`) takes the lender's
flag only with its tables. Slice 3 carries what it read on the pass's own frame stack (`lib/frame.fs`).

## 5. Recommendation: one group, three slices, one branch

Ordered by gain over risk. Each slice starts with the architect step (`AGENTS.md`, "Library first"),
writes its library words and their tests first, and measures with
`time bin/leanforth check --jobs 1 --no-manifest --resources --json .claude/work/IM/init.ndjson` on
`gforth-fast` (before and after on the same day, load average noted) and `make profile-check`.

1. **Fused reads (option a).** `src/lib/context.fs`: a defining word for a cell at a fixed offset inside
   a context member (one literal, as `member-body`), with tests. `src/lib/store.fs`: the origin cell, set
   by `store-place` and `store-install`, sealed by `store-check`; `store-records`, `store-slot`,
   `store-identities` from it; its tests (grow, shrink, heap and inline stores, corrupted origin refused
   at the root). `src/core/terms.fs`: `lf-term-base` and `lf-tin-at` as one word each, `lf-term-slot` from
   the origin, the field reads fetching the base once, `lf-tin-code` reading its record once. Target in
   the profile: the address words (view, base, input?, terms, slot, store-slot, records, identities,
   12 points today) under 4. 40-70 lines.
2. **Input leaves (option c').** The importer's once-per-view check that every leaf record has its entry
   (`src/core/terms.fs`, `src/import/`), the flag in the view record, `lf-tin-valid?` and `lf-tin-fields@`
   with one probe at most. Target: `lf-tin-leaf` from 3.13 inclusive to under 1. 15-30 lines.
3. **One read per visit (option c, the instantiation pass).** `src/kernel/mixed-open.fs`,
   `mixed-rebuild.fs`, `replace-memo.fs`: the visit's checked read gives the tag, children and identity
   once; `lf-rmemo!` reuses the key of `lf-rmemo@`; `lf-replace-update` and `lf-rebuild-stuck?` use the
   values read. Same visits, same fuel. Target: the pass's payers (appendix A, about 7.5 points today)
   halved after slice 1. 25-45 lines.

**Total** 80-145 Forth lines, 160-250 test lines, 12-15 faults; **10.5-17 points, 82-133 s; Init about
650-700 s, 17-18 times Lean (estimate)**. Tokens for the group (estimate): implementer 1.0-1.3 M,
Forth review 0.2-0.3 M, fixes 0.1-0.2 M, tier and done check 0.2 M: **1.5-2.0 M**.

**Identical-results evidence the branch shows** (once, on its head, after rebasing): Init's JSON report
at `--jobs 1` identical to main's outside `measured`, `settings` and `run` (59,349 accepted, 1 not
proved, the same fuel and axiom sets); the decide slice (`tests/front/decide-slice.ndjson`) at 1 and 4
workers and the Mathlib slice (`reference-mathlib-slice`) the same; every pinned-Lean comparison
(`make check`, with `make test-unit` on `gforth-fast` and `make check-rest`); the parallel run's planted
wrong declaration rejected at `--jobs 1`, `2` and the default; every malformed export of the suites
giving byte-identical output; `make mutants` and `make test-compact-faults`; `make cover-changed`.

## 6. Reuse and work in flight

- **Used:** `member-body`'s pattern (`context.fs:232-234`), `store-at?`, `store-count-valid?`,
  `store-check`, `store-install`, `store-place` (`lib/store.fs`), `u32@`, `frame-save`/`frame-restore`
  (slice 3), `htab-find` (slice 2, the importer's check), the existing memo key words.
- **New:** a member-cell defining word (general, `lib/context.fs`); `store-origin` (general,
  `lib/store.fs`); `lf-term-at` (the fused slot, `terms.fs`); the view's leaf flag (`terms.fs`). No copy
  of an existing word: `store-records` and `store-identities` are rewritten over the origin, not doubled.
- **Copies replaced:** the two `lf-term-base` computations of a store read become one; the second
  `lf-tin-at` in `lf-tin-first@`/`-second@` goes.
- **Front end:** no file of `src/front` defines or changes these words; seven files call
  `lf-term-base` (`term-find.fs:55`, `telescope.fs:111`, `mvars.fs:841`, `fun-info.fs:204`,
  `defeq.fs:370`, `dag-walk.fs:115`, `assign-check.fs:148`) and 41 call the field reads, all through
  unchanged names and stack effects. The simp work in `src/front` touches no file of this group; the
  architect step re-checks open branches for `src/lib/store.fs`, `src/lib/context.fs`,
  `src/core/terms.fs` and the three pass files (`git log main..` of each) before slice 1 starts.
- **Other speed candidates:** candidates 2 (universe substitution) and 7 (replace memo) change the same
  pass as slice 3; whichever lands second rebases. Candidate 4 (hashing) is untouched.

## 7. Questions for the owner

1. **Ordinary work?** Recommendation: yes, behaviour-preserving refactoring (Forth review, full tier,
   every pinned-Lean comparison, reported afterwards), because no check moves, no verdict, diagnostic
   or fuel changes and no input reaches the changed arithmetic; slice 2 stops and asks only if the
   leaves' fact cannot be shown and its flag would decide a verdict.
2. **No Forth macros now.** Recommendation: plain fused colon words; macros gain 0.3 ns a read
   (measured) but hide the reads from the profiler and make 40 callers' code larger; revisit for at most
   two words after the measurement.
3. **The leaner store next?** Recommendation: design it after this group is measured, as its own
   milestone: it is the only way left to take the input dispatch and decoding (6-10 points), but it
   trades memory on Mathlib against ADR 0016's in-place reading.

## Appendix A. The read layer by word (profile 2026-11-25 14:17, measured)

Exclusive points of the 47,027 samples, for the words of `terms.fs`, `store.fs` and the input decoding
named in section 1 (24.45 in all; the leaf probe's hashing, 2.75 more, is counted under hashing).

| Group | Words (points) | Sum |
| --- | --- | ---: |
| address and dispatch | lf-term-view 3.63, lf-term-base 2.97, lf-term-input? 1.42, store-identities 1.10, lf-terms 0.93, store-slot 0.91, lf-term-slot 0.55, store-records 0.31, store-identity 0.13 | 11.95 |
| input decoding | lf-tin-code 1.98, lf-tin-at 1.58, lf-tin-valid? 0.42, quad-ab@ 0.36, lf-tin-first@ 0.28, lf-tin-entry 0.27, lf-tin-leaf 0.23, lf-tin-data 0.23, lf-tin-leaf? 0.18, lf-tleaf 0.15, and nine below 0.15 | about 6.7 |
| entry words' bodies (the node loads land here) | lf-term-valid? 1.01, lf-term-tag@ 0.84, lf-term-identity 0.81, store-at? 0.68, lf-term-first@ 0.63, lf-term-data-word 0.41, lf-term-second@ 0.34, lf-term-data@ 0.26, lf-term-fields@ 0.21, others | about 5.5 |

Slice 1's estimate: 65-75% of the first group (the benchmark's 76%, less for loads that miss the cache),
30-45% of the second, 15-30% of the third: 8-12 points. Slice 2: the probe's 2.17 under `lf-tin-valid?`
and part of the 0.81 under `lf-tin-leaf@`. Slice 3: the instantiation pass's payers (`lf-rmemo-key!` 1.05,
`lf-open-word` 0.85, `lf-open-readable?` 0.82, `lf-replace-update` 0.75, `lf-open-children?` 0.66,
`lf-open-bvar?` 0.58, `lf-rebuild-tag` 0.53, `lf-rebuild-binder?` 0.52, `lf-rmemo!` 0.48,
`lf-open-loose` 0.43, `lf-rebuild-next` 0.38: 7.05) shrink to about a third after slice 1, of which slice 3
takes half to two thirds: 1-2.5.

## Appendix B. Reads of one binary node's visit in the instantiation pass

From the code (`src/kernel/mixed-open.fs`, `mixed-rebuild.fs`, `replace-memo.fs`), a node that is not
skipped and not in the memo: `lf-open-readable?` (`mixed-open.fs:136-137`: `lf-term-mark-end`, a base
read, and `lf-term-valid?`), `lf-rebuild-tag` (tag), `lf-open-word` (`lf-term-data@`: valid? again and
the data word), `lf-rmemo-key!` (`lf-term-identity`: valid? a third time and the identity),
`lf-open-children?` (first, second), `lf-rebuild-stuck?` (tag, read even when the depth is below max-n),
`lf-rebuild-first` (first), `lf-rebuild-next` (second, and the tag through `lf-rebuild-descend`), then
`lf-replace-update` (first, second), `lf-rebuild-build` (tag) for a changed node, and `lf-rmemo!`
(the identity of the node again and of the result): about 15 dispatched reads, 3-4 of them checked.

## Appendix C. The benchmark

A scratch file (not committed; slice 1 adds its own under its tests if the reviewer asks) with a USER
cell pointing at a context block that holds a view record and a store header, and four versions of a
store node's tag read: today's eleven words in the same shape (`ctx @ offset +` for the view and the
store, `store-identities` with its `?dup` branch); the offsets folded and an origin cell; one word with
one context fetch, `[ offset ] literal + @`, `- 4 lshift`, the origin and `l@`; and that word compiled
into the caller by an immediate `postpone` word. Loops of 1 M x 99 reads; the visit loops make ten reads
of one node (four tags, three first, three second) or decode three fields once into a record and fetch
ten times. `gforth-fast` 1.0.0, three runs, milliseconds: empty 37-39; today 951-975; folded 602-617;
fused 252-259; macro 221-231; visit today 967-974, fused 362-364, decoded 54-55.

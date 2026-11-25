# Design review: leaner reads of term nodes

Independent review (architect agent, 2026-11-25) of [KERNEL_TERM_READS.md](../../design/KERNEL_TERM_READS.md) at 049e9960. Its changes are taken into the design's section "Changes after the design review". The scratch benchmark files it names were machine-local.

DESIGN REVIEW: kernel term reads

Verdict: **approve with changes.** Keep a smaller slice 1, drop slice 2, move slice 3 to the replace-memo candidate (7). Drop the store-origin cell. Add one safe win the design missed: fusing `hash-fmix`.

## For the owner (plain language)
- The idea is right. Reading one field of a term goes through 9 to 11 tiny Forth words, and folding them into one or two words is a real speed-up with no change to what is checked.
- The new "origin" cell the design adds to every store is unsafe and buys nothing. Some stores sit inside the main context's block, and that block moves while modules load. A cell holding an absolute address would then point at freed memory, and the seal would not notice. I measured the safe alternative (read the block address and the capacity, both already in the header) at the same speed. So `lib/store.fs` does not need to change.
- Slice 2 rests on a claim that is false. Some input leaf records have no leaf entry on purpose: projections and lets that the importer copied instead. The per-read lookup is the check that refuses them, so it must stay.
- Slice 3 is sound but small and uncertain. It also edits the same pass as candidate 7, so it belongs in that branch.
- A cheaper win sits in the hashing library: `hash-fmix` is 4.4% of Init, and fusing it halves its cost (measured). That is three lines, checked against the old word on a million inputs.
- Result: one branch of about 30-50 Forth lines and 0.65-0.8M tokens. It gains about 9-12 points, roughly 70-94 s off Init's 779.5 s (estimate). The design's version was 1.5-2.0M tokens for 10.5-17 points.
- Gate: in this reduced form it is ordinary behaviour-preserving work (your decision of 2026-11-19): Forth review and the full tier, reported afterwards. No check moves, the library header and the snapshot are untouched, and the kernel still checks every proof.

## Findings, by severity

**1. Blocking: the origin cell goes stale when a store moves.**
- `store.fs:72-76` promises that a store made in place "has the same bytes wherever it is". That is why `store-block` is 0 for an inline store.
- Inline stores are context members: `context-store:` calls `member-store` and `store-init`, `context.fs:261-263`. The main context is RESIZEd at each later declaration (`context-grow`, `context.fs:204-206`; warning at `:92-93`).
- Three inline context stores exist today: `src/author/constants.fs:30`, `namespaces.fs:114`, `groups.fs:72`.
- After a move, an absolute origin would point into the freed old block. The seal is copied byte for byte with it, so `store-check` still passes and `store-slot` writes into freed memory.
- Other paths that change the block without `store-place` or `store-install`:
  - `tests/core/store-growth.fs:44-47` (`store-move` writes `store-block` and reseals);
  - `tests/support/context-canon.fs:16` (the digest blanks the block and the seal, and would also need the origin blanked);
  - `tests/lib/lib.fs:368-370`;
  - header copies at `src/core/input.fs:522` and `constant-references.fs:399`.
- **Change:** no new header cell. The term store is always a heap store: `lf-terms-make` aborts otherwise (`terms.fs:167-169`). So the fused slot in `terms.fs` reads `store-block` and `store-capacity` from the `lf-terms` header, which is branch-free.
- Measured on `gforth-fast`, 30M reads (fused with the origin cell, then fused with block and capacity, two runs each):
  - origin cell: 101.0 and 97.7 ms;
  - block and capacity: 100.8 and 96.6 ms;
  - today's chain: 307 and 294 ms.
- With this change `store.fs` is unchanged, as are its seal, fault `faults.toml:3459` and every other store (about 25 headers), with no format question.
- Snapshots: no store header is written to disk (`store.fs:45-48`; `snapshot-layer.fs` never names a store header or `lf-terms`).
- Workers: each context owns its own term store (`context.fs:44-53`), and only lendable input and constant-reference headers are copied (`input.fs:513-526`). So no worker sees another's term-store header mid-update.

**2. Blocking for slice 2: "every input leaf has its entry" is false.**
- `feed-mark` marks to copy a projection whose structure child was copied (`feed.fs:355-363`) and a let that is equal to an earlier one (`:444-446`).
- `feed-place` then copies them into the store instead of entering a leaf (`:455-456`). Their tier numbers have no entry by design.
- `lf-tin-valid?` (`terms.fs:353-355`) is the per-read check that refuses those numbers. A shared fed input also bounds leaf visibility per copy with the horizon (`terms.fs:336-349`).
- **Change:** drop slice 2 from the group. A per-read replacement (one load from a per-record entry index instead of a hash probe) belongs to the hashing group, measured there.

**3. Major: say that the width is fixed.**
- The benchmark's fused read uses `4 lshift` (`reads-bench.fs:40`), not `store-width @ *` (`store.fs:86`).
- That is fine: the width is sealed and checked at the root, and `/lf-term` is 16 (`terms.fs:162`). But "same loads" (section 0) is not literally true.
- **Change:** write "fewer loads, same checks", and add a check when the file loads that `/lf-term` is 16.

**4. Major: the fault list is inaccurate.**
- `s2-node-read-unchecked` is in `src/lib/node.fs` (`faults.toml:8076-8081`), not `terms.fs`.
- No fault quotes `lf-term-valid?` (`terms.fs:438`).
- **Change:** add faults on the fused `lf-term-valid?` dropping `store-at?`, and dropping the input test; the slot using a stale base; a wrong `lf-tin-at` offset; a wrong shift in the fused `hash-fmix`.
- No existing `old` text needs updating if `lf-tin-at` and `store-*` keep their bodies or names. That covers `faults.toml:9155`, `:468`, `:3459`, and the `:355` fault (it stays because slice 2 is dropped).

**5. Major: a missed safe win, `hash-fmix`.**
- `hash32.fs:41-42` is 4.42% inclusive (2077 of 47,027 samples). Under it, 46% is `hash-shift` and 35% `hash-mul`: call overhead.
- Fused into one colon definition with the same arithmetic, it is equal to the old word on 1M inputs. 20M calls take 113-115 ms today and 56.6 ms fused. That is about 2 points (estimate), for 3 lines.
- **Change:** put it in slice 1.
- `htab@` (4.27%) is `htab-slot u32@`, the slot load (likely a cache miss), not call overhead. It is the hashing group's work, not this one's.

**6. Minor: slice 3 is sound but should be deferred.**
- Visited nodes are below the pass's start mark (`mixed-open.fs:132-137`), so they are immutable and never rolled back. Caching values (not addresses) across a store growth is safe, and fuel is charged per visit.
- But its 1-2.5 points are an estimate after slice 1, and it edits the pass that candidates 2 and 7 change. `lf-rmemo!` re-deriving `lf-rmemo@`'s key (`replace-memo.fs:100-112`) is exactly candidate 7's work.
- **Change:** move slice 3 to candidate 7's branch.

**7. Minor: the gain arithmetic is inconsistent.** Appendix A's own percentages give 10.6-13.6 points, not the 8-12 stated. Use the recomputation below.

**8. Minor: the member offset.** The fused base needs `lf-term-view`'s offset when `terms.fs` compiles. One small public word in `context.fs` (the design's member-cell defining word), with a test, is enough. Tests reach nothing private.

## Recomputed gain (estimate, from the profile's exclusive shares)
- The address group is 11.95 points:
  - Store-only links: 3.93 (`lf-term-slot` 0.55, `lf-terms` 0.93, `store-slot` 0.91, `store-records` 0.31, `store-identities` 1.10, `store-identity` 0.13).
  - Shared links: 8.02 (`lf-term-view`, `lf-term-base`, `lf-term-input?`).
- Store reads are the benchmark's chain: about 3.93 × 11/5 ≈ 8.6 points, of which 76% goes, ≈ 6.5. The input side's share of view, base and `input?` is about 3.4, half of which goes: ≈ 1.7.
- Input decoding (6.7) loses about 30% when `lf-tin-at` is folded and `lf-tin-code` reads its record once: ≈ 2.0.
- Allowing for cache misses the tight loop does not see, as the design does: **7-10 points for slice 1, plus about 2 for `hash-fmix`: 9-12 points, about 70-94 s. Init about 685-710 s.**
- The profile was taken on `gforth-fast` with 25% profiling overhead (wall 970.5 s against 779.5 s). The shares carry over; the absolute seconds are estimates.

## Cheaper plan (at most about 0.8M tokens)
- **One slice, one branch:**
  - `terms.fs`: `lf-term-base` and `lf-tin-at` as one word each; `lf-term-slot` and `lf-term-identity` from `store-block` and `store-capacity`; the six entry words fetching the base once; `lf-tin-code` reading its record once.
  - `context.fs`: one public offset word.
  - `hash32.fs`: the fused `hash-fmix`.
  - Size: 30-50 Forth lines, 60-100 test lines, 5-6 faults.
- **Untouched:** `lib/store.fs`, the snapshot code and the kernel pass files.
- **Architect step:** this review's word list (above) can serve as it.
- **Evidence:**
  - one before/after Init pair at `--jobs 1` on `gforth-fast`, the same day, load average noted, with the JSON identical outside `measured`, `settings` and `run`;
  - one `make profile-check` afterwards;
  - `make cover-changed`, the new faults, and the full tier once (`make tier`, which already runs every pinned-Lean comparison, the decide and Mathlib slices and the malformed exports).
  - No extra runs at 1 and 4 workers, and no benchmark committed.
- **Tokens:** implementer 0.35-0.45M, Forth review 0.12-0.15M, fixes about 0.05M, tier and done check 0.1-0.15M: **0.65-0.8M**.

## Gate
- The reduced slice is ordinary refactoring of core and kernel code. No check moves, no verdict, diagnostic or fuel changes, and no format changes. The read checks stay per read in the kernel's path; nothing from the front end becomes trusted.
- Two parts of the design would have raised gate questions, and both are dropped:
  - The origin cell changed a general library's header and seal (and is unsafe, finding 1).
  - Slice 2 moved a fail-closed per-read check onto an importer invariant. That is a change to what the checker reads before it accepts, and it would need your gate even if the invariant held.

## Files
- Design: `docs/design/KERNEL_TERM_READS.md`
- My benchmarks:
  - `/tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/origin-bench.fs` (origin cell against block and capacity)
  - `/tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/fmix-bench.fs` (`hash-fmix` today against fused)

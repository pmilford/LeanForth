# Design review: fewer table lookups in the kernel

Independent review (architect agent, 2026-11-26) of [KERNEL_LOOKUPS.md](../../design/KERNEL_LOOKUPS.md) at 8107176d. Its corrections are taken into the design's section "Corrections after the design review". The scratch files it names were machine-local.

DESIGN REVIEW: kernel lookups

Verdict: **rework, then approve.** The direction is right. But the largest gain is overstated by about 2x, the front memo as written is weaker than today's memo (a wrong-result risk in kernel code), the side array's gain rests on a premise the profile contradicts, and the "about 10 times Lean" figure is optimistic.

Reviewed: KERNEL_LOOKUPS.md at 8107176d in the design branch, its measurements folder, main's src, and the prototype (cloned into /tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/lookups-review/proto). I re-read the prototype's profile with `scripts/profile-summary.py --under lf-mixed-level-substitute` (output in /tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/lookups-review/mls.txt and full.txt) and ran one gforth-fast micro-benchmark (bench.fs in the same folder). No Init run and no decide-slice run.

## Findings (by severity)

**1. BLOCKING: the front memo keys by node number; today's memo keys by identity.**
- The design says "keys are node numbers … slots hold numbers" (KERNEL_LOOKUPS.md:110-111) and checks only the result's identity on a hit (:106).
- Today's key is the node's identity, so that "an index taken again by another node is a miss, never a wrong result" (proto src/kernel/replace-memo.fs:20-22, 123-125).
- With number keys: after a rollback reuses number N for a different node, a stale slot returns the old node's result while that result is still live. That is a wrong instantiation result in trusted code.
- Change: key slots by identity, or store the key's identity and check it. Add a planted fault "number reused after rollback".

**2. BLOCKING for "exact": the spill rules do not reproduce today's hits.**
- (a) A failed stamped call cuts the table back to its base (proto replace-memo.fs:113, memo-cut). Entries of an *earlier successful* stamped call that this call spilled are inserted after that base, so the cut removes them. Today they survive. Later lookups then miss where they hit today, and since a hit saves fuel (design :89-90), fuel changes.
- (b) Rule (1) probes the table "if this call or its stamp has spilled or kept entries" (:101-103). That is per call, not per slot. After the first spill in a long pass, and for any stamp that already has table entries, every miss still probes the table. 45% of lookups are stamped (294,669 of 655,857), so most of the claimed saving disappears.
- (c) The call serial has to be a full cell, or the slots have to be cleared when it wraps. A 24-byte slot (:99-100) suggests packed 32-bit fields, and roughly a billion calls on Mathlib would wrap them. Today's epoch is a full cell (proto replace-memo.fs:62).
- Change:
  - protect spilled older entries from the failure cut;
  - use a per-slot "spilled here" bit;
  - state the serial's width;
  - make the experiment count *misses that must probe the table*, not only spills.
- Realistic gain: 5-20 s, not 25-40. Note that inserts cost more than lookups: lf-rmemo! 5.64% (33 s) against lf-rmemo@ 3.67% (22 s). Carrying the key's identity and hash from the lookup to the insert is exact, cheap and lives in lib/memo.fs.

**3. MAJOR: universe substitution's gain is overstated (design 65-90 s, profile supports 20-50 s).** Recomputed from the profile, 13,632 samples, 137.4 s in all:

| Part | Share of the subtree | Seconds |
| --- | ---: | ---: |
| Audit walk | 19.4% | 26.6 |
| — of which set probes | | ~9.8 |
| Graph check `lf-cterm-check` (a third walk the design never mentions, mixed-level-substitute.fs:320-324) | 8.0% | 11.0 |
| Input revalidation | | ~3.8 |
| Sort | 10.6% | 14.5 |
| Build | 56.1% | 77.1 |
| — level work | 16.0% | 21.9 |
| — binary search | 8.6% | 11.8 |
| — conses | 14.1% | 19.3 |
| — new references | | ~5.8 |
| — node re-reads and glue | | ~18 |

- A single walk must still do the level work, the conses, the references, the graph check and the revalidation: about 66 s, which is above the design's 48 s low end. The walk itself is about the audit's cost.
- Saving: **35-50 s** for one walk.
- It is **20-25 s** for an exact variant: keep the audit, and build children-first over the audit's set (the shared walker, with the set as its memo), with no sort and no binary search.
- `lf-mls-kept?` runs two binary searches and `lf-mls-binary` runs two more on every changed binary node (:273-276), so four where two suffice. Fixing that alone is free.

**4. MAJOR: one walk changes fuel or outcomes unless the walker is told otherwise.**
- Today a closed child costs nothing (it is never pushed: :154-166 with walk-children-unless, lib/walk.fs:172-180).
- A child reached before costs one unit (walk-spend? per pop, lib/walk.fs:194-201).
- The prototype walker charges every visit, closed children and memo hits included (proto mixed-open.fs:283-291), and the design keeps that rule (:180-181).
- Level fuel today is spent after all node fuel. The file's contract is that sources are "audited before allocation" (:339-347).
- Interleaving can turn "invalid" into "exhausted" on a malformed input near the fuel limit. It also consumes identity serials on failures that today allocate nothing.
- The audit has to stay anyway: mixed-signature-audit.fs:67 calls lf-mls-audit-formals (:212-214).
- Likelihood:
  - success-path fuel identical with a "closed: no charge" hook: about 75%;
  - failure outcomes identical: not guaranteed.
- Change: do the exact variant (keep the audit, walker build). One walk becomes an owner question with a before/after table.
- Separate lever, for the owner: each level call revalidates every actual "as metered work" (:102-103, lf-lsubst-prepare 9.0% of the subtree, about 12 s). Lean does not do this. Removing it changes fuel.

**5. MAJOR: the side array's premise.**
- Store-format reads cost about as much per read as input decoding does today:
  - store reads: 9.8% (58 s) for 8.11 M field reads and 2.01 M data words;
  - input decoding: 9.6% (57 s) for 6.97 M and 2.29 M.
- The cost is in the read layers (store-at?, slab-at, slab-unit, store-count-valid?, lf-term-base), not in the record format.
- So "57 s down to about 10" (:306) holds only if the side array is read raw (base + 16·i). That raw read is a group-3 lever, and it would equally speed up the 58 s of store reads at no memory cost.
- Change: put a raw-read or validity-at-entry experiment on both tiers first, then decide whether the side array is still worth its memory.

**6. MAJOR: the side array's memory and its paths.**
- 12.2 M × 16 B = 196 MB gross.
- It replaces the P4 dense array. That array is lf-term-base 32-bit entries, about 98 MB if input numbers are about 2 × 12.2 M (terms.fs:240-251: record u is number 2u+1); TERM_STORE.md:156 counted 49 MB.
- Let and projection records are nodes at both parities, so "one slot per expression" needs an overflow area.
- The design's "8-13%" is measured against the prototype's 779 MB, which already went past the 643 to 680 MB the owner was asked about (TERM_STORE.md:183, :280). Against main the side array is about +25-30%. Say that.
- Change:
  - list every path that makes a view and must build the array: feed, snapshot load, front-end readers, print, test helpers;
  - build it before workers start;
  - make the import decode never refuse.
- Refusal: tag 0 refuses at the same read only where lf-term-valid? runs before any field read (terms.fs:460-461, 488-499). Today an unchecked lf-term-tag@ on a leaf without an entry returns the real tag, so the byte-identical malformed-export tests are the guard. Keep them in the experiment.

**7. MINOR: the presence filters.**
- The inferred-type caches store through another word (measurements README:72-73). A filter not set on that path gives false negatives, which means more fuel.
- Change:
  - set the bit on every store path;
  - clear the filter only when its cache is emptied whole, never on a partial cut;
  - add a planted fault "store without bit".
- Gain: 5-10 s.

**8. MINOR: the cons front table.** Its identity check correctly excludes reused numbers. Its key must be exactly the store's cons key, and the horizon (terms.fs, lf-term-horizon!) must be part of the findability re-check.

**9. OK: the hook cost.** On gforth-fast, an xt fetched from a record and EXECUTEd costs 0.6-1.6 ns more than a direct call (bench.fs: 1.7, 2.3 and 3.0-3.3 ns per iteration). At 2-3 hooks a visit against 601 ns a visit that is under 1%. The gains survive.

## Recomputed estimates (one thread, 575.4 s base)

The 5.9 s a point conversion is sound (575.4 / 97.62). The gains below are net of overlaps.

| Group | Design (s) | Recomputed (s) | Basis |
| --- | ---: | ---: | --- |
| 1 | 90-130 | 27-74 | substitution 20-25 exact or 35-50 one walk; memo 5-20; abstract and shift 2-4 |
| 2 | 60-90 | 30-65 | side array 15-40 depending on raw reads; one-read word 5-10 after overlap; cons 10-17; filters 5-10 |
| 3 | 50-90 | 40-90 | not verified; read layers are about 140 s exclusive: store reads 58, base fetch 25, validity 39, field words 18 |

- After all three: **about 345-480 s, 11-15 times Lean, likely about 13 times.** "About 10 times" is optimistic.

## Recommended first step

- **First (about 0.4 M tokens, no gate):** the exact substitution build. Keep the audit and the fuel unchanged; build children-first over the audit's set; drop the sort and binary search; fix the doubled searches. About 20-25 s, measurable on the decide slice in seconds.
- **Then (about 0.2 M tokens), a raw-read experiment on both tiers instead of the side array.** If input reads fall to store cost, the side array's memory may not be worth asking for.
- **A cheaper grouping:**
  - (A) read layers: validity at entry, raw reads, the one-read word;
  - (B) the exact substitution build plus the memo insert fixes in lib/memo.fs;
  - (C) the front tables and filters only where the experiments show probe-avoidance.
  - That is about 3 M tokens instead of 4.5 M.

## Gates and trust

- Kernel trust: the front memo, the cons front table, the filters and the side array are trusted kernel code. Each needs planted faults:
  - number reused after rollback;
  - spilled older entry cut;
  - store without its filter bit;
  - stale slot;
  - wrapped serial.
- Owner gates:
  - memory, stated against main's peak, not the prototype's;
  - any fuel change: the one-walk substitution, or dropping the metered revalidation;
  - anything that moves where malformed data is refused.
- Everything stays behind the kernel: no front-end change.

## Tell the owner (plain language)

"The plan to speed up the checker is sound, but it promises too much. The biggest single item, universe substitution, saves about 20-50 seconds, not 65-90: much of its time is real work (building terms, substituting levels, a validity walk) that a smarter walk does not remove. A safe first version keeps today's fuel exactly and saves about 20-25 seconds cheaply. The proposed 'front memo' cache has two bugs on paper: it could return a stale answer after an undo, and it changes some hit counts. Both are fixable before coding. The 'decoded copy' of the input costs 160-200 MB more than today's main and may gain little, because today's reads of ordinary stored terms are as slow as the input decoding it replaces. Test cheaper reads first. Expect about 13 times Lean's speed after all three groups, not 10. Decisions for you later: extra memory (if still wanted after the experiment), and whether fuel numbers may change for a further 12-30 seconds."

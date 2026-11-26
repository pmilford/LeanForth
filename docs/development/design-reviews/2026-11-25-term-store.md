# Design review: the term store and the kernel speed route

Independent review (architect agent, 2026-11-25) of [TERM_STORE.md](../../design/TERM_STORE.md) at c45b2fd7. Its corrections are taken into the design's section "Corrections after the design review". The scratch files it names were machine-local.

DESIGN REVIEW: term store

**Verdict: rework the measurement and the go/no-go rule before slice 2. Slice 1 can go ahead.** The direction is right: stored hashes, one load per input leaf, a lean walker, substitution on the walker. But the 862 ns figure is broken down wrongly, the "floor" benchmark does not do the same work as the real pass, and slice 2's thresholds would almost certainly say "stop" for the wrong reason. The claim that native primitives stay out of the trusted base is false.

What I reproduced, read-only. Scratch copy with count-patch.py plus my own timer, decide slice, gforth-fast, load 0.7-1.0. Every Appendix A count matches exactly, and the fuel total is 2,649,895 in both runs. `lf-open-pass` took 0.964-1.058 s for 1,322,249 visits, about 730-800 ns a visit with counters in, against the design's 862 ns at load 3.6. bench.fs rebuild: 5.27 ms / 327,767 = 16.1 ns, reproduced. I wrote the profile split script myself: `/tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/tstore-review/split2.py`.

## Cost per instantiation visit on Init, by layer (recomputed)

`lf-open-pass` takes 38.10% inclusive of 656.5 s, which is 250 s. Visits are about 327 M; the design's scaling holds, since my decide timing gives 317 M. That makes about 765 ns a visit:

| Layer (first marker below the pass) | s | ns/visit |
| --- | ---: | ---: |
| hash-consing of rebuilt nodes (`lf-term-cons`) | 60.9 | 186 |
| replace memo lookups and inserts in the walk | 58.2 | 178 |
| memo end: the call's entries deleted one by one (`memo-cut`/`memo-drop-last`) | 26.7 (with begin) | 82 |
| other pass setup (ready, mark, scratch, identify) | 14.3 | 44 |
| reads, dispatch, rest | 36.2 | 111 |
| validity (`readable?`, `valid?`, `children?`) | 16.6 | 51 |
| closed test | 15.1 | 46 |
| frame admit/enter/exit + save/restore + loop | 21.5 | 66 |
| outcome plumbing | 0.7 | 2 |

- **The biggest layer is the hash tables, not the frames.** Memo plus cons is 58% of a visit (about 446 ns). The whole frame machinery is 9% (66 ns). Fuel and outcome values are negligible.
- **Across the whole check, the biggest layer is the read layer.** "Reads of terms, stores, slabs" is 36.85% exclusive, about 242 s. On decide, 16.6 M input-record decodes against 18.9 M field reads means nearly every read goes to an input-tier node.
- So "the layers, not Forth" is true in direction, but the slices aim at the wrong layers first.

## Findings (most serious first)

1. **The breakdown of the 862 ns is wrong (high).**
   - `lf-open-pass` does no audits: 0 audit samples under it on Init. The audit's callers are `mixed-shift.fs:136`, `mixed-beta.fs:94`, `mixed-instantiate.fs:128`, `mixed-compare.fs:276`, `mixed-level-substitute.fs:321` and `constant-term-scope.fs:56`. So the "up to 230 ms audits" share does not exist.
   - The real large items are the memo's per-entry deletion at every call's end (`replace-memo.fs:92-95`, `lib/memo.fs:210-225`: rehash plus Algorithm R per entry, about 20 s on Init) and hash-consing.
   - **Change:** replace section 1's split with the table above (from the profile, not timers). Add the memo cut to list (a): Lean throws its cache away whole.

2. **The floor benchmark is not the same rebuild (high).** The `inst` benchmark (`bench.fs:106-122`) differs from the real pass in three ways:
   - It has no memo, so it walks paths: 327,767 visits over a DAG of about 24 k nodes.
   - `csub` is the constant leaf, so every rebuilt subtree already exists. "nodes 23990" means about zero new nodes, so "new nodes included" (§1) is false.
   - It never touches the input tier. Its `cur` form also uses a store without a view, so the chase never pays the tier decode (`terms.fs:394-396`, `lf-tin-record` at `terms.fs:304-307`) that most real reads pay.

   A fair floor per visit adds about 0.63 conses (raw Forth at scale 179-210 ns each, by the design's own cons benchmark) and about 1 memo operation. That gives roughly 130-230 ns in pure Forth, not 16-24.

   **Change:** benchmark the real visit mix: memo, about 50% new nodes, tier-node reads.

3. **Slice 2's decision rule cannot answer its question (high).**
   - Slice 2 attacks frames, validity, reads and closed roots: at most about 240 ns of 765.
   - It leaves cons and memo (about 446 ns) for slices 1 and 4.
   - My estimate of what slice 2 saves is 25-40 s (closed roots about 13 s, kept children 10-18 s, one read 5-10 s), not 40-65 s.
   - After slice 2 a visit will measure about 650 ns, so the rule says "above 400 ns: stop, the layering is not the cause". That is a false negative.

   **Change:** decide on separate numbers: walk ns per visit without cons and memo, ns per cons, ns per memo operation, and hash probes per fuel unit.

4. **The native-code trust claim is false (high, trust boundary).** §2 says "none of the six decides verdicts". It does: a false hit in the cons probe's record compare or in the memo probe gives a different term, which the kernel then checks, so a wrong theorem could be accepted. The fuel step decides exhaustion. All six would be trusted kernel code; so would the slice 5 macros, as reviewed Forth.

   **Change:** say so plainly. The gate classing (owner approval plus review gate, new runtime dependency) is otherwise right. Also note that libcc needs a C compiler at run time.

5. **"Visits exactly Lean's nodes" is not exact (medium).**
   - "visits = passes + 2 x rebuilt" is true of any binary walker, so it proves nothing about which nodes.
   - In instantiate mode LeanForth descends into Lean-closed nodes that hold a free variable, unless the caches' hook clears them. That keeps a liveness check Lean does not have (`mixed-open.fs:37-42`, `:231-242`, `caches.fs:314-319`).
   - I counted 22,471 of 593,792 rebuilt nodes that Lean would return at once: about 3-4% extra visits.
   - Lean consults its cache before the closed test on every node that may be shared (`.claude/work/D2A/lean-src/replace_fn.cpp`, `apply`). So Lean does more cache lookups than LeanForth, not fewer.

   **Change:** correct both statements. Slice 2 must keep the free-variable rule.

6. **Slice 2 can keep fuel identical, but the design must spell out the conditions (medium).**
   - Charge the second child inline only after the first child's subtree returns.
   - Keep the max-n binder check before any child is charged (`mixed-rebuild.fs:60-65`, `:71-72`).
   - Keep every per-leaf fail-closed test the visit runs today: an unknown tag is bad (`mixed-open.fs:216-222`), a bound variable must be well formed (`:209-211`), a free variable must be live (`:213-214`).
   - A "full" diagnostic records `frame-room@` (`diagnostics.fs:206-207`). Its numbers, and the steps where the meta-sweeps' heap refusals land, change once kept children take no room. That is acceptable for a resource outcome, but declare it and test it.
   - Depth stays bounded: rebuilt nodes still go on the heap frame stack, and the inline tests are constant depth (`frame.fs:59-64`). I confirmed this.
   - The skipped `readable?` and `children?` tests rely on the validity design's invariant; state that.
   - "One read per visit" does not hold for tier nodes (moded records, a let's lambda across two quads, leaves through an entry). It needs a tier "read all" word.

7. **The audit saving is overstated (medium).** The audit is 29.2 s: its walk is 16 s and already uses a marks column (`lf-term-marks`, mark pages: `constant-term-boundary.fs:12-15`). The memo part is about 8 s. So slice 4's "29 to 9 s" should be at most about 8 s saved.
   - The audit is the fail-closed structural check of an input or constant graph before passes read it unchecked. Keep it.
   - Auditing once per input node per run (at import), instead of once per check, would remove most of the walk. But it moves where malformed data is refused, so it needs the gate.

8. **Hash-consing is work Lean does not do (medium).** Lean's `mk_app` allocates and probes no table. `lf-term-cons` is 80 s inclusive on Init, and the C cons figure (61-71 ns) is not Lean's cost. **Change:** move it into list (a), or state it as a design choice with its price.

9. **The floor ratios are optimistic (medium).** (i) 6-9, (ii) 3.5-6 and (iii) 2.5-4 apply in-cache chase ratios to everything. They assume a C version of LeanForth's algorithm runs at Lean's speed, despite hash-consing, tier decoding and about 2.4 hash probes per fuel unit (6.32 M / 2.65 M on decide, about 49 ns each on Init by `htab-find` inclusive). That is about 117 ns per unit before any other work. 3-5 times needs about 140-235 ns per unit in all. whnf, inference and definitional equality are not measured by layer. I would quote (i) 8-12, (ii) 6-9, (iii) 4-6 until a prototype shows more.

10. **Measurements are not fully reproducible (low).** The timer patch ("a second inline script") is not in the folder. Add it.

## Estimates re-based

| Slice | Design | Recomputed | Why |
| --- | --- | --- | --- |
| 1 | 35-55 s | 30-50 s | Plausible: leaf probes 18 s, tier-first probe 28 s |
| 2 | 40-65 s | 25-40 s | See finding 3 |
| 3 | 33-52 s | not verified | |
| 4 | 30-50 s | 30-45 s, but only with the memo cut added | Audit at most 8 s (finding 7); memo cut about 20 s is new |
| 5 | 30-60 s | very uncertain | |

All five end near 450-500 s (13-16 times Lean), not 430 s.

## Cheapest first experiment (do it before or beside slice 1)

A throwaway prototype in a scratch copy, never merged: about a day and 0.2-0.3 M tokens.

- **What:** instantiation only, all three cost groups at once:
  - lean walker: closed root returns at once, kept children inline, one read;
  - memo cut as one reset or generation bump, with a stored hash;
  - leaf entry by a dense array instead of `lf-tin-leaf`'s probe.
- **How:** decide slice runs (about 3 s each) after each change. Fuel 2,649,895 and the report identical outside `measured`. Then one profiled Init run at 1 thread (wall time, not tokens).
- **Numbers that decide:** instantiation ns per visit on Init, split into walk / cons / memo; probes per fuel unit; ns per fuel unit of the prototyped share.
  - Walk at or below about 80 ns, and a cons or memo operation at or below about 150 ns: rewriting every pass in Forth is worth it (about 6-9 times).
  - Pure-Forth 3-5 times is credible only if the whole check can reach about 1.2 probes per fuel unit or fewer.
  - Otherwise 3-5 times needs native code or a different term store (no hash-consing, a direct tier layout).

## Cost and grouping

The design spends 4.8 M tokens to save about 226 s (34%). That is good value only if the target stays near 14 times. Recommended grouping:

- **First:** the prototype (0.3 M).
- **Group 1:** slices 1 and 4 together (all the table work, with the memo cut and the audit memo): about 1.3-1.5 M.
- **Group 2:** slices 2 and 3 together (the walker and substitution on it): about 1.4-1.6 M.
- **Dropped as a slice:** slice 5. Add macros as each hot word is touched; the native proposal is a document.

That is 3.0-3.4 M in all.

## Gates

- Native primitives: correctly classed as owner approval plus review gate, but they are trusted code (finding 4).
- Fuel changes (slice 3): correctly classed as owner's approval.
- Memory 643 to 680 MB: correctly an owner question.
- Moving the audit to import: would be a gate item (finding 7). The design does not propose it.
- Everything in the design stays untrusted front-end-free: only the kernel accepts. Macros and primitives are kernel code.

## What to tell the owner

LeanForth spends about 765 ns on each node an instantiation looks at. More than half of that is two hash-table jobs: finding or adding the rebuilt node (which Lean does not do at all) and the per-call memo, whose entries are also deleted one by one at the end of each call. The frame and fuel machinery the design blames is about a tenth.

The benchmark that put "plain Forth" at 16-24 ns skipped exactly those jobs. A fair Forth floor is roughly 130-230 ns.

So 14 times is about right for the five slices. 3-5 times in pure Forth is not shown, and I doubt it without fewer hash-table probes per step or native code. Native code would be trusted kernel code, not a side helper.

I recommend a one-day throwaway prototype of instantiation first, to measure the real floor, with slice 1 in parallel. Then do the work in two groups instead of five.

Files: `docs/design/TERM_STORE.md`; the instantiation pass is `src/kernel/mixed-open.fs`, with its memo in `src/kernel/replace-memo.fs` and `src/lib/memo.fs`.

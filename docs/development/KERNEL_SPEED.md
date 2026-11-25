# Where the kernel spends its time (measurement of 2026-11-25)

Plan: the Later list's "Parallel running and speed", item 4 (a), the owner's order of 2026-11-23: measure
first, then change algorithms with identical verdicts, then (measured only) native primitives. Branch
`kernel-speed-measure`. No kernel, core or import word was changed. Each number says where it comes from:
**measured** (run for this document, 2026-11-24 23:50 to 2026-11-25 01:00, on the 10-thread Ryzen 5 7600X,
Gforth 1.0.0 `gforth-fast`, one worker), **recorded** (from a document named beside it) or **estimate**
(arithmetic on those). The machine's load average was 0.7 to 1.8 during the profiled run of Init, and 1 to 7
(other agents' tests) during the counted run and the engine runs. Raw outputs, the counter patch and the
scratch copies stayed in a scratch folder and are not in the repository, as in
[PARALLEL_REVIEW.md](PARALLEL_REVIEW.md).

## In short

- LeanForth checks Init (59,349 declarations, 57,919 checks) in 952 s on one worker (measured; 968 s with
  stage and feed, under the profiler). Lean's kernel takes 38.4 s for the same declarations and nanoda 44 s
  (recorded, [lean-kernel-profile-2026-11-02](measurements/lean-kernel-profile-2026-11-02/README.md)):
  **24.8 times** Lean.
- The algorithms are Lean's, and their shares match Lean's and nanoda's: instantiation and universe
  substitution own 48% of the time (Lean 41%, nanoda 51%), whnf 22% (Lean 13%, nanoda 29%).
- The gap is overhead per primitive, in two parts. **(1) LeanForth's own validity checks: 40% of the time**
  is spent inside them (handles, stores and the environment re-checked at every gate; Lean's resource checks
  are 2%). **(2) The term store's layers**: reading one field of a node goes through four to six small
  words; reads of terms, stores and slabs are 33% of the time where the CPU was, hashing and hash tables
  13%.
- Time per declaration is flat: 1.43 µs per fuel unit, from the smallest to the slowest declaration
  (log-log correlation 0.993; no declaration of 20 ms or more is off by a factor of 3). Fuel sees all the
  cost; no hidden cost grows with some declarations.
- Engines, on p1m at one worker under load: Gforth 1.0 `gforth-fast` 166 s CPU, Gforth 1.0 `gforth` 2.5
  times that, Gforth 0.7.3 6.5 to 7 times (measured).
- Answers to the coordinator's questions: (i) universe substitution is skipped wherever Lean skips it (4 of
  3.23 million calls began on a term without universe parameters); instantiation skips every clean node
  but sets up a whole pass first: 42.5% of its 31.8 million passes start on a term Lean returns at once,
  about 2% of the time. (ii) The `whnf_core` cache is keyed as Lean's and read where Lean reads it; it is
  filled almost as Lean fills it (two small differences, below); 3.7% of its 30.6 million lookups hit, a
  lookup costs 755 ns. Lean's own hit rate cannot be counted (no counters); by its code it should be as low.
- Ranked candidates (below): the validity checks moved out of the walks (up to 40%, realistically 25-35%),
  universe substitution as one memoized pass (about 10%), node field reads inlined (about 10%), hashing and
  the table probe as Forth macros or native code (5-10%), and four small ones (about 2% each). Pure-Forth
  changes could plausibly reach 10 to 14 times Lean (**estimate**); 3 to 5 times needs a leaner term store
  as well; native code pays for hashing and the probe, about 10% (**estimate**).

## How it was measured

- **Profile**: `make profile-check`'s tools (this branch; [PROFILING.md](PROFILING.md)) on
  `check --jobs 1 --no-manifest --resources --json` of `.claude/work/IM/init.ndjson` (345 MB), 20 ms
  between samples: 47,366 samples, 968 s wall, 960 s CPU, 641 MB peak (measured). The one-worker run of
  2026-11-23 took 969.8 s without the profiler (recorded, PARALLEL_REVIEW.md): at that interval the
  profiler's cost is within the spread between runs.
- **Counts**: a scratch copy of `src/` with counters at the entry of 30 words and timers around the four
  pass entries (lf-open-pass, lf-mixed-instantiate, lf-mixed-level-substitute, lf-mixed-shift), run on the
  same export at one worker (1,199 s wall: the counters and the load slow it). A count is exact; a time
  from this run is used only as a share within it. **Cost per call** = the word's inclusive seconds in the
  profile / its count.
- **Per declaration**: the JSON report's new `measured.declarationMicroseconds` (this branch) from the
  profiled run, listed by `scripts/slowest-declarations.py`.

## 1. Time by family, beside Lean and nanoda

Shares of Init's samples. Exclusive: where the CPU was. Inclusive: the family anywhere on the stack (they
overlap). Owner: the nearest family outwards that is not a service (store reads, validity, hashing, caches,
frames, library); owners add up to 100%. LeanForth measured; Lean (`leanchecker --fresh Init`) and nanoda
(`init.ndjson`, one thread) recorded on 2026-11-02 with `perf` (their families are named by function, so
some rows are not exact matches).

| Family | LeanForth excl / incl / owner | Lean excl / incl / owner | nanoda excl / incl / owner |
| --- | --- | --- | --- |
| Instantiation and abstraction (replace passes, memo) | 3.9 / 35.6 / 33.8 | 15.2 / 42.9 / 41.3 (with universe substitution) | 9.2 / 33.7 / 33.7 |
| Universe substitution in terms | 3.0 / 20.0 / 14.5 | in the row above (its callers: 12.6 incl.) | 4.7 / 17.3 / 17.3 |
| whnf: `whnf_core`, delta, iota, projections, literals | 2.7 / 59.0 / 21.8 | 3.3 / 46.0 / 13.0 | 5.9 / 63.4 / 28.7 |
| Definitional equality | 1.3 / 69.7 / 8.9 | 0.8 / 54.9 / 6.3 | 0.6 / 68.5 / 2.4 |
| Type inference, declaration checks | 1.5 / 96.7 / 7.5 | 1.7 / 77.3 / 8.6 | 2.2 / 87.7 / 4.2 |
| Level operations | 1.7 / 4.8 / 3.1 | 1.3 / 2.4 / 1.9 | – |
| Scheduler, environment, constant lookup | 2.4 / 98.5 / 8.9 | 8.9 / 11.5 / 15.0 (lookup and replay) | – |
| Term construction and hashing (`lf-term-cons`, htab, hash32) | 13.5 / 26.1 / – | 10.0 / 18.4 / 5.5 (nodes, sharecommon) | 50.4 / 51.8 / – (hash-consing, nodes) |
| Caches and memo tables | 5.7 / 33.8 / – | 24.7 / 30.6 / – (all hash tables) | 10.1 / 11.2 / – |
| **Validity checks** (LeanForth's own; inclusive with the term audit `lf-cterm-check`, 37.1 without) | **12.9 / 39.6 / –** | 2.3 / 2.3 / – (resource checks) | – |
| **Reads of terms, stores, slabs** | **33.1 / 51.7 / –** | – (a pointer read) | – |
| Memory: allocation, freeing, reference counts | small (stores, no freeing per node) | 21.5 / 22.0 / – | 7.6 / 8.0 / – |
| Walk machinery (frames) | 4.8 / 96.4 / – | – (C++ recursion) | – |
| Reading the export | 1.3 (stage, 12.6 s) | 0.4 (olean load) | 6.2 / 9.1 / 9.1 |

By file, where the CPU was: `core/terms.fs` 22.0%, `lib/store.fs` 12.0%, `lib/htab.fs` 8.1%, `lib/slab.fs`
5.7%, `lib/hash32.fs` 5.1%, `lib/bounds.fs` 4.7%, `lib/frame.fs` 3.7%, `lib/memo.fs` 3.5%; every kernel
file 2.4% or less (measured). Of the hashing (htab, hash32, memo: 16.6%), 3.4 points serve term
construction, 4.5 the replace memo, 1.9 the type checker's caches and 6.8 the rest (the audit memo, sets).

## 2. The costliest words

Exclusive (measured, % of Init's samples): htab@ 3.31, lf-term-view 3.24, between? 2.80, lf-term-base
2.55, store-count-valid? 2.28, hash-shift 1.95, lf-tin-code 1.79, hash-mul 1.57, store-identities 1.40,
lf-tin-at 1.26, store-check 1.26, lf-term-input? 1.23, cells= 1.07, htab-find 1.02, slab-at 0.96, slab-unit
0.91, hash-fmix 0.90, frame-loop 0.88, mark-identity 0.75, store-slot 0.75, memo-hash 0.71, lf-term-valid?
0.70, lf-terms 0.69, lf-term-identity 0.68, lf-term-tag@ 0.66. The 25 together: 35%. The profile is flat:
small words of the data layers, none an algorithm.

Inclusive, below the drivers (lf-check-declaration 96.7, inference 94.5, lf-defeq-on 66.5): lf-open-pass
34.4, lf-open-run 34.4, lf-rebuild-run 29.9, frame-run 28.8, lf-instantiate 26.5, lf-wc-tagged 21.5,
lf-wc-app 21.3, lf-wc-head 20.6, lf-wc-beta 20.2, lf-mixed-level-substitute 20.0, lf-mls-pass 20.0,
lf-whnf-beta 19.9, lf-mls-run 19.6, lf-whnf-beta-all 19.2, lf-whnf-put 18.9, lf-env-ours 15.6,
lf-env-current 15.3, lf-env-valid? 15.0, lf-open-updated 14.8, lf-rebuild-joined 14.8, lf-whnf-substitute
14.7, lf-open-update 14.6, lf-mls-apply 13.8, lf-mls-build 13.7, lf-term-add 12.8.

## 3. Calls and cost per call

Init, one worker: calls counted on the scratch copy, seconds from the profile (measured; cost = seconds /
calls). Lean's kernel has no counters; the only count recorded for it on Init is 8.8 million delta and iota
steps (TimedReplay `--diag`, recorded), beside LeanForth's 8.49 million delta unfoldings.

| Primitive (word) | Calls | Inclusive s (share) | Per call |
| --- | ---: | ---: | ---: |
| Term construction (`lf-term-cons`) | 250.1 M | 114.5 (11.8%) | 458 ns |
| Table probe (`htab-find`, every table; 1.21 key compares a probe) | 1,552 M | 91.8 (9.5%) | 59 ns |
| Instantiation passes (`lf-open-pass`, n > 0) | 31.8 M | 332.9 (34.4%) | 10.5 µs |
| - instantiate (beta, function types applied) | 20.0 M | 256.7 | 12.8 µs |
| - instantiate_rev under a scope (closing binders) | 9.48 M | 73.8 | 7.8 µs |
| - instantiate_rev / abstract | 1.93 M / 0.31 M | 7.1 / 5.5 | 3.7 / 17.7 µs |
| Universe substitution (`lf-mixed-level-substitute`) | 3.23 M | 193.4 (20.0%) | 59.9 µs |
| Replace memo lookup / insert (13.3% hits) | 196.1 M / 160.5 M | 35.1 / 47.9 | 179 / 298 ns |
| `whnf_core` beta (`lf-whnf-beta`) | 11.4 M | 192.2 (19.9%) | 16.8 µs |
| delta (`lf-whnf-unfold`) | 8.49 M | 81.8 (8.5%) | 9.6 µs |
| iota, tried (`lf-whnf-iota-step`; recursor reduction `lf-iota-reduce` 108.9 s) | 18.0 M | 49.3 | 2.7 µs |
| projection / let (`lf-whnf-proj-call` / `lf-whnf-zeta`) | 3.06 M / 21 K | 0.2 / 0.6 | – / 29 µs |
| definitional equality steps / lazy delta lookups | 11.6 M / 10.5 M | (recursive) / 17.5 | – / 1.7 µs |
| `lf-env-current` (K1; 6,635 a declaration) | 384.3 M | 147.6 (15.3%) | 384 ns |
| `store-count-valid?` | 3,644 M | 45.8 (4.7%) | 12.6 ns |
| `between?` | 13,126 M | 27.1 (2.8%) | 2.1 ns |
| Term audit at a pass's entry (`lf-cterm-check`; 3.57 M walked) | 20.6 M | 47.9 (5.0%) | 2.3 µs |
| `whnf_core` cache lookup / insert | 30.6 M / 8.08 M | 23.1 / 3.9 | 755 / 483 ns |

The other caches' lookups and hit rates: infer 16.5 M, 33.7%; infer-only 5.01 M, 58.2%; whnf 3.71 M,
61.5%; unfold 5.38 M, 90.7%; success 6.51 M, 9.5%; failure 0.27 M, 0.85% (measured; p1m's rates of
2026-11-18 were the same within 2 points, recorded in PERFORMANCE_SCAN.md K3).

## 4. Question (i): are instantiation and substitution skipped where Lean skips them?

**Universe substitution: yes.** Callers pass a constant without universe arguments through unchanged
(`env-signature.fs` `lf-envsig-bare?`, `whnf.fs` `lf-whnf-value`), as `instantiate_type_lparams` and
`instantiate_value_lparams` do, and inside a pass a subterm whose data word shows no universe parameter is
neither audited nor rebuilt (`lf-mls-closed?`, Lean's `has_param_univ`). On Init 4 of 3.23 million calls
began on a term without universe parameters, 56 µs in all (measured). Its cost is elsewhere: 60 µs a call,
because a call audits the source, collects the reached terms in a set, sorts them and builds each image
with a binary search for its children (`lf-mls-checks` 55.6 s, `lf-mls-build` 132.6 s, of which term
construction 26%), where Lean runs one memoized `replace`.

**Instantiation: per node yes, per call no.** Inside a pass a node whose data word shows no loose bound
variable at or beyond the depth is kept without a visit (`lf-rebuild-clean?`), as Lean's `replace` does.
But `lf-open-pass` sets up the whole pass (copy and check of the substitution, a store mark, the memo, the
frames, the scratch mark) before the root meets that test, where Lean's `instantiate` returns at once when
`get_loose_bvar_range(e) <= s` (and `abstract` when the term has no free variable). On Init 13.5 million of
31.8 million passes (42.5%) began on such a root: 23.8% of instantiate's, 53% of instantiate_rev's and
abstract's, 79.8% of the scope closings'. They took 5.9% of the passes' time in the counted run, about
1.8 µs each: about 2% of the check (20 s, **estimate** from the profile's 333 s for all passes). A test of the
root's data word before the set-up removes them, charging the one unit of fuel the root's visit charges
today so that fuel counts stay identical. The single-binder `lf-mixed-instantiate` (721 calls) and the
lift `lf-mixed-shift` (4,488) are not hot.

## 5. Question (ii): the `whnf_core` cache

**Keyed as Lean's**: by the node, which hash-consing makes Lean's structural `==`; LeanForth also keeps no
result for a key with loose bound variables whose pass read the inference scope (a key Lean never has).
**Read where Lean reads it**: on entry to a node that is not an easy case (Lean's type_checker.cpp 490-493)
and at each step within a visit (Lean's recursive calls). **Filled almost as Lean**: Lean inserts at the
end of a visit in full mode only, never with `cheap_rec` or `cheap_proj` (547-549), which is how
definitional equality calls it (1155-1156, and lazy delta 983-1014), so most lookups come from calls that
cannot fill it. Two differences, read from both sources: Lean does not insert after an iota reduction or
a stuck application (it returns at 533 and 535), and it does insert a stuck projection (`r = e`);
LeanForth inserts every result that is not the node itself.

On Init (measured): 30.6 M lookups, 1.13 M hits (3.7%), 29.5 M misses, 8.08 M inserts: each entry is read
0.14 times on average. A lookup costs 755 ns, an insert 483 ns: 27 s, 2.8% of the check, against the hits'
saving, not measured (a hit saves one `whnf_core` visit). Most of a lookup's cost is not the table: the key
(`lf-node-key`) re-checks the node's facts and the liveness of its free variables (`lf-term-facts` 44.6 s
and `lf-fvars-live?` 31.2 s inclusive over all caches). Lean's own hit rate cannot be counted (its kernel
has no counters and perf placed no probes, recorded). By its code it should be about as low: the same
lookups, mostly on terms the previous unfolding just built, and slightly fewer entries (no iota results).
The cache must stay (it is Lean's); a key that needs no re-check would make it much cheaper (**estimate**:
to a fifth).

## 6. Time per declaration

From `declarationMicroseconds` of the profiled run (measured): the checks add up to 936.9 s of the check
phase's 952.5 s. Median 2.8 ms (Lean 120 µs, recorded), mean 16.2 ms. The slowest 20 take 6.3% of the time,
the slowest 1% 32.3%, the slowest 10% 77.7% (Lean: 32.0% and 75.6%, recorded). The 30 slowest, with their
fuel (`scripts/slowest-declarations.py -n 30`):

| # | Declaration (`_private.Init.Data.` shortened to `…`) | ms | Fuel | ns/fuel |
| ---: | --- | ---: | ---: | ---: |
| 1 | `…Vector.Extract.0.Vector.extract_append._proof_1` (Lean 285 ms) | 6,264 | 4,382,815 | 1,429 |
| 2 | `…Array.Extract.0.Array.extract_append._proof_1_1` (Lean 209 ms) | 6,141 | 4,342,962 | 1,414 |
| 3 | `…Vector.Extract.0.Vector.extract_extract._proof_1` | 4,639 | 3,249,616 | 1,428 |
| 4 | `…Array.Extract.0.Array.extract_append_extract._proof_1_1` | 4,016 | 2,788,611 | 1,440 |
| 5 | `…Vector.Extract.0.Vector.extract_append_extract._proof_1` | 3,921 | 2,814,234 | 1,393 |
| 6 | `…Array.Extract.0.Array.extract_append._proof_1_4` | 3,429 | 2,430,202 | 1,411 |
| 7 | `…BitVec.Lemmas.0.BitVec.getMsbD_extractLsb._proof_1_4` | 2,899 | 1,886,736 | 1,536 |
| 8 | `…Array.Extract.0.Array.extract_append_extract._proof_1_3` | 2,860 | 2,059,550 | 1,389 |
| 9 | `…Array.Extract.0.Array.extract_reverse._proof_1_2` | 2,814 | 1,978,652 | 1,422 |
| 10 | `…Array.Extract.0.Array.extract_extract._proof_1_1` | 2,765 | 1,948,072 | 1,420 |
| 11 | `…Array.Extract.0.Array.extract_add_left._proof_1_2` | 2,631 | 1,917,083 | 1,372 |
| 12 | `…Int.DivMod.Lemmas.0.Int.add_one_tdiv._proof_1_1` | 2,157 | 1,558,019 | 1,384 |
| 13 | `…Vector.Extract.0.Vector.extract_reverse._proof_1_1` | 2,143 | 1,525,321 | 1,405 |
| 14 | `…Vector.Extract.0.Vector.extract_add_left._proof_1` | 2,129 | 1,533,422 | 1,389 |
| 15 | `…Array.Extract.0.Array.extract_append._proof_1_3` | 1,809 | 1,336,089 | 1,354 |
| 16 | `…Vector.Extract.0.Vector.extract_reverse._proof_1` | 1,763 | 1,258,689 | 1,401 |
| 17 | `…List.ToArray.0.List.insertIdx_toArray._proof_1_8` | 1,707 | 1,198,239 | 1,425 |
| 18 | `…BitVec.Lemmas.0.BitVec.getMsbD_extractLsb._proof_1_1` | 1,701 | 1,156,234 | 1,472 |
| 19 | `…Dyadic.Basic.0.Dyadic.toRat_mul._proof_1_8` | 1,682 | 1,300,559 | 1,293 |
| 20 | `Lean.Grind.Ring.OfSemiring.mul_helper` (Lean 66 ms) | 1,589 | 1,085,373 | 1,464 |
| 21 | `…BitVec.Lemmas.0.BitVec.getMsbD_extractLsb._proof_1_3` | 1,547 | 1,052,145 | 1,470 |
| 22 | `ByteArray.utf8DecodeChar?_utf8EncodeChar_append` (Lean 57 ms) | 1,525 | 939,554 | 1,623 |
| 23 | `…Dyadic.Basic.0.Dyadic.toRat_add._proof_1_17` | 1,482 | 1,089,305 | 1,360 |
| 24 | `…Array.Extract.0.Array.reverse_extract._proof_1_3` | 1,370 | 934,797 | 1,465 |
| 25 | `…Array.Extract.0.Array.extract_append_extract._proof_1_2` | 1,349 | 943,024 | 1,431 |
| 26 | `…String.Lemmas.Pattern.String.ForwardSearcher.0.…ForwardSliceSearche…` | 1,341 | 1,364,102 | 983 |
| 27 | `…String.Pattern.String.0.…ForwardSliceSearcher.finitenessRelation._proof_…` | 1,258 | 1,253,104 | 1,004 |
| 28 | `…Nat.Lemmas.0.Nat.sub_max_sub_left._proof_1_1` | 1,227 | 893,472 | 1,373 |
| 29 | `…Dyadic.Basic.0.Dyadic.toRat_add._proof_1_18` | 1,205 | 883,659 | 1,363 |
| 30 | `…Nat.Lemmas.0.Nat.sub_min_sub_left._proof_1_1` | 1,198 | 830,567 | 1,443 |

Time per fuel unit is flat (measured; aggregate ns per fuel unit by fuel used): 2,834 below 100 fuel
(1,777 declarations; a fixed cost of about 170 µs a declaration), 1,738 for 100-1,000, 1,466 for
1,000-10,000, 1,420 for 10⁴-10⁵, 1,424 for 10⁵-10⁶, 1,391 above 10⁶; 1,431 over all. Among the 6,502
declarations of 20 ms or more, none is three times off the median (1,464). So no cost hides from fuel; the
same omega proofs lead here as in Lean, at 22 to 29 times Lean's time each.

## 7. The same check on each engine

`check --jobs 1 --no-manifest --resources` of p1m (the first million lines of the Mathlib export, 9,202
declarations, 51 MB; measured, load average in brackets; CPU seconds are the fairer figure under load):

| Engine | Wall s | CPU s | Check phase, CPU s | CPU against Gforth 1.0 `gforth-fast` | Load |
| --- | ---: | ---: | ---: | ---: | --- |
| Gforth 1.0 `gforth-fast` (what `check` runs) | 172.2 | 166.5 | 164.2 | 1.00 | 4.5-6.7 |
| Gforth 1.0 `gforth` (the checking engine, `--checked`; the tests' engine) | 426.7 | 415.0 | 409.0 | 2.49 | 6.7-10.0 |
| Gforth 0.7.3 `gforth` (the binary `gforth073.sh` runs) | 1,286.4 | 1,178.3 | 1,156.6 | 7.08 | 10.0-4.2 |
| Gforth 0.7.3 `gforth-fast` | 1,108.7 | 1,074.4 | 1,057.9 | 6.45 | 4.2-6.6 |

All four accepted the 9,202 declarations. `gforth073.sh` itself cannot run this check: it stops every run
after 120 s (`timeout -k 5 120`, for the unit tests of `make daily`), so the same binary was run with the
wrapper's settings and no time limit. The load made the runs slower than on an idle machine: the
`gforth-fast` run took 146.0 s wall and 145.8 s CPU at load 0.14 on 2026-11-23 (recorded,
PARALLEL_REVIEW.md), 14% less CPU than today (two threads share a core). The ratios are therefore rough,
but the order is clear: Gforth 1.0's `gforth-fast` is 2.5 times its `gforth` and 6 to 7 times Gforth 0.7.3.

## 8. Front end: `lf-instantiate-mvars` scans every metavariable

Read: each call (`src/front/mvars.fs` 843-848) runs `mv-any-delay` (702), a loop over every metavariable of
the context testing for a ready delayed assignment, and allocates a spine table of two cells for every
term of the whole term store (`mv-spine-block`, 840-842), before its walk. Measured on the longest accepted
text, `tests/front/tactics/decide/sy-vars-init.lf` (344 lines, against Init's snapshot and elaboration
data, a scratch copy timing each call): 8,149 calls; a call took 7 µs with at most one metavariable, 15 µs
with 8 to 127 and 17 to 20 µs with 128 to 511; the scan alone grew linearly, 0.06 µs to 2.9 µs (about 7.6
ns a metavariable). No test text reaches 3,300 metavariables, so yesterday's 430 µs could not be
repeated; the scan alone would be about 25 µs there (**estimate**). The fix, as Lean does it: (1) skip a
term without metavariables (Lean's `if !e.hasMVar then return e`; the data word would need that bit);
(2) no global scan: Lean looks up a delayed assignment only for a metavariable head the walk meets, or a
count kept when a pending metavariable is assigned would answer in O(1); (3) the spine cells in a table of
the walk's own nodes (`memo`) rather than an array over the whole store. Not changed here.

## 9. Ranked candidates

None of these may change what the kernel accepts, nor its fuel counts; each is [kernel] or core code under
the review gate, with the full tier and every pinned-Lean comparison. Shares are of Init's check (952 s).

| # | What | Share it could remove (basis) | Kind | Files | Size (Forth lines) | Trust risk |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | Validity checks out of the walks: the environment and stores validated once per pass and when a store changes (K1), node handles checked once when a pass takes a term (the audit memo already knows them), fields read unchecked inside a pass | up to 40% (samples under a validity word), realistically 25-35% (**estimate**) | algorithm, identical verdicts | kernel/environment.fs, caches.fs, whnf.fs; core/terms.fs; lib/store.fs | 200-400 | high: moves fail-closed checks; malformed-input tests must still fail closed |
| 2 | Universe substitution as one memoized `replace` pass (as instantiation's), without the reached set, the sort and the binary search | about 10% of the 20% (**estimate**: nanoda's is 7.5 s) | algorithm | kernel/mixed-level-substitute.fs | 150-250 | medium: same results and fuel |
| 3 | Node field reads inlined: `lf-term-first@`, `-second@`, `-tag@`, `-data@` as one address computation, not view, base, input test and slab layers | about 10% (reads are 33% exclusive; **estimate**) | macro or inlining | core/terms.fs, lib/slab.fs, lib/store.fs | 50-150 | low if equal on every input |
| 4 | Hashing and the probe (`hash32` 5.1% and `htab` 8.1% exclusive): one fused hash word and an unrolled probe, or a native primitive | 5% as Forth macros, about 10% native (**estimate**) | macro, or native (owner's gate) | lib/hash32.fs, lib/htab.fs, lib/memo.fs | 30-80 | none for Forth; native is a new dependency |
| 5 | Instantiation passes whose root is clean skipped before the set-up (charging the root's unit of fuel) | 2% (counted: 13.5 M passes at 1.8 µs) | algorithm | kernel/mixed-open.fs | 5-15 | low |
| 6 | Cache keys without the re-check of facts and liveness at each lookup | about 2% (755 ns a `whnf_core` lookup, 26 s for all lookups) | algorithm | kernel/caches.fs | 20-60 | medium: the liveness rule must hold |
| 7 | Replace memo cheaper per operation (179 ns a lookup, 298 ns an insert), same hits | about 4% (**estimate**: half of its 83 s) | algorithm | kernel/replace-memo.fs, lib/memo.fs | 30-80 | low: same results and fuel |
| 8 | `lf-instantiate-mvars` (front end, section 8) | none of the kernel; grows with proofs | algorithm | front/mvars.fs | 20-60 | none (untrusted front end) |

## 10. Projection

Where the 24.8 times goes (**estimate** from the shares above): the validity checks are about 380 s of 952; reading
terms through the store layers and hashing are most of the rest of the excess. The algorithms themselves
(the owners) cost about what Lean's cost, times the price of a primitive: a field read is four to six
colon calls (Gforth's `gforth-fast` costs about 1-3 ns a call and return) where C++ reads a pointer; a new
node costs 458 ns (Lean: an allocation and a hash, tens of ns).

- Candidates 1, 2, 5, 6 and 7 (algorithms): about 45-55% off, 430-520 s, 11-14 times Lean.
- With 3 and 4 as Forth macros: about 370-450 s, 10-12 times.
- Native hashing and probe (4): about 330-420 s, 9-11 times; a native field read would add a few percent
  more, but inlining in Forth gets most of it.
- 3 to 5 times Lean (115-190 s) is not in reach of local changes: it needs a term store where a node is
  one block read directly (no view, base and slab layers), passes that walk once (no audit walk before the
  build), and Forth words fused into fewer, larger ones on the hot paths. Even then Gforth's threaded code
  stays a few times slower per primitive than compiled C++ (**estimate**).

Which primitives would pay as native code: (a) hashing and the table probe, about 10%; (b) a node field
read, a few percent after inlining; nothing else is above 3% once the validity checks are moved.

## 11. Not measured

- Lean's and nanoda's call counts and cache hit rates: neither exposes counters, and no new run of them was
  made for counts; their shares are the recorded ones of 2026-11-02 (same export, same machine).
- Nodes visited per instantiation or substitution pass, and what a `whnf_core` hit saves.
- Allocation (`ALLOCATE`, `FREE`) on Init; p1m's were 42 a declaration (recorded, PERFORMANCE_SCAN.md).
- A front-end context of 3,300 metavariables (no test text has one).
- Timings on an idle machine for the engine runs (load in the table).

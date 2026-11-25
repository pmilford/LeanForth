# Where the kernel spends its time (measurement of 2026-11-25)

Plan: the Later list's "Parallel running and speed", item 4 (a), the owner's order of 2026-11-23: measure
first, then change algorithms with identical verdicts, then (measured only) native primitives. Branch
`kernel-speed-measure`. No kernel, core or import word was changed. Each number says where it comes from:
**measured** (run for this document, 2026-11-24 23:50 to 2026-11-25 01:00, on the 10-thread Ryzen 5 7600X,
Gforth 1.0.0 `gforth-fast`, one worker), **recorded** (from a document named beside it) or **estimate**
(arithmetic on those). The machine's load average was 0.7 to 1.8 during the profiled run of Init, and 1 to 7
(other agents' tests) during the counted run and the engine runs. Raw outputs, the counter patch and the
scratch copies stayed in a scratch folder and are not in the repository, as in
[PARALLEL_REVIEW.md](PARALLEL_REVIEW.md). That night's profiled run is **run 1**. **Run 2** is a second profile of
Init made the same way on 2026-11-25 07:59 to 08:18 (57,421 samples; 1,188 s wall while other test runs
used the machine, so its time is not comparable, its sample shares are), kept read-only with its tables in
`.claude/work/init-profile-2026-11-25/` of the main checkout (`check.prof`, `check.syms`, `run.log`). The
summary's shares, section 1, section 2, candidate 1's callers and the projection (section 10) are
recomputed from run 2; sections 3 to 7 and the counts are run 1's (and its counted copy's).

## In short

- LeanForth checks Init (59,349 declarations, 57,919 checks) in 952 s on one worker (measured; 968 s with
  stage and feed, under the profiler; 824 s with the environment stamp of branch `kernel-validity-1`,
  section 10). Lean's kernel takes 38.4 s for the same declarations and nanoda 44 s
  (recorded, [lean-kernel-profile-2026-11-02](measurements/lean-kernel-profile-2026-11-02/README.md)):
  **24.8 times** Lean.
- The algorithms are Lean's, and their shares match Lean's and nanoda's: instantiation and universe
  substitution own 47% of the time (run 2; Lean 41%, nanoda 51%, recorded), whnf 22% (Lean 13%, nanoda 29%).
- The gap is overhead per primitive. Exclusive shares (where the CPU was; run 2): **reads of terms, stores
  and slabs 40.3%** (reading one field of a node goes through four to six small words), **hashing and hash
  tables 16.3%** (`lib/htab.fs`, `lib/hash32.fs`, `lib/memo.fs`; the one hashing figure used here) and
  **LeanForth's own validity checks 12.5%** (handles, stores and the environment re-checked at every gate;
  Lean's resource checks are 2.3%, recorded). They overlap: 16.7 points of the reads and 4.1 of the hashing
  are made inside a validity word, so the checks with what they call take 35.9% (inclusive); outside them,
  reads are 23.6% and hashing 12.3%.
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
- Ranked candidates (below; points of the 952 s, each net of the candidates before it): the validity checks
  moved out of the walks (36 under a validity word, 13-17 of them movable: section 10), universe
  substitution as one memoized pass (5-8), node field reads inlined (6-9), hashing and the table probe as
  Forth macros (2.4) or native code (4.7), and three small ones (0.4 to 3.1). The algorithm changes alone
  could reach 17 to 19 times Lean, with the field reads and hashing as Forth macros 14.5 to 17 times
  (**estimate**, section 10); 3 to 5 times needs a leaner term store as well.

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

Shares of Init's samples in run 2, the rows exactly as `python3 scripts/profile-summary.py check.prof
check.syms` prints them (measured). Exclusive: where the CPU was. Inclusive: the family anywhere on the
stack (they overlap). Owner: the nearest family outwards that is not a service (store reads, validity,
term construction, caches, frames, other library, runtime); owners add up to 100%. Lean (`leanchecker
--fresh Init`) and nanoda (`init.ndjson`, one thread) recorded on 2026-11-02 with `perf` (their families
are named by function, so some rows are not exact matches). Run 1's version of this table merged some rows
by hand and counted only `core/terms.fs`, `lib/store.fs` and `lib/slab.fs` as reads (33.1% there; 32.0% of
run 2 by that grouping); the tool's reads row now holds all of `src/core` with the store and slab files.

| Family (the tool's row) | LeanForth excl / incl / owner | Lean excl / incl / owner | nanoda excl / incl / owner |
| --- | --- | --- | --- |
| instantiation and abstraction (replace passes) | 3.31 / 35.13 / 33.63 | 15.2 / 42.9 / 41.3 (with universe substitution and the memo) | 9.2 / 33.7 / 33.7 (with the memo) |
| instantiation memo (replace memo) | 0.72 / 21.11 / – | in the row above | in the row above |
| universe substitution | 2.72 / 19.07 / 13.86 | in the first row (its callers: 12.6 incl.) | 4.7 / 17.3 / 17.3 |
| whnf_core, whnf: rest (head, delta, projection, let) | 2.13 / 58.56 / 20.76 | 3.3 / 46.0 / 13.0 (all of whnf) | 5.9 / 63.4 / 28.7 (all of whnf) |
| whnf_core: recursors, quotients (iota) | 0.41 / 17.25 / 0.93 | in the row above | in the row above |
| whnf: Nat and String literals | 0.17 / 0.71 / 0.61 | in the row above | in the row above |
| definitional equality | 1.17 / 69.05 / 8.76 | 0.8 / 54.9 / 6.3 | 0.6 / 68.5 / 2.4 |
| type inference, declaration checks | 1.52 / 95.99 / 7.10 | 1.7 / 77.3 / 8.6 | 2.2 / 87.7 / 4.2 |
| level operations | 1.53 / 4.57 / 2.91 | 1.3 / 2.4 / 1.9 | – |
| scheduler, environment, publishing | 2.65 / 97.64 / 9.03 | 8.9 / 11.5 / 15.0 (lookup and replay) | – |
| term construction and hashing (lf-term-cons, htab, hash32) | 13.43 / 25.97 / – | 10.0 / 18.4 / 5.5 (nodes, sharecommon) | 50.4 / 51.8 / – (hash-consing, nodes) |
| caches (infer, whnf, defeq, free-variable memo; with `lib/memo.fs`) | 4.78 / 33.38 / – | 24.7 / 30.6 / – (all hash tables) | 10.1 / 11.2 / – |
| **validity checks** (41.28 inclusive with the term audits `lf-cterm-check`, `lf-mls-checks`) | **12.45 / 35.93 / –** | 2.3 / 2.3 / – (resource checks) | – |
| **reads of terms, stores, slabs (src/core, store.fs, slab.fs)** | **40.31 / 58.63 / –** | – (a pointer read) | – |
| walk machinery (frames) | 4.69 / 95.66 / – | – (C++ recursion) | – |
| other library (bounds, outcomes, contexts; inclusive: `timed` and `ok-each` hold every check) | 5.63 / 96.46 / – | – | – |
| import and decoding (reading the export) | 1.27 / 2.27 / 2.27 | 0.4 (olean load) | 6.2 / 9.1 / 9.1 |
| Gforth runtime, C library, command line, other | 1.11 / – / 0.14 | – | – |
| Memory: allocation, freeing, reference counts (not a row of the tool) | small (stores, no freeing per node) | 21.5 / 22.0 / – | 7.6 / 8.0 / – |

The validity family is a list of names (`VALID` in the tool). It counts `between?`, a general bounds word of
`lib/bounds.fs`, wholly: 2.53% exclusive, of which 0.57 is called directly by a validity word and 2.24 lies
under one somewhere on the stack (measured, run 2). Checks named otherwise (`lf-pool-sound?`,
`frame-sound?`, `htab-shape?`, `slab-has?`) are not in it.

By file, where the CPU was (run 2): `core/terms.fs` 22.95%, `lib/store.fs` 11.65%, `lib/htab.fs` 8.52%,
`lib/slab.fs` 5.62%, `lib/bounds.fs` 4.53%, `lib/hash32.fs` 4.44%, `lib/frame.fs` 3.56%, `lib/memo.fs`
3.35%, `kernel/environment.fs` 3.02%; every other kernel file 2.4% or less (measured). Of the hashing
(htab, hash32, memo: 16.31%), 3.69 points serve term construction, 4.23 the replace memo, 3.07 the type
checker's caches and 5.33 the rest (the audit memo, sets).

## 2. The costliest words

Exclusive (measured, run 2, % of Init's samples): htab@ 3.74, lf-term-view 3.01, between? 2.53,
lf-term-base 2.49, store-count-valid? 2.04, lf-tin-code 1.80, hash-shift 1.67, store-identities 1.44,
hash-mul 1.43, lf-tin-at 1.29, cells= 1.24, store-check 1.19, lf-term-input? 1.17, htab-find 1.05, slab-at
0.93, slab-unit 0.91, lf-term-valid? 0.90, store-slot 0.79, frame-loop 0.78, memo-hash 0.76, mark-identity
0.75, lf-terms 0.75, lf-term-identity 0.73, lf-term-tag@ 0.68, hash-fmix 0.66. The 25 together: 34.7%. The
profile is flat: small words of the data layers, none an algorithm.

Inclusive, below the drivers (run 2; lf-check-declaration 95.98, lf-minfer-walk-run 93.85, lf-defeq-on
66.03): lf-open-pass 34.06, lf-open-run 34.04, lf-rebuild-run 29.71, frame-run 28.68, lf-instantiate
26.10, lf-wc-tagged 21.47, lf-wc-app 21.21, lf-wc-head 20.47, lf-wc-beta 20.09, lf-whnf-beta 19.67,
lf-mixed-level-substitute 19.06, lf-mls-pass 19.05, lf-whnf-beta-all 19.00, lf-whnf-put 18.62, lf-mls-run
18.61, lf-env-ours 14.95.

## 3. Calls and cost per call

Init, one worker: calls counted on the scratch copy, seconds from run 1's profile (measured; cost = seconds /
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
| 1 | Validity checks out of the walks: the environment and stores validated once per pass and when a store changes (K1), node handles checked once when a pass takes a term (the audit memo already knows them), fields read unchecked inside a pass | up to 36% (run 2: samples under a validity word; 41% with the term audits), of which 13-17 points can move (**estimate**; section 10) | algorithm, identical verdicts | kernel/environment.fs, caches.fs, whnf.fs; core/terms.fs; lib/store.fs | 200-400 | high: moves fail-closed checks; malformed-input tests must still fail closed |
| 2 | Universe substitution as one memoized `replace` pass (as instantiation's), without the reached set, the sort and the binary search | 5-8 points (**estimate**: about half of the 13.1 points of its 19.1% that lie outside validity words; nanoda's is 7.5 s) | algorithm | kernel/mixed-level-substitute.fs | 150-250 | medium: same results and fuel |
| 3 | Node field reads inlined: `lf-term-first@`, `-second@`, `-tag@`, `-data@` as one address computation, not view, base, input test and slab layers | 6-9 points (**estimate**: a third to a half of the 18.0 points of reads outside validity words, substitution and the memo) | macro or inlining | core/terms.fs, lib/slab.fs, lib/store.fs | 50-150 | low if equal on every input |
| 4 | Hashing and the probe (`hash32` 5.1% and `htab` 8.1% exclusive): one fused hash word and an unrolled probe, or a native primitive | 2.4 points as Forth macros, 4.7 native (**estimate**: a third or two thirds of the 7.1 points of hashing outside validity words, the replace memo and substitution) | macro, or native (owner's gate) | lib/hash32.fs, lib/htab.fs, lib/memo.fs | 30-80 | none for Forth; native is a new dependency |
| 5 | Instantiation passes whose root is clean skipped before the set-up (charging the root's unit of fuel) | 2% (counted: 13.5 M passes at 1.8 µs), 1.5 points beyond candidate 1 | algorithm | kernel/mixed-open.fs | 5-15 | low |
| 6 | Cache keys without the re-check of facts and liveness at each lookup | 0.4 points beyond candidate 1: of `lf-node-key`'s 2.17% (run 2), 1.79 lies under validity words (`lf-fvars-live?` 1.59) | algorithm | kernel/caches.fs | 20-60 | medium: the liveness rule must hold |
| 7 | Replace memo cheaper per operation (179 ns a lookup, 298 ns an insert), same hits | 3.1 points (**estimate**: half of the 6.2 points of its lookups and inserts, 8.30% in run 2, outside validity words; its hashing included) | algorithm | kernel/replace-memo.fs, lib/memo.fs | 30-80 | low: same results and fuel |
| 8 | `lf-instantiate-mvars` (front end, section 8) | none of the kernel; grows with proofs | algorithm | front/mvars.fs | 20-60 | none (untrusted front end) |

**Candidate 1: where the checks are called** (run 2, samples by the immediate caller on the sampled stack;
counts are run 1's counted copy). `lf-env-current` (14.60% inclusive, 384.3 M calls) is called only by
`lf-env-ours` (14.57), which is called by `lf-whnf-env?` (11.87) and `lf-env-snapshot` (3.08); one level
further out: `lf-caches-on?` 5.91, `lf-audit-on?` 3.92, `lf-env-readable` 1.65, `lf-env-lookup-found` 1.40,
`lf-whnf-delta-of` 0.70, `lf-iota-recursor` 0.56, `lf-quot-rule` 0.56. `store-count-valid?` (4.54%, 3,644
M calls): `mark-this?` 2.12, `lf-pool-sound?` 0.98, `lf-term-count-valid?` 0.42, `store-open?` 0.37,
`store-mark` 0.28, `lf-level-count-valid?` 0.11, `store-valid?` 0.10. `between?` (2.53% exclusive, 13,126 M
calls) is a general bounds word: its callers are `upto?` 0.92, `store-count-valid?` 0.57, `mark-count?`
0.44, `htab-shape?` 0.23, `frame-sound?` 0.16, `lf-env-sane?` 0.09, `slab-has?` 0.06; 0.57 points come
from validity callers and 1.96 from others, of which 1.67 still lie under a validity word further out.

**The invariant candidate 1 needs** (a design assumption, to be verified before the change): a handle
checked once when a pass takes it stays valid for the whole pass if (a) no store is rolled back, cut or
freed while a pass runs (marks, `lf-term-rollback`, `memo-cut` and scratch marks only at a pass's end or
outside it); (b) every handle a pass makes is valid by construction (returned by the store that holds it,
in that store's current generation); (c) a pass reads no other context's handles (each worker its own
stores; the shared environment read only through handles checked at entry). The checks that must remain at
a pass's entry: the environment is the current one and valid (`lf-env-current` once per pass, and again
after anything that can change it), each input term handle and its store count (`lf-term-input?`,
`store-count-valid?`), the substitution's handles, and every bounds check of data read from the export.

## 10. Projection

Every figure is an **estimate**: a share of run 2's samples (measured) times run 1's 952 s for the check
(measured), Lean's 38.4 s (recorded). Shares are added as points of the 952 s, not compounded; each row
removes first what the rows before it already take (the overlap), so the rows can be added.

| Candidate | Basis, points | Overlap removed, points | Points taken | Seconds | Seconds left | Times Lean |
| --- | --- | --- | ---: | ---: | ---: | ---: |
| 1 validity checks | 35.9 under a validity word (41.3 with the audits) | – | 13-17 | 124-162 | 790-828 | 20.6-21.6 |
| 2 universe substitution | 19.1 inclusive | 6.0 under validity words (its audit `lf-mls-checks` 1.7 of them) | 5-8 | 48-76 | 714-780 | 18.6-20.3 |
| 5 clean roots | 2.1 (20 s, run 1's counted copy) | 0.6 (27% of `lf-open-pass` lies under validity words) | 1.5 | 14 | 700-766 | 18.2-19.9 |
| 6 cache keys | 2.17 (`lf-node-key`) | 1.79 under validity words (`lf-fvars-live?` 1.59) | 0.4 | 4 | 696-762 | 18.1-19.8 |
| 7 replace memo | 8.30 (`lf-rmemo@`, `lf-rmemo!`) | 2.1 under validity words; its hashing (3.9) stays here, not in 4 | 3.1 | 30 | 666-732 | 17.3-19.1 |
| 3 field reads inlined | 40.3 reads exclusive | 16.7 under validity, 4.6 in substitution, 1.0 in the memo | 6-9 | 57-86 | 580-675 | 15.1-17.6 |
| 4 hashing and probe, Forth macros | 16.3 hashing exclusive | 4.1 under validity, 3.9 in the memo, 1.3 in substitution | 2.4 | 23 | 557-652 | 14.5-17.0 |
| 4 the same, native | the same 7.1 | the same | 4.7 | 45 | 535-630 | 13.9-16.4 |

**Candidate 1 is 13-17 points, not the 25-32 of the first version of this table** (corrected 2026-11-25
from [KERNEL_VALIDITY_CHECKS.md](../design/KERNEL_VALIDITY_CHECKS.md), sections 1 and 5, and its review).
Of the 35.9 points under a validity word, the three slices of that design can move `lf-env-ours`'s 14.95
(slice 1, about 14.1-14.6 after the fast path's own cost), part of the memo liveness and the constructor's
header check (slice 2, 0.4-2.0) and the audits' handle checks (slice 3, 0.5-1.0). The 25-32 also counted
work that stays: the per-read range checks and the input-or-store dispatch (`lf-term-valid?`,
`lf-term-input?`, 8.0 points; ADR 0016 C8 keeps a check on every read of data from the export), the
rollback's own work (1.5) and the cache keys' liveness (`lf-fvars-live?`, 3.1, a cache rule: candidate 6).
The rows below candidate 1 keep the overlap deductions of the first version, which assumed that candidate
1 took every validity word: their own points are therefore low (candidate 6 may take up to the 3.1 above,
candidate 3 part of the 8.0), and their seconds left move only by candidate 1's change.

**Measured after slice 1** (2026-11-25, branch `kernel-validity-1` with the source of 0a76195b against main 90667b10;
`check --jobs 1 --no-manifest --resources --json` of `.claude/work/IM/init.ndjson` on Gforth 1.0
`gforth-fast`, one run each, one after the other, on a machine shared with another agent's tests). Main:
967.4 s wall, check phase 952.7 s (load average 0.6 at the start, 2.1 at the end). Branch: 839.7 s wall,
check phase 823.9 s (load 2.2 at the start, 6.2 at the end). The stamp takes 128.9 s, **13.5 points** of
the 952.7 s (measured; the design review's estimate was 14.1-14.6, and the second run had the higher load):
Init's check is now about 21.5 times Lean's 38.4 s (recorded), against 24.8. Both reports are identical
outside `measured`, `settings` and `run`: 59,349 declarations accepted, 1 not proved, fuel 654,719,715,
the same axiom sets. At `--jobs 4` the branch took 352.8 s wall (check phase 332.6 s wall, 1,074 s CPU) at
load 5.9-8.5, with the same report; it is not compared with the 287 s recorded on 2026-11-24 for main,
since the machine was loaded. The decide slice (`tests/front/decide-slice.ndjson`, 1,290 declarations)
went from 3.75 s to 3.10 s of check phase at one worker (load 1.0), with identical reports at 1 and 4
workers.

So: the algorithm changes (1, 2, 5, 6, 7) take 23-30 points, 666-732 s, **17 to 19 times Lean**; with 3
and 4 as Forth macros 557-652 s, **14.5 to 17 times**; native hashing and probe 535-630 s, 14 to 16.4
times. The first version (14-16, 11-14 and 10-13.5 times) counted 25-32 points for candidate 1. The
version before it (11-14, 10-12 and 9-11 times) added overlapping candidates: candidate
1's family counts `lf-fvars-live?` (most of candidate 6), the audit words inside candidate 2 and the memo's
hashing inside candidate 4. Inside a pass the reads and hashing that candidates 2 and 7 remove are left
out of 3 and 4, so their lower ends are the safer figures. A field read is four to six colon calls
(Gforth's `gforth-fast` costs about 1-3 ns a call and return) where C++ reads a pointer; a new node costs
458 ns (run 1; Lean: an allocation and a hash, tens of ns).

3 to 5 times Lean (115-190 s) is not in reach of local changes: it needs a term store where a node is one
block read directly (no view, base and slab layers), passes that walk once (no audit walk before the
build), and Forth words fused into fewer, larger ones on the hot paths. Even then Gforth's threaded code
stays a few times slower per primitive than compiled C++ (**estimate**). Native code pays for hashing and
the probe (about 2 points beyond the macros) and, after inlining, a node field read (a few points); nothing
else is above 3 points once the validity checks are moved.

## 11. Not measured

- Lean's and nanoda's call counts and cache hit rates: neither exposes counters, and no new run of them was
  made for counts; their shares are the recorded ones of 2026-11-02 (same export, same machine).
- Nodes visited per instantiation or substitution pass, and what a `whnf_core` hit saves.
- Allocation (`ALLOCATE`, `FREE`) on Init; p1m's were 42 a declaration (recorded, PERFORMANCE_SCAN.md).
- A front-end context of 3,300 metavariables (no test text has one).
- Timings on an idle machine for the engine runs (load in the table).

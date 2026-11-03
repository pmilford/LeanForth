# Where Lean's kernel spends its time: measurements (2026-11-02)

Measured on 2026-11-02 (local time, UTC-8) by a Claude Code subagent (PF),
for the owner's question "do we have information on where Lean is slow, or
spends most of its time?". Every figure below was **measured on this
machine** unless it is marked *published* or *estimate*. The design
conclusions are in
[SCALE_ASSESSMENT.md, "Where Lean's kernel spends its time"](../../../project/SCALE_ASSESSMENT.md#where-leans-kernel-spends-its-time-and-what-leanforth-should-do-about-it).

## Summary

- **Instantiation is the biggest single cost.** Replacing bound variables
  and universe parameters inside terms (Lean's `instantiate`,
  `instantiate_lparams`, `abstract`, all built on one generic `replace`
  walk) owns 41–42% of the run time on `Init` and `Std` and 39% on a
  Mathlib slice ([table 2](#2-time-shares-by-family)). Beta reduction
  inside `whnf_core` alone is 13–18%.
- **Infrastructure, not logic, dominates.** About a fifth of the time is
  allocation, reference counting and freeing; 21–25% is in C++
  `std::unordered_map` operations (14–16% for the per-call memo of
  `instantiate`); 7–8% is structural equality; 5–8% is looking constants up
  by name; 5.5–6.7% is destroying the per-declaration caches; 5–6% is
  re-sharing (hash-consing) every theorem before checking it.
- **The typing rules themselves are cheap.** Time *inside* the functions for
  type inference, weak-head normalisation and definitional equality, not
  counting what they call, is under 6% together.
- **A few declarations dominate.** The slowest 1% of declarations take 32%
  (`Init`), 35% (`Std`) and 35% (Mathlib slice) of the kernel time. Most of
  them are proofs produced by the `omega` arithmetic tactic, which the kernel
  checks by running tens of thousands of reduction steps; omega proofs are
  5.6% of `Init`'s declarations but 58% of its kernel time.
- **Theorems are 85–95% of the time;** definitions and inductive types are
  cheap. A theorem's proof is never unfolded, so proofs can be checked in
  parallel.
- **nanoda, the Rust checker, has the same shape of costs:** it hash-conses
  every new term, and that costs 38% of its time; instantiation and universe
  substitution 34% and 17%. It checks `Init` in 44 s on one thread (Lean's
  kernel: 39 s) and in 12 s on six threads with only 34% more memory.

## Machine, versions and inputs

| Item | Value |
| --- | --- |
| Machine | AMD Ryzen 5 7600X (6 cores, 12 threads), WSL2 kernel 6.18.54.1-microsoft-standard-WSL2, 39 GiB RAM of which about 11.5 GB held by an unrelated process; other agents' jobs ran at the same time (load average 2.7–6.3) |
| Lean | 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, binaries run directly from `.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin` (`leanchecker`, `lean`, `leanexport`, `nanoda_bin`, `lean4lean`) |
| nanoda | `nanoda_bin` 0.4.19, bundled with the toolchain |
| perf | 6.18.54.1.g26d1ceb55087, `perf_event_paranoid` = 2 (user-space samples only). This build has no libelf, libdw or libunwind, so it cannot unwind or symbolise; see [Method](#method) |
| Mathlib | tag `v4.35.0`, commit `56a005855ea17e0b0958f73ec801ae140b0a1679`, built oleans in `.tools/mathlib/mathlib4` ([earlier measurement](../mathlib-2026-11-02/README.md)) |
| `init.ndjson` (export of `Init`) | 345,690,182 B, SHA-256 `c1b2071a6d2132ace8c4711499f078aab2117d925213d5a222a1fe843a59a179` |
| `std.ndjson` (export of `Std`, includes `Init`) | 562,170,995 B, SHA-256 `bae74d695e165b8af16f34e66125de3177575e5c75d6b12e45982ea5a9afcbeb` |

The exports were produced earlier the same day with `leanexport Init` and
`leanexport Std` (lean4export 3.1.0 format). The olean runs below do not use
them; nanoda and `leanchecker --from-export` do.

Corpora:

- **`Init`**: `leanchecker --fresh Init` replays all 65,972 constants of
  Lean's `Init` into an empty environment (63,937 kernel calls; a
  constructor or recursor is not sent separately).
- **`Std`**: the same for `Std` (112,803 constants, 109,213 kernel calls,
  including `Init`).
- **Mathlib slice**: the import closure of
  `Mathlib.Algebra.Order.Field.Basic` (224,291 constants, 213,067 kernel
  calls): `Init`, part of `Std`, `Lean`, Batteries, Aesop and 38,962
  Mathlib declarations of the algebra and order hierarchy.

## Method

1. **Whole runs** with GNU `time -v` under an RSS watchdog
   ([`watch.py`](watch.py), kill limit 8 GB, never reached), through
   [`run_profiled.sh`](run_profiled.sh).
2. **Sampling profiles**: `perf record -F 499` (Init) or `-F 199` (Std,
   slice) `--call-graph dwarf,32768`, which copies 32 KiB of user stack per
   sample. Because this perf build cannot unwind,
   [`perfunwind.py`](perfunwind.py) reads `perf.data` itself and unwinds each
   sample with the DWARF call-frame rules in each library's `.eh_frame`
   (Lean's `libleanshared.so` has no frame pointers but full unwind tables
   and a symbol table), then demangles with `c++filt`. Its chains reach the
   thread entry point for 99.1% (Init), 96.9% (Std) and 98.7% (slice) of
   samples; the rest are cut off at 32 KiB and still have correct leaf
   frames.
3. **Families**: [`analyze.py`](analyze.py) classifies every frame by
   function name (its rule list is the definition of each family) and reports
   three views. *Exclusive*: the family of the innermost frame (where the CPU
   was). *Inclusive*: samples with any frame of the family on the stack,
   counted once per sample, so recursion is not double counted; inclusive
   shares overlap. *Owner*: walking outwards from the innermost frame past
   "service" frames (allocation, hash tables, structural equality, node
   construction, resource checks) to the first algorithmic frame; the owner
   column partitions the samples. [`callers.py`](callers.py) attributes a
   function's samples to its callers.
4. **Per-declaration times**: [`TimedReplay.lean`](TimedReplay.lean) is a
   copy of `Lean.Kernel.Environment.replay` (Lean 4.35.0,
   `src/lean/Lean/Replay.lean`, which `leanchecker --fresh` uses) that reads
   a monotonic clock around each kernel call (`addDeclCore`), so dependency
   ordering and bookkeeping are not counted. With `--diag` it turns on the
   kernel's own diagnostics and records how many times each constant was
   unfolded (delta) or its recursor reduced (iota) during that declaration;
   with `--dag` it counts distinct sub-terms (structural equality, the size a
   hash-consed store would hold); with `--tags` it marks proof styles by the
   constants a proof uses (heuristic: `omega` = uses `Lean.Omega.*`;
   `decide` = uses `of_decide_eq_true`; `grind` = `Lean.Grind.*`;
   `bv_decide` = `Std.Tactic.BVDecide.*`; `wf` = well-founded recursion;
   `rfl` = the proof is `Eq.refl`/`rfl` after its binders; `proj` = contains
   a projection; `bignat` = a `Nat` literal ≥ 2⁶⁴). Summaries:
   [`declstats.py`](declstats.py), [`sizestats.py`](sizestats.py),
   [`byroot.py`](byroot.py).
5. **nanoda**: timed on the `Init` export with 1 and 6 threads, and profiled
   on 1 thread the same way ([`nanoda_groups.py`](nanoda_groups.py) has its
   family rules).

Precision. A share from *n* samples has a sampling error of about
√(p(1−p)/n): ±0.3 percentage points at 20,000 samples. Wall times varied by
up to a third between runs because other agents' jobs shared the machine
(the same `Init` declarations took 38.4 s of kernel time alone and 51.1 s
inside the slice run); shares were stable across corpora. Running under
`perf` added 2.6% (Init) to the run time. perf samples only user-space
code; time in the operating system (page faults on memory-mapped oleans,
0.4–2.7 s of system time per run) is not in the shares.

## 1. Whole runs

| Run | Wall | User CPU | Peak RSS |
| --- | ---: | ---: | ---: |
| `leanchecker --fresh Init` | 39.5 s | 39.0 s | 529 MB |
| `leanchecker --fresh Init` under perf (499 Hz) | 40.5 s | 39.9 s | 654 MB (the largest process, perf; leanchecker 522 MB) |
| `leanchecker --from-export init.ndjson` (same input as nanoda; includes Lean's NDJSON parser) | 51.7 s | 51.1 s | 611 MB |
| `leanchecker --fresh Std` under perf (199 Hz) | 71.9 s | 71.1 s | 927 MB |
| `leanchecker --fresh Mathlib.Algebra.Group.Basic` | 59.2 s | 56.5 s | 1.15 GB |
| `leanchecker --fresh Mathlib.Algebra.Order.Field.Basic` (the slice) | 84.1 s | 81.6 s | 1.60 GB |
| the slice under perf (199 Hz) | 104.9 s | 102.7 s | 1.60 GB |
| `nanoda_bin`, `init.ndjson`, 1 thread | 44.3 s | 43.7 s | 364 MB |
| `nanoda_bin`, `init.ndjson`, 6 threads | 11.9 s | 45.4 s (385% CPU) | 487 MB |
| `TimedReplay.lean Init` (interpreted driver; kernel calls 37.7 s of it) | 45.1 s | 43.8 s | 2.05 GB |
| `TimedReplay.lean Std --diag --dag --tags` (kernel calls 68.9 s) | 109.9 s | 104.4 s | 2.50 GB |
| `TimedReplay.lean` slice `--diag --dag --tags` (kernel calls 102.5 s) | 185.8 s | 177.4 s | 3.52 GB |

`TimedReplay` uses more memory than `leanchecker` because the interpreter
also loads `Lean` for the script itself. Loading the oleans
(`importModules`) took 0.5–0.9 s for `Init`, 3.7 s for `Std` and 6.4 s for
the slice inside `TimedReplay`; perf sees only about 0.1 s (Init) and 0.2 s
(Std) of it as user-space work in `leanchecker`, because the files are
memory-mapped.

Earlier the same day ([SCALE_ASSESSMENT.md](../../../project/SCALE_ASSESSMENT.md)):
`leanchecker Init` without `--fresh`, which checks each module in its own
task with its own imports, took 21.2 s wall, 98 s CPU and 3.4 GB.

## 2. Time shares by family

Shares of all perf samples of `leanchecker --fresh`. Exclusive = where the
CPU was; inclusive = on the stack (overlapping); owner = nearest
algorithmic caller (a partition, sums to 100%).

Regions (by the frames on the stack):

| Region | Init | Std | Slice |
| --- | ---: | ---: | ---: |
| Kernel (inside `lean_add_decl`) | 91.0% | 90.1% | 86.2% |
| `leanchecker`'s replay bookkeeping (dependency order, `getUsedConstants`, name sets) | 7.5% | 8.5% | 10.6% |
| Start-up, olean loading | 0.4% | 0.4% | 0.7% |
| Other (exit, unknown) | 1.0% | 1.1% | 2.6% |

Families, the owner's requested list first:

| Family | Init excl. | Init incl. | Init owner | Std excl. | Std incl. | Std owner | Slice excl. | Slice incl. | Slice owner |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Loading oleans and the environment (start-up) | 0.1% | – | 0.4% | 0.1% | – | 0.3% | 0.2% | – | 0.6% |
| Type inference (`infer_*`, `check`, `ensure_*`) | 1.7% | 77.3% | 8.6% | 1.8% | 74.0% | 9.1% | 2.2% | 71.5% | 10.0% |
| Weak-head normalisation (`whnf`, `whnf_core`, delta unfolding, recursor and projection reduction) | 3.3% | 46.0% | 13.0% | 2.5% | 40.4% | 10.5% | 2.4% | 36.2% | 9.9% |
| Definitional equality (`is_def_eq*`, lazy delta, eta, proof irrelevance) | 0.8% | 54.9% | 6.3% | 0.5% | 49.4% | 6.1% | 0.6% | 45.4% | 5.9% |
| Instantiation and abstraction (`instantiate`, `instantiate_rev`, `instantiate_lparams`, `abstract`, lift/lower, the shared `replace` walk) | 15.2% | 42.9% | 41.3% | 15.7% | 43.6% | 41.6% | 14.6% | 41.0% | 38.9% |
| Level operations | 1.3% | 2.4% | 1.9% | 1.6% | 3.0% | 2.5% | 1.8% | 3.1% | 2.6% |
| Hash tables (C++ `unordered_map`: instantiate memo, type-checker caches) | 24.7% | 30.6% | – | 23.9% | 29.8% | – | 21.3% | 27.2% | – |
| Re-sharing each theorem (`sharecommon`, hash-consing on input) | 2.5% | 5.5% | 5.5% | 2.6% | 5.6% | 5.6% | 2.2% | 5.1% | 5.1% |
| Structural equality and hashing of terms and names | 7.0% | 9.6% | – | 7.7% | 10.5% | – | 8.4% | 10.7% | – |
| Nat and String literal arithmetic (`reduce_nat`, GMP) | 0.2% | 4.4% | 0.6% | 0.2% | 4.6% | 0.6% | 0.2% | 3.3% | 0.6% |
| Memory: allocation | 7.5% | 7.8% | – | 7.8% | 8.2% | – | 9.4% | 9.7% | – |
| Memory: freeing and reference counting | 14.0% | 14.2% | – | 13.9% | 14.3% | – | 13.4% | 13.7% | – |
| Other: constant lookup by name | 5.1% | 11.5% | 7.4% | 5.2% | 11.6% | 7.4% | 5.6% | 12.3% | 7.7% |
| Other: building term nodes (`mk_app`, `update_*`, node data) | 7.5% | 12.9% | – | 6.9% | 13.4% | – | 6.5% | 13.4% | – |
| Other: destroying per-declaration caches (`~type_checker`) | 0.4% | 6.5% | 6.5% | 0.4% | 6.7% | 6.7% | 0.3% | 5.5% | 5.5% |
| Other: resource checks (stack, memory, heartbeats) | 2.3% | 2.3% | – | 1.9% | 1.9% | – | 1.9% | 1.9% | – |
| Other: replay bookkeeping | 3.8% | – | 7.6% | 4.1% | – | 8.7% | 5.1% | – | 10.8% |
| Other: rest | 2.8% | – | 1.0% | 3.2% | – | 1.0% | 4.0% | – | 2.6% |

Exclusive hash-table time by caller: the instantiate memo
(`replace_rec_fn`'s per-call `unordered_map` keyed by node address and
binder offset) 16.2% (Init), 15.7% (Std) and 14.1% (slice); the type
checker's caches (infer, whnf, whnf_core, definitional-equality success and
failure) 5.1%, 4.8% and 4.5%; `sharecommon`'s tables 1.8%, 1.7% and 1.5%;
structural equality's visited-pairs table 1.5%, 1.6% and 1.2%.

**Who pays for instantiation** (share of all samples; outermost
instantiation call and its caller):

| Caller → operation | Init | Std | Slice |
| --- | ---: | ---: | ---: |
| `whnf_core` → `instantiate` (beta reduction) | 17.9% | 15.4% | 13.1% |
| `infer_app` → `instantiate` (function type applied to arguments) | 7.2% | 8.0% | 7.4% |
| `reduce_recursor` → `instantiate_lparams` (iota: recursor rule at the call's universe levels) | 5.3% | 4.0% | 3.9% |
| `unfold_definition` → `instantiate_value_lparams` (delta: definition body at the call's levels) | 3.8% | 4.7% | 4.1% |
| `infer_constant` → `instantiate_type_lparams` (a constant's type at the call's levels) | 3.5% | 5.1% | 6.0% |
| `infer_lambda`/`infer_pi`/`is_def_eq_binding` → `instantiate_rev` (open a binder with a free variable) | 3.2% | 3.3% | 3.7% |
| `mk_binding` → `abstract` (close a binder again) | 1.3% | 2.0% | 1.6% |

**Where `whnf_core` is called from:** lazy delta reduction
(`lazy_delta_reduction_step`) 22.6% / 20.0% / 18.0% of all samples, the
start of `is_def_eq_core` 17.8% / 14.5% / 13.0% (Init / Std / slice).
**Constant lookups** come from `reduce_recursor` (2.9% / 3.0% / 3.0%), lazy
delta's `is_delta` (2.2% / 1.7% / 1.4%) and `infer_constant` (1.2% / 1.6% /
2.1%). `reduce_nat` is called from `whnf` (4.1% / 4.2% / 2.9%); GMP itself
is 0.2%.

## 3. Per-declaration times and the slowest declarations

From `TimedReplay.lean` (kernel time only; `--diag` adds about 5%).

| Measure | Init | Std | Slice | Mathlib part of the slice |
| --- | ---: | ---: | ---: | ---: |
| Declarations (kernel calls) | 63,937 | 109,213 | 213,067 | 38,962 |
| Kernel time | 38.4 s | 68.9 s | 102.5 s | 15.1 s |
| Median / mean per declaration | 120 / 600 µs | 151 / 631 µs | 124 / 481 µs | 175 / 388 µs |
| Share of time in the slowest 100 declarations / 1% / 10% | 12.8% / 32.0% / 75.6% | 13.9% / 35.1% / 71.4% | 7.8% / 34.6% / 69.2% | 15.3% / 24.7% / 53.0% |
| Slowest single declaration | 0.29 s | 1.52 s | 0.43 s | 0.11 s |
| Theorems' share of time | 95.2% | 94.8% | 85.2% | 82.0% |
| Correlation of log time with log distinct nodes | 0.91 | 0.90 | 0.90 | 0.87 |
| Kernel time per distinct node | 3.0 µs | 3.3 µs | 3.3 µs | 2.9 µs |
| Delta and iota steps recorded | 8.8 M | 11.6 M | 13.1 M | 1.5 M |

Time per distinct node grows with declaration size: 1.8 µs below 100
distinct nodes, 2.8 µs for 100–1,000, 3.9 µs for 1,000–10,000 and 5.2 µs
above 10,000 (Init; Std 2.4 / 2.9 / 4.0 / 6.7 µs).

**By proof style** (tags overlap; share of kernel time, and how many of
the slowest 1% carry the tag):

| Tag | Init decls | Init time | Std time | Slice time | Mathlib part | In slowest 1% (Init / Std / slice) |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| `omega` | 3,601 (5.6%) | 57.6% | 44.6% | 34.3% | 1.8% | 541 / 839 / 1,538 |
| `decide` (mostly inside omega proofs) | 3,956 | 58.7% | 47.1% | 35.6% | 2.0% | 552 / 893 / 1,568 |
| `grind` | 2,833 | 4.2% | 2.5% | 7.9% | 21.9% | 31 / 38 / 244 |
| well-founded recursion (`wf`) | 301 | 2.7% | 8.9% | 2.5% | 0.5% | 35 / 145 / 93 |
| about `bv_decide`'s bit-blaster | 0 | – | 8.8% | – | – | – / 127 / – |
| `rfl` proofs | 6,516 | 2.7% | 2.9% | 4.0% | 9.6% | 0 / 1 / 1 |
| `bignat` (literal ≥ 2⁶⁴) | 132 | 0.2% | 0.1% | 0.2% | – | 0 / 0 / 3 |
| none of these | 48,391 | 30.9% | 39.8% | 48.1% | 63.6% | 45 / 94 / 235 |

**The slowest declarations** (full lists: `declstats.py` on the TSV files):

| Declaration | Time | Distinct nodes | Delta/iota steps (most frequent) | Kind |
| --- | ---: | ---: | --- | --- |
| `Std.Tactic.BVDecide.BVExpr.bitblast.goCache_Inv_of_Inv._mutual` | 1,524 ms | 79,209 | 123,490 (`PSigma.casesOn` 11,788) | correctness of the bit-blaster's cache, by well-founded recursion, omega side goals |
| `Std.Tactic.BVDecide.BVExpr.bitblast.goCache._mutual.eq_def` | 727 ms | 12,756 | 68,656 | equation lemma of a well-founded definition: proved by unfolding it |
| `_private.Std.Data.DTreeMap.Internal.Balancing…adjust_left._proof_1_1` | 431 ms | 6,833 | 15,772 (`List.rec`) | omega |
| `_private.Init.Data.Vector.Extract…Vector.extract_append._proof_1` | 285 ms | 26,959 | 58,134 (`List.rec` 10,128) | omega |
| `_private.Init.Data.Array.Extract…Array.extract_append._proof_1_1` | 209 ms | 26,770 | 58,063 | omega |
| `Lean.Grind.Ring.OfSemiring.mul_helper` | 66 ms | 4,390 | 18,897 (`List.rec`) | grind ring normalisation by reflection |
| `ByteArray.utf8DecodeChar?_utf8EncodeChar_append` | 57 ms | 687 | 25,392 (`Nat.rec` 3,792) | small term, deep computation |
| `_private.Mathlib.Algebra.Group.Nat.Even…Nat.even_add._proof_1_1` | 106 ms | 2,661 | 14,520 (`Int.Internal.Linear.Poly.rec`) | grind linear-arithmetic certificate (slowest Mathlib declaration of the slice) |

What makes declarations slow, in order of measured kernel time:

1. **Proof by computation inside the kernel.** `omega`, `grind`'s
   arithmetic and ring certificates, and `decide` produce small proofs that
   the kernel accepts only after evaluating functions on lists, integers and
   polynomials: tens of thousands of delta and iota steps per proof, each
   followed by beta reduction (instantiate). In `Init` these are 58% of the
   time.
2. **Well-founded recursion.** Equation lemmas (`eq_def`) and proofs about
   functions defined by well-founded recursion unfold `WellFounded.fix`
   through `Acc.rec` and `PSigma` encodings; 9% of `Std`.
3. **Size.** Outside those styles, time follows the number of distinct
   sub-terms (log-log correlation 0.87–0.91), at about 2–7 µs per node.
4. **Not slow:** big literals (`bignat` 0.1–0.2%), GMP arithmetic (0.2%
   exclusive), definitions (5% of `Init`), inductive types (0.3–0.7%), and
   `rfl` proofs on average (160–360 µs).

## 4. Independent checkers

**nanoda 0.4.19** (Rust; same export as `leanchecker --from-export`): 59,348
declarations of `Init` accepted. Profile of the 1-thread run (23,484
samples; exclusive / inclusive / owner):

| Family | Excl. | Incl. | Owner |
| --- | ---: | ---: | ---: |
| Parsing the NDJSON export | 6.2% | 9.1% | 9.1% |
| Hash-consing each new term (`alloc_expr`, `IndexMap` insert and look-up) | 38.2% | 42.4% | – |
| Instantiation and abstraction | 9.2% | 33.7% | 33.7% |
| Universe-level substitution in terms | 4.7% | 17.3% | 17.3% |
| Weak-head normalisation | 5.9% | 63.4% | 28.7% |
| Definitional equality | 0.6% | 68.5% | 2.4% |
| Type inference | 2.2% | 87.7% | 4.2% |
| Other hash tables (caches) | 10.1% | 11.2% | – |
| Building term nodes (`mk_app`, spines) | 12.2% | 51.8% | – |
| Memory (malloc, vectors) | 7.6% | 8.0% | – |
| Nat literal reduction | 0.4% | 6.1% | 1.6% |

From nanoda's source (read for this comparison, not measured):
expressions live in a global read-only DAG built from the export plus a
temporary DAG per declaration, dropped after it; a 32-bit pointer's top bit
says which. Every node stores its hash, loose-bound-variable count and a
has-free-variables flag; every constructor first looks the node up in the
export DAG and then inserts it into the temporary one (two hash look-ups).
Caches: infer (checked and unchecked), whnf, whnf without unfolding,
definitional-equality success and failure, instantiation and abstraction
memos keyed by (node, offset), and universe-substitution memos keyed by
(node, level lists). Workers share the export DAG read-only.

Comparison on `Init` (same machine, same day):

| Checker | Wall | CPU | Peak RSS | Notes |
| --- | ---: | ---: | ---: | --- |
| Lean kernel, `leanchecker --fresh Init` (oleans) | 39.5 s | 39.0 s | 529 MB | 1 thread; 91% in the kernel |
| Lean kernel, `leanchecker --from-export` | 51.7 s | 51.1 s | 611 MB | adds Lean's NDJSON parser |
| Lean kernel, `leanchecker Init` (one task per module) | 21.2 s | 98 s | 3.4 GB | earlier measurement; every task loads its own imports |
| nanoda, 1 thread | 44.3 s | 43.7 s | 364 MB | 9% parsing |
| nanoda, 6 threads | 11.9 s | 45.4 s | 487 MB | 3.7× faster, +34% memory |

**lean4lean** could not be run: the bundled binary rejects the 4.35.0
oleans ("incompatible header") and has no `--from-export` mode in this
build. The arena's published figure for Mathlib is 38.8 min and 11.6 GB
(*published*, in SCALE_ASSESSMENT.md §2).

**nanoda on `Std`** was not re-run: the earlier run on the full `Std` export
passed 19 GB ([SCALE_ASSESSMENT.md](../../../project/SCALE_ASSESSMENT.md)),
above this task's 8 GB limit. Two cheap probes of the cause:

- The import closure of `Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Expr`
  (exported with `leanexport`, 459,698,858 B; it contains `Std`'s slowest
  and largest declaration) passed: 75,495 declarations in 52.9 s, 547 MB,
  1 thread. That declaration is not the trigger.
- Switching nanoda's String extension off is not possible: nanoda refuses an
  export that contains string literals without it.

The trigger stays unknown; the arena reports 58 s and 709 MB for nanoda on
`Std` (*published*), probably with a different nanoda version.

## 5. What was not measured

- **Cache hit rates.** Lean's kernel exposes no counters for its caches, and
  this perf build cannot place probes, so hit rates are unknown. The time
  spent *in* the caches is measured (about 5% for the type checker's caches,
  16% for the instantiate memo). LeanForth should count hits and misses
  itself (plan task 6.5.1).
- **A full Mathlib profile.** The slice is 31% of Mathlib's 729,263
  constants by count, but only 38,962 of its declarations are Mathlib's own.
- **Kernel-mode time** (page faults on memory-mapped oleans): not sampled.

## Reproduction

All commands ran from this folder with `OUT` pointing at a scratch folder;
`run_profiled.sh NAME LIMIT_MIB [--perf HZ] [--mathlib] -- CMD`:

```sh
run_profiled.sh init-fresh 8000 -- leanchecker --fresh Init
run_profiled.sh init-fresh-perf 8000 --perf 499 -- leanchecker --fresh Init
run_profiled.sh std-fresh-perf 8000 --perf 199 -- leanchecker --fresh Std
run_profiled.sh ml-agb 8000 --mathlib -- leanchecker --fresh Mathlib.Algebra.Group.Basic
run_profiled.sh ml-aofb 8000 --mathlib -- leanchecker --fresh Mathlib.Algebra.Order.Field.Basic
run_profiled.sh ml-aofb-perf 8000 --perf 199 --mathlib -- leanchecker --fresh Mathlib.Algebra.Order.Field.Basic
run_profiled.sh lc-init-export 8000 -- leanchecker --from-export init.ndjson
run_profiled.sh nanoda-init-1 8000 -- nanoda_bin nanoda-init-1.json      # num_threads 1
run_profiled.sh nanoda-init-6 8000 -- nanoda_bin nanoda-init-6.json      # num_threads 6
run_profiled.sh nanoda-perf 8000 --perf 499 -- nanoda_bin nanoda-init-1.json
run_profiled.sh export-bv 8000 -- leanexport Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Expr
run_profiled.sh nanoda-bv 8000 -- nanoda_bin nanoda-bv-1.json            # export-bv.stdout, 1 thread
run_profiled.sh init-timed 8000 -- lean --run TimedReplay.lean Init init-decls.tsv
run_profiled.sh init-all 8000 -- lean --run TimedReplay.lean Init init-decls-all.tsv --diag --dag --tags
run_profiled.sh std-all 8000 -- lean --run TimedReplay.lean Std std-decls-all.tsv --diag --dag --tags
run_profiled.sh ml-all 8000 --mathlib -- lean --run TimedReplay.lean Mathlib.Algebra.Order.Field.Basic ml-decls-all.tsv --diag --dag --tags
python3 -I perfunwind.py out/init-fresh-perf.perf.data init.stacks   # 3.5 min, 1.1 GB
python3 -I analyze.py init.stacks --detail
python3 -I callers.py init.stacks '^lean::type_checker::whnf_core$'
python3 -I declstats.py init-decls-all.tsv 40 --modules
python3 -I sizestats.py init-decls-all.tsv
python3 -I byroot.py ml-decls-all.tsv
python3 -I nanoda_groups.py nanoda.stacks
```

nanoda's configuration: `{"export_file_path": …, "use_stdin": false,
"permitted_axioms": ["propext","Classical.choice","Quot.sound"],
"unpermitted_axiom_hard_error": false, "nat_extension": true,
"string_extension": true, "num_threads": 1 or 6,
"print_success_message": true}`.

The perf data (0.45–0.74 GB per run), unwound stacks and per-declaration
TSV files are not in git; they stayed in the measuring session's scratch
folder.

## Files

- [`run_profiled.sh`](run_profiled.sh), [`watch.py`](watch.py): timing,
  watchdog and perf wrapper.
- [`perfunwind.py`](perfunwind.py): `perf.data` reader, `.eh_frame`
  unwinder and symboliser.
- [`analyze.py`](analyze.py), [`topsyms.py`](topsyms.py),
  [`callers.py`](callers.py), [`nanoda_groups.py`](nanoda_groups.py):
  profile summaries.
- [`TimedReplay.lean`](TimedReplay.lean): per-declaration kernel timing.
- [`declstats.py`](declstats.py), [`sizestats.py`](sizestats.py),
  [`byroot.py`](byroot.py): per-declaration summaries.

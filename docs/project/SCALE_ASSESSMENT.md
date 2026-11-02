# LeanForth at Mathlib scale: memory and CPU assessment

*Assessment of 2026-11-02 by a Claude Code agent, for the draft plan's
scale workstream (W7 in [PLAN_DRAFT.md](PLAN_DRAFT.md)). Not a decision.*

Prepared 2026-11-02 for planning. Read-only with respect to the repository: the
code was read from the working tree during an ongoing `src/` refactor, and
measurements used copies in the scratchpad. Confidence labels:
**measured** (run here today), **published, verified** (I read the primary
page), **published, reported** (read by a research subagent; I did not
re-open it), and **estimate** (my own reasoning, with the basis given).

**Measured since (2026-11-02, later):** the pinned Mathlib for Lean 4.35.0
(tag `v4.35.0`, commit `56a0058`) was exported and counted on this machine
([measurements](../development/measurements/mathlib-2026-11-02/README.md)):
6.26 GB, 110.9 M lines, **729,263 constants**, 105.9 M expression nodes,
4.24 M names, 47,805 levels; export 6.6 minutes and 13.8 GB peak memory;
1.03 GB with `zstd -3`. Corrections to the estimates below: names are 4.2 M,
not 5–6 M; **up to 30 universe arguments** occur (1,831 declarations exceed
LeanForth's limit of 8); expression depth reaches 1,221; the largest
declaration has 95,123 distinct nodes and one has a tree size of 1.2×10¹⁴,
so walking shared nodes once per path is impossible at Mathlib scale.

## Summary for the owner

Full Mathlib is big, but within reach of an ordinary workstation **if the
checker is built the way the existing fast checkers are built**. A complete
Lean export of Mathlib with all its dependencies is a 5.8 GB file of about
110 million records, almost all of them expression nodes, describing about
719,000 declarations. Today's independent checkers need between 2.3 and 12 GB
of memory for it. Lean's own kernel takes roughly 30–45 minutes on one core,
and the fastest new checkers take minutes. LeanForth's current code cannot
check even Lean's basic `Init` library, for three reasons:

- Every table holds 64 entries. More than half of `Init`'s declarations are
  bigger than that on their own.
- Shared sub-terms are re-walked and re-copied once for every path that leads
  to them. That is 63 times the necessary work over `Init` and 194 times over
  `Std`, and a single `Std` declaration would need 2.6 billion visits.
- Names are found by scanning every entry, and every operation re-audits whole
  tables.

None of this is a design dead end. The record layout, the outcome codes and
the roll-back discipline are the right shape. The fix is a known recipe:

- growable tables;
- hash tables that store each term once;
- per-node caches;
- a streaming reader written in Forth;
- one context record per worker thread.

Projected cost for the full library with that recipe:

- **Memory:** about 3–6 GB, plus about 1 GB per worker.
- **CPU:** roughly 1.5–7.5 CPU-hours, or about 15–75 minutes on this machine
  (Ryzen 5 7600X, 6 cores and 12 threads).

The CPU figure is a low-confidence estimate.

**Disk is this machine's binding limit, not memory or CPU.** Only about
13 GB of disk is free.

- **Fits in about 10 GB:**
  - every rung up to `Std` and Lean, since their compiled files are already
    in the installed toolchain;
  - a Mathlib slice;
  - possibly all of Mathlib, if its compiled files fit (about 4.5 GB
    reported in early 2025, more now) and the export is streamed or kept
    compressed rather than written out as 5.8 GB of text. I recommend climbing a ladder:
`Init` → `Std` → Lean and Batteries → a Mathlib slice → all of Mathlib. Each
rung adds one order of magnitude. The first rung already needs most of
Lean's kernel features: inductive types, recursors, quotients, projections,
big-number literals and `let`.

## 1. How big is Mathlib?

| Item | Figure | Source, date, version | Confidence |
| --- | --- | --- | --- |
| Mathlib definitions / theorems | 140,100 / 292,326 (Mathlib only; excludes auto-generated equation lemmas and abstracted proofs) | https://leanprover-community.github.io/mathlib_stats.html (undated, fetched 2026-11-02) | published, verified |
| Mathlib modules | 7,563 modules, 308,129 declarations (Feb 2026, commit 534cf0b) | arXiv 2604.24797; https://mathlib-network.pages.dev/ | published, reported |
| Mathlib lines | 2 million lines of code (28 Oct 2025); cloc: 7,208 files, about 1.25M code lines | Zulip archive, topic "2 million", 2025-11-03 | published, reported |
| **Full kernel export** (Mathlib, Lean, Std, Batteries and other dependencies) | **5.8 GB, 109.8 M NDJSON lines**, lean4export 3.1.0, Lean 4.34.1, Mathlib `d13f23b` | https://arena.lean-lang.org/test/mathlib/ | published, verified |
| Declarations in that export | 718,574 accepted by the official checker | https://arena.lean-lang.org/checker/official/ | published, reported |
| Names / levels / expressions in the Mathlib export | Not published. Estimate: about 103 M expressions, 5–6 M names, levels in the tens of thousands, 0.7 M declaration records | Applies the measured `Init`/`Std` record mix below (94% expressions, 5% names) to 109.8 M lines | estimate, medium |
| Bigger project for scale | FLT plus Mathlib: 1,052,234 constants; export 37.8 GB; exporting took 44 min with 59 GB peak memory | https://github.com/Kha/fermats-last-theorem/releases (Lean 4.33.1) | published, reported |

**Measured here** with the pinned toolchain (`leanexport` shipped in Lean 4.35.0)
on the two smallest rungs. Expression nodes are counted after the exporter's
structural sharing.

| Export | Constants | Expression nodes | Names | Levels | Bytes | Export run |
| --- | --- | --- | --- | --- | --- | --- |
| `Init` | 59,349 (15,143 defs, 41,920 thms, 604 inductive types, 824 constructors, 606 recursors, 244 opaque, 4 axioms, 4 quot) | 6,099,054 (85% `app`, 9% `lam`, 5% `forallE`; `letE` 11,259; `proj` 3,608; literals 2,099) | 295,431 | 577 | 345.7 MB | 12.7 s, 1.0 GB RSS |
| `Std` (includes `Init`) | 99,619 | 9,539,642 | 556,077 | 929 | 562.2 MB | 21.3 s, 1.4 GB RSS |

Per declaration, measured on `Init` and `Std`:

- Distinct nodes reachable: median 78–90, 99th percentile about 1,900, maximum
  79,001.
- Universe parameters: at most 7; constants carry at most 7 universe
  arguments.
- `natVal` literals reach 20 digits, such as 2^64, which does not fit in a
  64-bit cell.

## 2. What existing checkers need

| Checker (corpus) | Time | Peak memory | Cores | Source | Confidence |
| --- | --- | --- | --- | --- | --- |
| Lean official kernel (Mathlib export) | 32.3 min virtual CPU (instructions ÷ 6 Ginstr/s) | 9.9 GB | 1 | arena Mathlib page | published, verified |
| nanoda, Rust (Mathlib) | 15.2 min virtual; 5.8 min wall | 6.0 GB | 4 threads | arena | verified time and memory; reported threads |
| kefir, Rust, streaming and freeing (Mathlib) | 6.8 min | **2.3 GB** | 1 | arena | verified time and memory; reported thread count |
| nano-lean, Rust, hash-consed de Bruijn (Mathlib) | 1.3 min virtual; 61.7 s wall | 5.2 GB | parallel | arena | verified time and memory; reported rest |
| lean4lean (Mathlib) | 38.8 min | 11.6 GB | 1 | arena | published, verified |
| arena "parse-only" baseline (Mathlib) | 5.1 min | 9.9 GB | – | arena | published, verified |
| lean4checker vs lean4lean (Mathlib with Batteries and Lean, 2024 snapshot) | 44.54 min vs 58.79 min | – | single-threaded, i7-1255U | arXiv 2403.14064 v3, Fig. 2 | published, verified |
| Mathlib daily CI, `leanchecker --fresh Mathlib` | 34 min 52 s | ≤ 16 GB runner | 4-CPU runner | mathlib4 `daily.yml`, run 2026-11-02 | published, reported |
| nanoda (FLT, 1.05 M constants) | 24 min | 45.5 GiB | 16 threads | Kha FLT release | published, reported |
| **Local: `leanchecker --fresh Init`** | 38.3 s | 528 MB | 1 | this machine | measured |
| **Local: `leanchecker Init`** (parallel per module) | 21.2 s wall, 98 s CPU | **3.4 GB** | about 6.5 | this machine | measured |
| **Local: nanoda 0.4.19 on `Init` export** | 38.4 s | 364 MB, about 60 B per expression node all-in | 1 | this machine | measured |
| Arena `Init` / `Std`, official | 1.1 min, 566 MB / 1.9 min, 932 MB | – | 1 | arena init and std pages | published, verified |

Notes on these runs:

- **Per-module parallelism multiplies memory.** Lean's per-module replay was
  1.8 times faster than the fresh replay but used 6.4 times the memory,
  because every task loads its imports.
- **A local nanoda run on `Std` failed.** With my configuration (Nat and
  String extensions on) it ran past 6.7 minutes and 19 GB RSS, and I stopped
  it to protect the machine. The arena reports 58 s and 709 MB for nanoda on
  `Std`. I did not investigate the cause. It is a reminder that a few heavy
  declarations dominate the tail.
- **The pinned toolchain bundles other checkers.** It also ships `lean4lean`,
  `con-leche` and `con-ron`. Run without arguments, `lean4lean` printed
  "incompatible header" for several `.olean` files; I did not investigate.

## 3. Per-object memory in LeanForth today and projected to Mathlib

**Method.** I measured how many dictionary bytes each unit of capacity costs.
`src/` was copied, one capacity constant at a time was raised by 1,024, and
`gforth` loaded `main.fs` (64-bit cells). The measured costs:

| Object | Cells per unit (bytes) | Of which data | Of which scratch sized by capacity |
| --- | --- | --- | --- |
| Term node | **48 (384 B)** | 7: 3-cell record, 1 identity, 3 side stamps (`lf-cterm-stamps`, `lf-hsort-*-identities`) | 41: per-module frame arrays and work stacks (shift 4, instantiate 6, beta 4, compare 6, convert 6, infer 7, six worklists 8) |
| Level node | 64 (512 B) | 4 | 28, plus 32 from the signature-formals matrix (`lf-msp-formals`, signatures × level capacity) |
| Name entry | 5 (40 B) | 5, plus string bytes (measured average 4.6 B per component) | – |
| Constant reference | 20 (160 B) | fixed room for 8 universe arguments | – |
| Signature entry | 68 (544 B) | 4 | 64 (one row of `lf-msp-formals`) |

**Projected to Mathlib** at about 103 M expressions and about 5.5 M names
(estimate):

- **Current layout with every capacity scaled up:** about 40 GB for terms,
  of which 5.8 GB is data and the rest is scratch. Names add 0.25 GB and
  constant references about 0.16 GB. The signature matrix grows as
  *declarations × levels*: 718 k × even 10 k cells is about 57 GB. It must
  become variable-length.
- **Loading alone is not the cost.** The figures above assume the exporter's
  sharing is kept, which `import/load.fs` does. The blow-up comes from
  **generated** terms: shift, instantiate, beta and level substitution copy a
  node once per path. One full traversal of every declaration is 7.6×10⁸
  node visits in `Init` against 1.2×10⁷ distinct nodes, and 3.9×10⁹ against
  2.0×10⁷ in `Std` (measured).
- **Without sharing**, terms stored as trees would cost 43 GB of data for
  `Init` alone and 218 GB for `Std` at 56 B per node. Mathlib's figure is
  unknown and larger.
- **Proposed compact layout, hash-consed** (estimate):
  - Each node gets a 24 B record (tag and flags, two 32-bit children, a
    32-bit hash, loose-bound-variable range and depth) plus about 6 B of
    hash slot. That is about 30 B per node, or **about 3.1 GB**.
  - Names, declarations and literals add about 0.3 GB.
  - Using plain 64-bit cells for every field instead doubles this to about
    6 GB.
  - This brackets the published checkers: kefir 2.3 GB, nano-lean 5.2 GB,
    nanoda 6.0 GB, official 9.9 GB.
  - The immutable tier needs no per-node identities, which saves 4 cells,
    or about 3.3 GB at Mathlib scale.

## 4. What fails or blows up at scale, and what is already right

**Fixed capacities.** 64 terms, levels and names, 32 references and 32
signatures, at most 8 universe arguments, and a 2,048-byte name pool.

- Measured: 56% of `Init` declarations (32,692) and 62% of `Std` declarations
  (59,800) exceed 64 distinct nodes on their own.
- The name pool needs about 1.4 MB for `Init` and about 2.5 MB for `Std`;
  Mathlib likely needs about 25–30 MB (estimate).
- Seven universe arguments is the maximum seen in `Init` and `Std`. Mathlib
  has up to 30 (measured later the same day), so the fixed limit of 8 must
  become variable-length.
- Sort payloads and `bvar` indices are plain cells, but literals need bignums.

**Linear and whole-table work on every call.** Measured from the code; each
cost below is per call.

- **Name interning** (`lf-name-find-str`) scans every entry, and
  `lf-name-storage-valid?` audits the whole table on every intern *and* on
  every constant-reference check (`lf-cref-name-valid?`). Interning about
  5.5 M names would take on the order of 10¹³ entry visits, which is days of
  work. Each constant visit would also audit millions of names.
- **Level substitution** (`lf-mls-audit`) erases a capacity-sized `seen`
  array, and `lf-mls-build` loops over every index from 0 to the root.
  `level-substitute.fs` erases five capacity-sized arrays. At 10⁸ nodes, each
  specialisation of a constant would touch gigabytes.
- **Every public operation re-audits its whole input graphs**
  (`lf-cterm-check` in shift, instantiate, beta, compare and convert), and it
  does so per path, inside recursion:
  - `convert` calls `beta` (a full audit) at every node;
  - `infer` calls `convert` (two full audits) at every application node.
  This is quadratic on top of the per-path blow-up.

**Per-path visits of shared nodes.** Fuel is charged per occurrence, and
outputs are rebuilt per occurrence with no `(node, offset)` memo. Measured
ratio of tree size to DAG size:

| Corpus | Median | 99th percentile | Total | Maximum for one declaration |
| --- | --- | --- | --- | --- |
| `Init` | 2.6 | 90 | 63× | 8,621× |
| `Std` | 2.35 | 70 | 194× | 3.9×10⁵× |

The largest `Std` declaration needs 2.6×10⁹ visits for one pass, and
Mathlib's tail is unknown but likely worse.

- **Instantiate and shift** have no loose-bound-variable cache to skip closed
  subterms. Bound variables in `infer` are shifted with fresh allocation at
  every occurrence.
- **Compare and convert** have no pointer-equality fast path: identical nodes,
  even identical names, are compared component by component.

**Missing caches.** There are no `whnf`, infer or definitional-equality
success and failure caches. Lean's kernel keeps all of them
(`m_infer_type[2]`, `m_whnf_core`, `m_whnf`, `m_unfold`, `m_success`,
`m_failure` in `type_checker.h`; published, reported). Bailey's checker
guide calls failure caching "performance critical".

**Global single-instance state.** About 225 globals (roadmap Q10 baseline)
and every scratch array are module-level `variable` and `create` words, so
there is one checker per Gforth image and no thread safety.

**Fuel semantics.** One budget, charged per occurrence, means the budget a
valid declaration needs grows with tree size, so practical budgets would
report "exhausted" widely. Once caches exist, budgets must charge only real
work and stay per declaration, so outcomes do not depend on checking order.
Lean replaced its union-find definitional-equality cache because results
depended on hash collisions (lean4 PR 14806; published, reported).

**Python decoding step.** `ndjson_preview.py` is bounded to 1 MiB, 64
expressions and 32-bit numbers. It builds whole in-memory objects; json
parsing alone measured about 29 MB/s, which is about 3.5 minutes for Mathlib,
plus tens of GB of Python objects (estimate). It is also outside Forth, and
the plan requires the semantics to be checked in Forth. Eleven test readers
duplicate its framing.

**Missing kernel features that dominate cost.**

- Inductive types, recursors, quotients, projections, `let` and lazy delta
  unfolding with height hints are all absent.
- Nat and String literal kernel extensions are absent. They need a bignum
  library, which is trusted code.

**Already the right shape:**

- Index-based nodes whose children precede their parents. This matches the
  export's topological order, allows 32-bit handles, and allows one-pass
  validation on import.
- Names stored once by prefix.
- The `store:` defining word, which gives one place to make tables growable.
- Mark-and-release roll-back of store counts: exactly the per-declaration
  scratch tier that con-ron and kefir use.
- The explicit ok, invalid, exhausted and unknown outcomes, and failing
  closed.
- `mixed-level-substitute`'s memo keyed by node index.
- Fuel as an explicit budget.
- Gforth pthreads, measured at about 6× speed-up for 12 CPU-bound tasks.

## 5. Recommended data structures and pipeline (Forth)

1. **Two storage tiers.**
   - An immutable **environment tier**: growable `ALLOCATE`/`RESIZE` arenas
     addressed by index, never by address, with packed 32-bit fields. Gforth
     has `l@`/`l!`; put them in the portability adapter. The export's dense
     `ie`, `in` and `il` indices are used directly after checking that every
     reference points backwards. No per-node identity is stored.
   - A per-declaration **scratch tier**: a region released after each
     declaration, as the existing roll-back already does.
   - Sizing: environment about 3–6 GB for Mathlib; scratch budget 0.25–1 GB
     per worker, with exhaustion reported as a resource outcome and retried
     serially with a larger budget.
2. **Hash-consing.**
   - Expression and level constructors look up `(tag, children, payload)` in
     an open-addressing table. Each node caches its hash, loose-bound-variable
     range, depth and has-parameter flags, as Lean's `Expr.Data` does.
   - Names are interned through a hash on `(prefix, component)`.
   - Declarations are found through an array indexed by name ID, about
     22 MB.
   - For Mathlib the expression table is 2²⁷ four-byte slots, 0.5 GB at load
     0.78, held per tier.
   - Hash-consing only improves performance. Soundness must never assume
     that the exporter shared nodes.
3. **Caches keyed by node index** in the scratch tier: `whnf_core`, `whnf`,
   infer (two modes), definitional-equality success and failure pairs, and
   `(node, offset)` memos for instantiate, shift and level substitution. Use
   epoch-stamped tables so clearing costs nothing, and charge no fuel on cache
   hits.
4. **Validate once.** Check structure while reading the stream, and keep "all
   nodes valid" as a store invariant. Handle checks are O(1). Delete the
   per-call whole-graph audits.
5. **Binder representation.** Choose locally nameless with free variables,
   as Lean does, or de Bruijn with lazy shifting, as nano-lean and nanobruijn
   do. Both are published. The choice is a kernel-representation ADR and
   goes through the review gate.
6. **Streaming NDJSON reader in Forth** for export 3.1.0. It reads lines,
   uses a schema-specific scanner (keys are sorted), applies the strict
   framing rules in `NDJSON_PREVIEW.md`, and fills the environment tier
   directly. Measured sketch: 339 MB of `Init` scanned and 6.1 M expressions
   hash-consed in **3.5 s with `gforth-fast`** (96 MB/s, 381 MB RSS). That
   extrapolates to about 1 minute for Mathlib's 5.8 GB (estimate). The Python
   preview stays as a differential oracle.
7. **Parallel checking.**
   - Load sequentially. Then N Gforth pthreads take declarations from a
     queue. Each task holds a context record (scratch, caches, work stacks,
     fuel, statistics) reached through one `USER` variable. The environment
     is shared read-only, with no locks.
   - A declaration is *accepted* only if it passes and every transitive
     dependency is accepted (a closure pass), with references required to
     point backwards so there are no cycles. This acceptance rule is a
     verifier-bypass risk and needs the review gate.
   - Use about 6 workers, matching the 6 physical cores.
   - Separate processes would multiply memory: 6 × 4 GB is about this
     machine's 25 GiB available. Sharing through a memory-mapped file needs a C
     binding, which is a new dependency and needs approval.
8. **Memory budgets and measurement** (roadmap M1–M2): limits per tier and
   per worker, high-water marks, and process RSS reported on every run.

**Order of work** (each step behaviour-preserving and tested; kernel-semantics
items go through the gate):

1. growable `store:` with 32-bit index fields, and removal of capacity-sized
   scratch;
2. a hash-table library in `lib/`, then name and level interning;
3. a validated-by-construction invariant that replaces per-call audits;
4. hash-consed term constructors with cached node data;
5. memoised walkers and pointer-equality fast paths;
6. context records reached through a `USER` pointer;
7. the streaming Forth NDJSON reader, replacing the eleven test readers;
8. kernel caches together with declaration features (inductives, recursors,
   quotients, projections, `let`, delta unfolding);
9. bignum Nat and String literals;
10. the parallel scheduler and the closure acceptance rule;
11. measurement at every rung (M3, against the bundled `leanchecker`,
    `nanoda`, `lean4lean` and `con-*`).

## 6. Staged target ladder

Forth CPU figures assume Lean-kernel-equivalent algorithms and Gforth-fast
running 3–10× slower than C++ or Rust on this pointer-chasing code. That
ratio is **unmeasured**, so these are low-confidence estimates. The
environment-tier column uses the 30–60 B per node range from section 3.

| Rung | Corpus size | Environment tier (est.) | Forth single-thread CPU (est.) | Reference |
| --- | --- | --- | --- | --- |
| 0. `Init.Prelude` | 3.6 MB, 64.1 k lines (arena) | < 10 MB | seconds | Already needs inductives, recursors, `Quot`, literals |
| 1. `Init` | 59,349 constants, 6.1 M expressions, 346 MB (measured) | 0.2–0.4 GB | 2–6 min | C++ 38 s / 528 MB; nanoda 38 s / 364 MB (measured) |
| 2. `Std` | 99,619 constants, 9.5 M expressions, 562 MB (measured) | 0.3–0.6 GB | 6–20 min | official 1.9 min / 932 MB (arena) |
| 3. Lean and Batteries (Mathlib's other dependencies) | unknown locally | about 1–1.5 GB | 0.3–1 h | lean4checker: Lean 37 s, Batteries 32 s (2024 paper) |
| 4. Mathlib slice (for example, the import closure of one algebra or order module) | unknown; perhaps 150–250 k constants | 1–2 GB | 1–2 h | needs a local Mathlib build, which needs network approval |
| 5. All of Mathlib | 718,574 declarations, 109.8 M lines, 5.8 GB (arena, Lean 4.34.1) | 3–6 GB plus about 1 GB per worker | 1.5–7.5 h CPU, about 15–75 min wall at 6× (6 physical cores) | official 32.3 min / 9.9 GB; kefir 6.8 min / 2.3 GB |

Disk rather than memory limits rungs 4–5 here; see the budget below.

### Machine and disk budget (what fits in about 10 GB)

Machine facts from the coordinator:

- WSL2 on an AMD Ryzen 5 7600X: 6 physical cores, 12 threads. The measured
  6× Gforth pthread speed-up matches the physical core count, so plan for
  about 6×, not 12×.
- 39 GiB of RAM visible, about 25 GiB available.
- About 13 GB of disk free on a 1007 GB file system that is 99% full. Treat
  about 10 GB as the hard budget.

Memory is not the constraint: even rung 5 at 3–6 GB plus 6 × 1 GB of
workers fits. Disk is the constraint.

| Item | Size on disk | Basis |
| --- | --- | --- |
| `Init` / `Std` compiled files (already installed with the toolchain) | 0.40 / 0.34 GB | measured `du` |
| `Init` export: raw / gzip -6 / zstd -3 / zstd -19 | 346 / 57 / 60 / 38 MB (6.1× / 5.7× / 9.1×) | measured |
| Mathlib export: raw / gzip / zstd -19 | 5.8 GB / about 0.95 GB / about 0.65 GB | arena size (verified) × `Init` ratios (estimate) |
| Mathlib compiled files (`.lake/build`) | about 4.5 GB (Jan 2025); likely 5–7 GB now | Zulip "Saving disk space?" thread (reported); growth is my estimate |
| Mathlib compressed download cache (`~/.cache/mathlib`) | unknown, about 1–2 GB per snapshot; one user found 145 GB accumulated (Aug 2025) | Zulip "disc space and .cache remark" (reported) |
| Subset download (`lake exe cache get Mathlib/X/Y.lean` fetches only that file's import closure) | for example 2.7 GB instead of 5.1 GB (Jan 2025) | Zulip "Size issue" (reported) |
| Lean toolchain | already installed (2.8 GB), if the chosen Mathlib commit pins Lean 4.35.0 | measured |

What fits in about 10 GB:

- **Rungs 1–3: about 0 GB extra.** `Init`, `Std` and `Lean` come with the
  toolchain. Batteries is a small source download (estimate under 0.5 GB with
  its build), which still needs approval. Exports are streamed, or kept
  compressed at about 40–60 MB per 350 MB.
- **Rung 4, a Mathlib slice: about 3–4 GB.** That is a partial
  `cache get` plus a slice export kept compressed. Comfortable.
- **Rung 5, all of Mathlib: about 6–9 GB** (estimate, tight). That is the
  Mathlib checkout and compiled files (5–7 GB) and a cleared download cache
  (point `MATHLIB_CACHE_DIR` at the scratch area and delete it by name after
  unpacking). The export must be streamed (`leanexport Mathlib |
  forth-reader`) or stored zstd-compressed (about 0.65 GB); the raw 5.8 GB
  text does not fit alongside the compiled files.
- **Exporter memory:** Mathlib CI exports Mathlib on a 16 GB runner
  (reported), so it fits in the 25 GiB available.
- **Network:** fetching Mathlib is a new network dependency of several GB.
  It needs the owner's approval. Nothing was downloaded for this report.
- **A version catch:** the arena's published Mathlib export is for Lean
  4.34.1, not the pinned 4.35.0.

## Sources

**Verified by me:**

- [Lean Kernel Arena, Mathlib test](https://arena.lean-lang.org/test/mathlib/)
- [Arena, Std test](https://arena.lean-lang.org/test/std/)
- [Arena, Init test](https://arena.lean-lang.org/test/init/)
- [lean4lean paper, Fig. 2](https://arxiv.org/html/2403.14064v3)
- [Mathlib statistics](https://leanprover-community.github.io/mathlib_stats.html)

**Reported by the research subagent:**

- [Arena, official checker](https://arena.lean-lang.org/checker/official/)
- [lean4export format](https://raw.githubusercontent.com/leanprover/lean4export/master/format_ndjson.md)
- [FLT releases](https://github.com/Kha/fermats-last-theorem/releases)
- [Mathlib daily CI workflow](https://raw.githubusercontent.com/leanprover-community/mathlib4/master/.github/workflows/daily.yml)
- [Lean kernel `type_checker.h`](https://raw.githubusercontent.com/leanprover/lean4/v4.34.1/src/kernel/type_checker.h)
- [Bailey, *Type checking in Lean 4*](https://ammkrn.github.io/type_checking_in_lean4/)
- [Lean 4.35.0 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/)
- [Zulip: 2 million lines](https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/2.20million.html)

**Disk figures (search results; anecdotal):**

- [Zulip: Saving disk space?](https://leanprover-community.github.io/archive/stream/113488-general/topic/Saving.20disk.20space.3F.html)
- [Zulip: Size issue](https://leanprover-community.github.io/archive/stream/270676-lean4/topic/Size.20issue.html)
- [Zulip: disc space and .cache remark](https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/disc.20space.20and.20.2Ecache.20remark.html)

## Reproduction

The measurements ran in a scratch directory; nothing in the repository was
changed. The scripts are kept in
[`docs/development/measurements/scale-2026-11-02/`](../development/measurements/scale-2026-11-02/):

- `count.py`: record counts and bytes per kind;
- `dag.py`: DAG versus tree sizes and depth;
- `bench.fs`: the Gforth streaming and hash-consing sketch.

All binaries came from
`.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin` (invoked directly,
never through the elan proxies), with Gforth 1.0.0. Each run was timed with
`/usr/bin/time -v`.

Commands:

- `leanexport Init > init.ndjson` and `leanexport Std > std.ndjson`
- `nanoda_bin` with `{"export_file_path": …, "permitted_axioms": ["propext","Classical.choice","Quot.sound"], "unpermitted_axiom_hard_error": false, "nat_extension": true, "string_extension": true}`
- `leanchecker --fresh Init` and `leanchecker Init`
- `gforth-fast bench.fs init.ndjson`
- the capacity sweep of `src/main.fs` with each capacity raised by 1,024

Afterwards:

- I deleted the two export files (0.9 GB), because the disk is 99% full.
  Regenerate them with the commands above; each takes about 13–21 s.
- Lean `Init` maximum expression depth was 325 in both exports.

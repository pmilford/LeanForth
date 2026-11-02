# Full Mathlib kernel export with the pinned Lean 4.35.0: measurements

Measured 2026-11-02 (local time, UTC-8) by a Claude Code subagent, following
owner approval of OQ-9 ([the draft plan](../../../project/PLAN_DRAFT.md)). Everything downloaded or
generated lives in `.tools/mathlib/` (gitignored).
The scripts and the count and DAG outputs are in this folder; the RSS
monitor logs stayed in the measuring session's scratch folder.
All figures below are **measured** on this machine unless stated otherwise.

## Summary

| Item | Value |
| --- | --- |
| Mathlib | tag `v4.35.0`, commit `56a005855ea17e0b0958f73ec801ae140b0a1679` (2026-10-13, "chore: bump toolchain to v4.35.0 (#44806)"); `lean-toolchain` = `leanprover/lean4:v4.35.0` exactly |
| Lean | 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (pinned toolchain binaries, no elan proxy used) |
| Exporter | `leanexport` from the pinned toolchain; header says lean4export 3.1.0, format 3.1.0 |
| Cache download | 9,031 `.ltar` files, **455,355,304 B** compressed; `lake exe cache get` **45.5 s** wall |
| `.lake` after cache get | **7,102,787,821 B** (7.1 GB; `.lake/build` 6.7 GB); whole checkout 7,236,621,693 B |
| Export file | `.tools/mathlib/mathlib.ndjson`, **6,258,342,501 B** (6.26 GB, 5.83 GiB), **110,895,826 lines** |
| Export sha256 | `18448e5d228e385d75bf6bad5bd9208a8b561b5e395f372e85caa350211559c6` |
| Export run | **6 min 33.5 s** wall, 336.8 s user + 50.2 s sys, 98% CPU (single-threaded), **peak RSS 13,448,292 KiB = 13.8 GB (12.8 GiB)** |
| Export, zstd -3 | 1,026,182,250 B (6.1x), 3.4 s with `-T6` from page cache (not written to disk) |
| Constants | **729,263** (184,355 defs, 517,916 theorems, 2,913 opaques, 4 axioms, 4 quot, 7,046 inductive types, 9,863 constructors, 7,162 recursors) |
| Expression nodes | **105,894,257** (95.5% of lines) |
| Names / levels | **4,241,558** / **47,805** |
| Max universe parameters / max universe arguments of a `const` | **30 / 30** |
| nanoda 0.4.19, 4 threads | **stopped by the watchdog** at 16.0 GB RSS after 4 min 14 s (see below) |
| nanoda 0.4.19, 1 thread | **stopped by the watchdog** at 16.1 GB RSS after 8 min 5 s |
| DAG statistics | max expression depth 1,221; distinct nodes per declaration median 134, max 95,123; largest tree size 1.25e14 |

**No local reference-checker baseline was obtained.** Both nanoda runs stopped
at the 16 GB RSS limit set to protect the machine, with no output, as the
earlier local nanoda run on `Std` did at 19 GB. The arena reports 6.0 GB for
nanoda on Mathlib.

Total disk used under `.tools/mathlib/`: 13,950,319,498 B (about 14 GB:
cache 0.46 GB, checkout and `.lake` 7.24 GB, export 6.26 GB). Free disk after
the work: 147 GB.

## Machine and versions

- WSL2, kernel 6.18.54.1-microsoft-standard-WSL2; AMD Ryzen 5 7600X, 6 cores /
  12 threads; 39 GiB RAM (40,112 MiB), of which about 11.5 GB was held by the
  owner's image-generation process (PID 1453023, untouched). Available memory
  before the runs: about 24-26 GB.
- Lean 4.35.0 (`eb6cafb`), Lake 5.0.0-src+eb6cafb, from
  `.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin` (`which lean lake`
  resolved there; `ELAN_HOME=/home/peter/code/LeanForth/.tools/elan` was set
  for every command; no `lean`/`lake` elan shim was on PATH).
- `leantar` bundled with that toolchain (the cache tool finds it via
  `lean --print-prefix`).
- git 2.43.0, curl 8.5.0, Python 3.13.2, zstd 1.5.6, GNU time (`/usr/bin/time -v`).
- nanoda_bin 0.4.19 (bundled with the toolchain).

Mathlib dependencies (from `lake-manifest.json`, verified checked out at these
revisions in `.lake/packages`):

| Package | Revision |
| --- | --- |
| batteries | `66e469188fe07963e5cf666c7d4433f45b8131c5` |
| Qq (quote4) | `dce0ad79c486cb1fb504af04f953c3466b0c6db8` |
| aesop | `4a174c490d8707121c4a9290800489f105d85e07` |
| proofwidgets | `df72b022e558978a1c50264cfc4d7fec86fa8e04` |
| importGraph | `a41f0e9a4dea23188ea9cc1c41ac9f8bbafe0b93` |
| LeanSearchClient | `d6b4c7be5be75ec4917c873ac50c756dc1436372` |
| plausible | `dfa4f38190d07c37e315953e08b90fe2d95b3c24` |
| Cli (lean4-cli, inherited) | `c24fe6078c630e89b489bffe59b3e20ac30d12c8` |

## Commands

Environment (`env.sh` in this folder), sourced before every command:

```sh
export ELAN_HOME=/home/peter/code/LeanForth/.tools/elan
export PATH=/home/peter/code/LeanForth/.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
export MATHLIB_CACHE_DIR=/home/peter/code/LeanForth/.tools/mathlib/cache
export XDG_CACHE_HOME=/home/peter/code/LeanForth/.tools/mathlib/xdg-cache   # never created
```

1. Find the tag: `git ls-remote --tags https://github.com/leanprover-community/mathlib4 'v4.35*'`
   gave `v4.35.0 -> 56a005855ea17e0b0958f73ec801ae140b0a1679` (also rc1-rc4;
   `v4.34.1 -> d13f23b`, the arena's Mathlib commit).
2. Clone (9.9 s wall; 153 MB with `.git`):
   `git clone --depth 1 --branch v4.35.0 https://github.com/leanprover-community/mathlib4 .tools/mathlib/mathlib4`
3. Cache (in `mathlib4/`): `/usr/bin/time -v lake exe cache get`.
   This cloned the 8 dependencies, built the `cache` executable (42 jobs),
   downloaded 9,031 files and decompressed them. 45.5 s wall, 50.0 s user,
   75.5 s sys, peak RSS 1.0 GB, exit 0. Compressed cache:
   455,355,304 B in `.tools/mathlib/cache`. Nothing was built from source.
4. Check: `lake build --no-build Mathlib` gave "All targets up-to-date (9046
   jobs)" in 3.6 s.
5. Search path: `lake env printenv LEAN_PATH` gave the 8 package
   `.lake/build/lib/lean` folders, Mathlib's `.lake/build/lib/lean` and the
   toolchain's `lib/lean`. The export ran `leanexport` directly with that
   `LEAN_PATH` exported (`run_export.sh`; `LEAN_PATH` recorded in
   `export.env`), so `lake` is not in the timing:
   `/usr/bin/time -v leanexport Mathlib > .tools/mathlib/mathlib.ndjson`.
   A watchdog sampled RSS every 2 s by PID (`export.monitor`) with a kill limit
   of 18.5 GB; it was not triggered. RSS rose to about 8 GB in the first
   minute and peaked at 13.4 GB near the end.
6. `wc -l` (2.7 s) and `sha256sum` (3.7 s) on the page-cached file.
7. Counts: `python3 -I docs/development/measurements/scale-2026-11-02/count.py .tools/mathlib/mathlib.ndjson`
   (unchanged repository script; it already streams line by line).
   3 min 32.5 s wall, 210.5 s user, peak RSS 36.6 MB.
8. DAG statistics: `python3 -I docs/development/measurements/mathlib-2026-11-02/dag_compact.py .tools/mathlib/mathlib.ndjson`,
   a memory-compact variant of the repository's `dag.py` (32-bit arrays,
   float64 tree sizes; the original's Python int lists would need roughly
   8-10 GB here). Its output matched `dag.py` line for line on an
   `Init.Prelude` export (`sample/`). 5 min 53.8 s wall, 347.0 s user, peak
   RSS 3.27 GB. Ran concurrently with step 7 on a separate core.
9. `zstd -3 -T6 -q -c mathlib.ndjson | wc -c` gave 1,026,182,250 (3.35 s).
10. nanoda (optional step): `run_watched.sh nanoda 16000000 2700 - nanoda_bin nanoda.json`
    and the same with `nanoda1.json` (1 thread). Config:
    `{"export_file_path": ".../mathlib.ndjson", "use_stdin": false,
    "permitted_axioms": ["propext","Classical.choice","Quot.sound"],
    "unpermitted_axiom_hard_error": false, "nat_extension": true,
    "string_extension": true, "num_threads": 4 (or 1), "print_success_message": true}`.
    `num_threads` is not in `--help` but is a field of nanoda's config struct;
    the config was validated on the `Init.Prelude` sample (2,120 declarations
    checked in 0.04 s).

## Record counts (`count.py`)

| Kind | Records | Bytes | B/record |
| --- | ---: | ---: | ---: |
| expr.app | 90,514,763 | 4,603,891,630 | 50.9 |
| expr.lam | 8,207,621 | 741,116,823 | 90.3 |
| expr.forallE | 5,437,711 | 514,427,042 | 94.6 |
| expr.const | 1,426,722 | 76,671,590 | 53.7 |
| expr.letE | 242,083 | 24,221,283 | 100.1 |
| expr.proj | 38,389 | 2,475,061 | 64.5 |
| expr.strVal | 19,235 | 3,688,190 | 191.7 |
| expr.natVal | 5,616 | 295,825 | 52.7 |
| expr.sort | 1,757 | 49,226 | 28.0 |
| expr.bvar | 360 | 9,323 | 25.9 |
| name | 4,241,558 | 211,697,994 | 49.9 |
| level | 47,805 | 1,404,410 | 29.4 |
| decl.thm | 517,916 | 49,685,418 | 95.9 |
| decl.def | 184,355 | 23,947,418 | 129.9 |
| decl.inductive (blocks) | 7,013 | 4,428,374 | 631.5 |
| decl.opaque | 2,913 | 332,153 | 114.0 |
| decl.axiom | 4 | 294 | 73.5 |
| decl.quot | 4 | 274 | 68.5 |
| meta | 1 | 173 | 173.0 |

- Records sum to 110,895,826, equal to `wc -l`; bytes sum to the file size.
- Expression mix: app 85.5%, lam 7.8%, forallE 5.1%, const 1.35%, letE 0.23%,
  proj 0.04%; no `mdata`, `fvar` or `mvar` records. `app` records are 73.6%
  of all bytes. About 59 B of export per expression node.
- Name component strings total 19,787,897 B.
- Inductive blocks: 7,013 records containing 7,046 types, 9,863 constructors
  and 7,162 recursors.
- Universe parameters per declaration record (histogram, inductive blocks
  counted once): 0: 146,073; 1: 231,055; 2: 186,873; 3: 77,394; 4: 42,514;
  5: 10,879; 6: 10,508; 7: 2,850; 8: 2,228; 9: 432; 10: 493; 11: 59; 12: 340;
  13: 57; 14: 88; 15: 98; 16: 95; 18: 135; 19: 5; 20: 9; 22: 1; 24: 16; 26: 1;
  30: 2. So 4,059 declarations have more than 7 and 1,831 more than 8. The
  maximum number of universe arguments on a `const` node is also 30.

## DAG and tree sizes (`dag_compact.py`)

Per declaration record (712,205; an inductive block's roots are all its types,
constructors, recursors and recursor rules):

| Measure | Value |
| --- | --- |
| Expression nodes / maximum expression depth | 105,894,257 / **1,221** (Init: 325) |
| Distinct nodes reachable per declaration | median 134, p90 672, p99 3,010, **max 95,123**; sum 226,236,107 (2.14 per distinct node) |
| Tree size (paths) per declaration | median 436, p90 12,202, p99 4.55e5, **max 1.246e14**; sum 1.296e14 |
| Tree / DAG ratio | median 3.10, p90 20.7, p99 251.6, max 1.50e10; total 5.73e5 (dominated by the one 1.2e14 declaration) |
| Declarations with tree size > 1e4 / 1e6 / 1e9 / 1e12 | 79,945 / 3,913 / 30 / 2 |
| Declarations with more than 64 / 1e4 / 1e5 distinct nodes | 527,201 (74.0%) / 535 / 0 |
| Expression depth per declaration | median 24, p99 90, max 1,221 |

Largest by distinct nodes: `CategoryTheory.Functor.IsDenseSubsite.isIso_ranCounit_app_of_isDenseSubsite`
(95,123), `Std.Tactic.BVDecide.BVExpr.bitblast.goCache_Inv_of_Inv._mutual`
(79,001, the `Std` maximum already in `SCALE_ASSESSMENT.md`),
`_private.Mathlib.LinearAlgebra.RootSystem.Finite.G2.0.RootPairing.EmbeddedG2.isOrthogonal_short_and_long_aux._proof_1_1`
(70,430), `AlgebraicGeometry.Proj.lift_awayMapₐ_awayMapₐ_surjective` (65,996).

Largest by tree size: `_private.Mathlib.Condensed.Light.Sequence.0.InternalProjectivityProof.aux`
(1.246e14), `CategoryTheory.Limits.colimitLimitToLimitColimit_surjective`
(4.67e12), `IsEvenlyCovered.toTrivialization_apply` (1.01e11),
`groupCohomology.H1InfRes_exact` (2.43e10). Full top-10 lists are in `dag.out`.

## Reference checker (nanoda 0.4.19)

Both runs were stopped (SIGTERM to the nanoda PID) by the RSS watchdog at the
16 GB limit chosen to keep at least about 8 GB available for the owner's
process and the system. Neither printed anything, so no declaration count or
error is available. Available memory before each run was about 25 GB.

| Run | Load phase | After loading | Stopped at | CPU |
| --- | --- | --- | --- | --- |
| 4 threads (`nanoda.json`) | about 2 min, single-threaded, to about 5.8 GB | RSS grew from 5.8 GB at 13:47:32 to 16.0 GB at 13:49:37, about 5 GB/min | 4 min 13.9 s wall, 16,041,468 KiB | 712.3 s user, 290% |
| 1 thread (`nanoda1.json`) | about 1.5 min, to 5.66 GB | **flat at 5.66-5.80 GB for about 2.75 min**, then grew from 13:55:17 at about 2.4 GB/min | 8 min 4.5 s wall, 16,060,812 KiB | 467.6 s user, 99% |

Interpretation (not investigated further):

- The growth is not caused by the thread count. A single thread holds steady
  for about three minutes of checking and then grows without limit. That
  points to a particular region of the export, probably a few heavy
  declarations.
- `SCALE_ASSESSMENT.md` records the same pattern on the `Std` export: more
  than 19 GB after 6.7 minutes, against the arena's 58 s and 709 MB. Mathlib
  contains `Std`, so this is probably the same trigger.
- Candidates to test next, cheaply, on the 562 MB `Std` export:
  - `nat_extension` and `string_extension` off;
  - an upstream nanoda release instead of the bundled 0.4.19;
  - the arena's exact nanoda configuration.
- The load phase is a useful number in itself: nanoda holds the whole Mathlib
  environment in about 5.8 GB (5,669,940 KiB, about 55 B per expression node, all-in),
  close to the arena's 6.0 GB total.

## Comparison with the estimates in `SCALE_ASSESSMENT.md`

| Item | Estimate or published figure | Measured here |
| --- | --- | --- |
| Export size / lines | 5.8 GB, 109.8 M lines (arena, Lean 4.34.1, Mathlib `d13f23b`) | 6.26 GB (5.83 GiB), 110.9 M lines (+1.0%) |
| Declarations | 718,574 (arena, official checker) | 729,263 constants (+1.5%; newer Mathlib) |
| Expressions | about 103 M | 105.9 M |
| Names | 5-6 M | 4.24 M |
| Levels | tens of thousands | 47,805 |
| Name pool | 25-30 MB | 19.8 MB of component strings |
| Max universe arguments | unknown; LeanForth's limit is 8 | **30**; 1,831 declarations exceed 8 |
| Max expression depth | unknown (Init 325) | 1,221 |
| Largest declaration (distinct nodes) | Std 79,001 | 95,123 |
| Compiled files (`.lake`) | 5-7 GB | 7.1 GB |
| Download | 1-2 GB | 0.46 GB compressed |
| Export, compressed | gzip about 0.95 GB, zstd -19 about 0.65 GB | zstd -3: 1.03 GB |
| Exporter memory | fits a 16 GB CI runner | 13.8 GB peak RSS, 6.6 min |

## Failed, skipped or worth knowing

- `leanchecker --fresh Mathlib` was skipped, as instructed (too long).
- `count.py` was used unchanged; no streaming variant was needed (36.6 MB
  RSS). `dag.py` was not run on the full export; the compact variant was used
  instead (see step 8).
- Both nanoda runs (4 threads and 1 thread) were stopped by the watchdog at
  16 GB RSS. They are resource stops, not checker verdicts: nanoda printed
  nothing, so they say nothing about whether Mathlib type-checks. No further
  nanoda variants were tried.
- Nothing was written to `~/.cache/mathlib`, `~/.cache/lake`, `~/.elan` or
  `~/.lake` (checked afterwards).

## Files created by this task

Under `.tools/mathlib/` (delete only by these exact
names if space is needed):

- `mathlib4/` (shallow clone plus `.lake/`, 7.24 GB)
- `cache/` (compressed `.ltar` download cache, 0.46 GB; safe to delete after
  unpacking, but `lake exe cache get` would then download again)
- `mathlib.ndjson` (export, 6.26 GB)

In this folder: `env.sh`, `run_export.sh`, `run_watched.sh`,
`dag_compact.py`, `nanoda.json`, `nanoda1.json` (absolute export path as
run), `count.out` and `dag.out`. The scripts now take the repository root
from git and write logs to `.tools/mathlib/logs` unless `SP` is set.

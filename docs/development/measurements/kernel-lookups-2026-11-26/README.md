# Kernel lookups measurements (2026-11-25/26)

Counts and profile tables for [KERNEL_LOOKUPS.md](../../../design/KERNEL_LOOKUPS.md). No source file of `src/`
was changed; the counting patch ran on a scratch copy only.

## Machine and load

The 10-thread Ryzen 5 7600X under WSL2 (Linux 6.18), Gforth 1.0.0 `gforth-fast`. Two other agents were
running (kernel tests and a front-end tier): load average 7.7 at the start of the counted run (2026-11-25
23:56:49) and 14.0 just after it (23:58:42). The counts do not depend on load; no time in this folder is
from that run.

## What was measured

1. **Counts on the decide slice** (`counts-decide.txt`): the instantiation prototype's tree (git bundle
   `.claude/work/proto-instantiation-2026-11-25/proto.bundle` of the main checkout, commit `edcb539`, its
   changes P1-P4: the memo reset in one step, stored hashes in hash-table slots, the lean instantiation
   walker, input leaf entries by a dense array; the same changes branch `kernel-speed-3` lands), exported
   to a scratch folder, patched with `count-patch.py` and run as

   ```
   ulimit -u 500
   GFORTH=/home/peter/code/LeanForth/.tools/gforth/bin/gforth-fast \
     bin/leanforth check --jobs 1 --no-manifest --resources --json tests/front/decide-slice.ndjson
   ```

   Result: exit 0, 1,290 declarations accepted, **fuel 2,649,895** (the same total as main's run of the
   same slice in TERM_STORE.md Appendix A: the patch counts, it changes nothing). The patch renames a word
   `w` to `w0` and defines `w` as counters followed by `w0`; the replace memo's lookups are also marked
   in a per-pass column (pass serial and binder offset per node) to tell a second sighting in the same
   pass from a first one; new store nodes count their children's parents (0, 1, 2 or more); two
   direct-mapped tables (1,024 and 65,536 entries) remember the last conses by key to count how often a
   cons repeats a recent key. Counter names are explained in Appendix A of the design.

2. **Profile groups** (`profile-groups.txt`, `profile-inclusive.txt`): the prototype's profile of Init
   (`.claude/work/proto-instantiation-2026-11-25/prof/check.prof` and `check.syms`; 58,163 samples,
   604.0 s wall under the profiler; the unprofiled run's check phase was 575.4 s at one thread, report
   `init-p4-j1.json` there), read with

   ```
   python3 scripts/profile-summary.py --top 3000 check.prof check.syms > full.txt
   python3 groups.py full.txt
   ```

   `groups.py` sums the exclusive shares of the words by kind (input-tier decoding, the base fetch,
   store reads, hash tables, memo, frames, sorting). `profile-inclusive.txt` keeps the inclusive shares of
   the words the design cites. A share of the profile converts to seconds of the check phase at about
   5.9 s a point (575.4 s / 97.62%, the check phase's share of the samples): an estimate, since the
   profiled run was slower than the unprofiled one.

## Results in short

| Count (decide slice, prototype P1-P4) | Value |
| --- | ---: |
| instantiation walks set up / their visits (roots answered at once as closed are not counted) | 98,493 / 1,237,176 |
| replace-memo lookups / hits / inserts | 655,857 / 62,065 (9.5%) / 593,792 |
| lookups on a node already seen in the same pass | 62,673 (9.6%) |
| hits in the same pass / from an earlier call | 60,339 / 1,726 |
| hits at another binder offset than the node's first sighting | 457 |
| lookups / hits of stamped (scope) calls | 294,669 / 50,873 |
| lookups / hits on input-tier nodes | 397,502 / 54,549 |
| lookups / hits on store nodes with at most one parent | 13,517 / 0 |
| conses / given by the input tier / found in the store / new | 833,837 / 62,068 / 375,752 / 396,017 |
| conses whose key is in a 1,024-entry recent table (same node) | 349,545 (336,565) |
| conses whose key is in a 65,536-entry recent table (same node) | 520,579 (481,485) |
| field reads input / store; data words input / store | 6.97 M / 8.11 M; 2.29 M / 2.01 M |
| input record decodes (`lf-tin-record`) | 16.76 M |
| universe substitutions / reached Sorts / child images / binary rebuilds / their conses | 14,985 / 21,775 / 175,110 / 131,928 / 141,915 |

Caches (hits / misses / stores): infer 27,542 / 75,618 / –; infer-only 4,628 / 7,196 / –; whnf_core
901 / 59,579 / 14,098; whnf 4,085 / 4,579 / 4,579; unfold 6,882 / 2,542 / 2,542; success pairs
1,202 / 13,474 / 60,244; failure pairs 2 / 326 / 29 (the inferred-type caches store through another
word, not counted).

A "same node" count above the found conses (437,820) is possible: rollback frees store numbers and a
later cons makes the same key again at the same number; a real front table checks the node's identity
and misses there.

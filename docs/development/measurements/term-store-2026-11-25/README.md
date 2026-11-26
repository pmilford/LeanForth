# Term-store measurements (2026-11-25)

For [TERM_STORE.md](../../../design/TERM_STORE.md): what an operation on a 16-byte term node costs in
LeanForth's own words, in well-written Forth and in C, and what Init's instantiation passes visit. Report
only; nothing here is a test target.

**Machine and load.** The 10-thread Ryzen 5 7600X under WSL2 (Linux 6.18), Gforth 1.0.0 `gforth-fast` from
`.tools/gforth`, gcc 13.3.0 (Ubuntu 24.04) at `-O2`, one thread. Another agent's tests ran meanwhile: load
average 0.5 to 3.6 (given per run below). Single runs; the ranges are over three runs.

## Files

- `bench.fs` — the Forth benchmarks: *chase* (follow random children down a random DAG, reading tag, data
  and one child per step), *cons* (hash-cons `app(a, b)` for random `a`, `b` below 2,048: 4.2 M calls, 37%
  found, 2.7 M nodes), *inst* (instantiate bound variable 0 in a random tree of depth 18, keeping closed
  subterms by the data word, rebuilding with cons; 327,767 visits). Forms: *cur* (LeanForth's
  `lf-term-tag@`, `lf-term-first@`, `lf-term-second@`, `lf-term-data-word`, `lf-term-app` on a store
  without an input view), *col* (one colon word per field), *raw* (the reads written out in the step).
  Uses Gforth's `ul@` and `l!` (not Forth-2012; a benchmark only).
- `bench.c` — the same layout and operations in C.
- `count-patch.py` — inserts entry counters on 25 words (and, as described in TERM_STORE.md Appendix A,
  timers around `lf-term-add`, `lf-open-pass`, `lf-cterm-check`, `lf-mixed-level-substitute`, added by a
  second inline script of the same kind) into a scratch copy of `src/`, and prints them when the command
  line leaves.

## Commands

```sh
cd docs/development/measurements/term-store-2026-11-25
ulimit -u 500
.../.tools/gforth/bin/gforth-fast bench.fs -e "all bye"
gcc -O2 -o /tmp/.../benchc bench.c && /tmp/.../benchc
# counts: a scratch copy (cp -r src bin scripts), then
python3 count-patch.py /abs/path/of/the/copy
GFORTH=.../gforth-fast /abs/path/of/the/copy/bin/leanforth check --jobs 1 --no-manifest --resources \
  --json tests/front/decide-slice.ndjson > report.json 2> counts.txt
```

## Results

Per operation, from three runs (21:58, load 0.5-2.7; 22:04 twice, load 2.0-2.7):

| Operation | cur | col | raw | C | raw / C |
| --- | ---: | ---: | ---: | ---: | ---: |
| chase, 4,096 nodes, per step | 12.7-13.7 ns | 7.3-8.7 | 3.8-4.6 | 1.0-1.4 | 3.2-3.8 |
| chase, 4 M nodes (64 MB), per step | 46-75 | 48-66 | 46-65 | 47-57 | 0.8-1.2 |
| hash-cons, per call | 329-410 | – | 179-210 | 61-71 | 2.5-3.2 |
| rebuild, per visit | – | – | 15.7-24.1 | 4.0-5.5 | 3.9-4.4 |

Raw milliseconds are in TERM_STORE.md, Appendix B. The real instantiation pass on the decide slice costs
862 ns a visit (timed, Appendix A there).

Counts on `tests/front/decide-slice.ndjson` (scratch copy of main f0f552fd, 2026-11-25 21:56-22:01, load
0.6-3.6): 134,665 instantiation passes (62,684 on a closed root), 1,322,249 visits = 134,665 + 2 x 593,792
rebuilt nodes (Lean's `replace` rule), 516,370 leaves, 150,022 closed binary nodes kept, 62,065 memo hits;
fuel 2,649,895; the full table is TERM_STORE.md Appendix A.

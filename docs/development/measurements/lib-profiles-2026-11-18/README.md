# Library profiles, 2026-11-18

The measurements behind [FORTH_LIBRARY.md, "Measured profiles"](../../FORTH_LIBRARY.md#measured-profiles-2026-11-18)
(plan task 1.1.8, branch `lib-tidy-2`). Machine: 10 logical cores under WSL2, shared
with other agents (load average 3 to 5 during the runs); Gforth 1.0.0.

- `bench.txt`: `make lib-bench GFORTH=.../.tools/gforth/bin/gforth` (the driver is
  `tests/lib/lib-bench.fs`): each library at a small and a large size on gforth-fast,
  then gforth. Each figure is the better of two runs of at least 0.2 s.
- `counts.txt`: how often LeanForth calls each library, and with what sizes, on a
  check of `Init` (59,349 declarations). Made on a scratch copy of the source, never
  on `src/`:

  ```sh
  mkdir -p W/inst && git archive HEAD src bin | tar -x -C W/inst
  python3 docs/development/measurements/lib-profiles-2026-11-18/tools/patch-lib.py W/inst
  cd W/inst && GFORTH=.../gforth-fast bin/leanforth check --json --jobs 1 \
      --save-snapshot ../cnt.lfsnap .claude/work/S1DONE/init.ndjson > ../cnt.json
  grep '^LCNT' ../cnt.json
  ```

  `tools/patch-lib.py` puts a counter (`tools/libcnt.fs`) at the start of 54 library
  words and prints them when the command ends, one line `LCNT i calls total largest
  | k:n ...` each; `counts.txt` gives them with the names of `tools/labels.txt`:
  the calls, the sum and the largest of the sizes passed, and how many sizes fell in
  each power of two (k: sizes from 2^k to 2^(k+1)-1; 0 also holds sizes 0 and 1).
  The counters are global, so the run uses one job; the job pool and the scheduler's
  priority queues, used only with `--jobs` above 1, are not counted. The run took
  1,078 s (gforth-fast, counters in place) and gave exit 0.

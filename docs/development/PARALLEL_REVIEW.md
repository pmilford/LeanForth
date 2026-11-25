# LeanForth parallel running: where it stands (review of 2026-11-23)

Read-only review of `main` at 17692c36. Measured today on the 10-thread machine (Ryzen 5 7600X: 5 physical
cores, 2 threads each, 39 GB). Load average was 0.14 at the start, and no other heavy work ran: the timings are
fair. Measured = run today. Recorded = a number in a document or run log. Estimate = arithmetic on those numbers.
Raw outputs were kept in a scratch folder and are not in the repository.

## The four answers (one page)

1. **How much runs in parallel, and is it re-entrant?** Only one thing runs in parallel: the kernel's type check
   of an export's declarations under `check --jobs N`. Each declaration is one job, run in its own worker
   context. That is 98% of a one-worker Init check (951 of 970 s, measured) and 93% of the recorded Mathlib run.
   These parts are serial:
   - reading and decoding the export (the "stage");
   - feeding the input to each worker, one worker after another;
   - publishing each result (one publisher, by design, so that verdicts match the serial run);
   - loading a snapshot;
   - saving a snapshot;
   - the whole front end (`.lf` text).

   The checking layers (lib, core, kernel, the loader) keep their state in context records (228 members). A test
   shows the dictionary unchanged after real work in contexts. Run-time globals remain in one place: about 20
   records that drive a run, 16 of them in `src/cli/check-run.fs`. So a process runs one check at a time, and
   only the driving task writes those records. The front end keeps its state in contexts too, but two things
   stop it from running in a job:
   - it reads text with Forth's `EVALUATE`, which a job may not do;
   - the re-entrancy test exercises only the metavariable context, not elaboration or tactics.
2. **Should elaboration run in parallel?** Not yet: today there is almost nothing to gain. A tactic test's own
   theorems take about 0.05 s of a 4.2 s run. The rest is re-checking the 1,291-declaration library slice.
   Through a snapshot the whole run is 0.43 s. On Init, loading the snapshot takes 9.4 s and the text's own work
   about 2.3 s. The front end's cost is loading the library, not elaborating. Parallel elaboration needs four
   things:
   - reading split from elaborating;
   - each declaration elaborated as a job, with readiness rules like the kernel's;
   - the elaboration data shared read-only;
   - output in source order.

   Rough size: 600-1,500 lines of Forth plus tests (estimate). Do it after the library stays loaded (plan PD21),
   and only once a real text spends seconds elaborating.
3. **Is loading the export the big win?** No. In the recorded Mathlib run (8 workers, 7,357 s) the time splits:
   - stage (read, parse, decode): 240 s, 3.3%;
   - feed: 152 s, 2.1%;
   - snapshot save and output: about 130 s, 1.8%;
   - kernel check: 6,836 s, 92.9%.

   Parsing alone (`count`) read the 6.26 GB export in 127 s today (49 MB/s, 38 MB of memory). The bottleneck at
   every worker count on this machine is the kernel's check. Single-threaded, LeanForth checks Init in 951 s,
   and Lean's own checker takes 38 s (recorded on this machine), about 25 times faster. Loading becomes the
   bottleneck only after the kernel is about 10 times faster.
4. **Is the thread count right? Do workers stall?** Workers barely stall:
   - every run reported "not ready 0, forced 0";
   - during the check phase the workers are busy 94-99% of the time;
   - the job pool sleeps on condition variables and takes one lock per job.

   Two other limits cost the speed:
   - (a) the machine has 5 real cores. Past 4 workers each check costs more CPU (+34% at 8 workers, +49% at 10),
     because two threads share a core.
   - (b) the serial stage and feed. They are 14% of the run at 10 workers on Init, and the feed grows by about
     0.8 s per worker.

   Init speed-up: 1.85 at 2 workers, 3.47 at 4, 5.14 at 8, 5.51 at 10. 10 workers is the fastest setting here.
   4-5 workers give the most result per CPU second. The default is still `--jobs 1`.

## Measurements

All `bin/leanforth` on gforth-fast under `ulimit -u 500`, `/usr/bin/time -v`. The phases are the program's own
`--resources` report. Utilization is (user+sys)/(wall x workers). "Check util." is check CPU/(check wall x
workers), the workers' busy share.

**Init export** (59,349 declarations, 345 MB; `check --resources --jobs N .claude/work/IM/init.ndjson`; all
accepted):

| Workers | Wall s | User s | Peak MB | Stage s | Feed s | Check wall/CPU s | Speed-up (wall) | Check speed-up | Check CPU vs 1 | Util. | Check util. |
| ---: | ---: | ---: | ---: | ---: | ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 1 | 969.8 | 969.0 | 614 | 17.2 | 1.4 | 950.9 / 950.7 | 1.00 | 1.00 | 1.00 | 100% | 100% |
| 2 | 524.1 | 1020.5 | 783 | 16.9 | 2.7 | 504.3 / 1003.7 | 1.85 | 1.89 | 1.06 | 98% | 99.5% |
| 4 | 279.3 | 1035.1 | 907 | 17.2 | 4.1 | 257.7 / 1016.3 | 3.47 | 3.69 | 1.07 | 93% | 98.6% |
| 8 | 188.6 | 1297.7 | 1025 | 17.3 | 7.0 | 164.0 / 1276.1 | 5.14 | 5.80 | 1.34 | 86% | 97.3% |
| 10 | 176.1 | 1442.9 | 1111 | 17.0 | 8.4 | 150.4 / 1420.3 | 5.51 | 6.32 | 1.49 | 82% | 94.5% |

- Every parallel run reported "checks handed out 57919, run again 0, not ready 0, forced 0, workers replaced 0".
- The one-worker time agrees with the nightly record of 2026-11-20 (989.8 s; `.claude/work/parallel-init/init-1.json`).
- Memory grows by about 55 MB per worker.

**p1m** (the first million lines of the Mathlib export: 9,202 declarations, 51 MB; `--no-manifest`):

| Workers | Wall s | User s | Peak MB | Check wall/CPU s | Speed-up | Check speed-up | Check util. |
| ---: | ---: | ---: | ---: | --- | ---: | ---: | ---: |
| 1 | 146.0 | 145.8 | 144 | 143.9 / 143.8 | 1.00 | 1.00 | 100% |
| 2 | 77.5 | 151.5 | 231 | 75.2 / 149.6 | 1.88 | 1.91 | 99.5% |
| 4 | 41.4 | 154.7 | 276 | 38.8 / 152.7 | 3.53 | 3.71 | 98.4% |
| 8 | 27.6 | 193.4 | 396 | 24.7 / 191.2 | 5.29 | 5.83 | 96.7% |
| 10 | 25.9 / 26.0 (twice) | 212.6 / 215.1 | 407 | 22.7 / 210.0 | 5.63 | 6.34 | 92.5-93.4% |

**Loading alone**:

| Command | Wall s | Memory | Throughput |
| --- | ---: | ---: | --- |
| `count` Init (345 MB) | 14.4 | 35 MB | 24 MB/s |
| `count --no-manifest` Mathlib (6.26 GB, 110.9 M records) | 127.2 | 38 MB | 49 MB/s, 0.87 M records/s, 5,730 declarations/s |
| Stage of a full check: Init | 17.2 | (stage 180 MB) | 20 MB/s |
| Stage of a full check: Mathlib, recorded on 677800d7 | 239.6 | (stage 2,993 MB) | 26 MB/s |

**Mathlib, recorded** (`.claude/work/overnight/full-677800d7.txt`, 2026-11-20, `--jobs 8 --fuel 250000000
--memory-per-check 8192 --save-snapshot`): stage 239.6 s, feed 151.5 s, check 6,835.7 s wall / 53,163 s CPU (check
util. 97.2%), total 7,356.8 s, peak 22.8 GB. Its progress lines show resident memory growing with the declarations
done, from 7.0 GB at 7% to 20.5 GB at 100%: it is the environment growing, not the workers. No full Mathlib run was
made today.

**Front end** (`check --resources`, gforth-fast unless said; each measured twice):

| Run | Wall s | Split |
| --- | ---: | --- |
| `--env tests/front/decide-slice.ndjson --elab-data ... tests/front/tactics/decide/dc-logic.lf` | 4.22, 4.21 | check phase 3.70 s |
| The same export alone, no text | 4.11, 4.05 | check phase 3.71 s: the text's own work is about 0.1 s |
| The same text against a snapshot of the slice (`--snapshot`) | 0.44, 0.43 | stage 0.15, check 0.05 s; Gforth start about 0.18 s |
| A batch-a tactic test (`change.lf`) on `--env tests/front/s2-slice.ndjson`, checking engine `gforth` | 2.07 | check phase 1.57 s, mostly the 579-declaration slice (0.66 s alone on gforth-fast) |
| `dc-init.lf` against Init's snapshot (`init-1.lfsn`) with Init's elaboration data | 11.68, 11.92 | 59,349 declarations taken from the snapshot, 4 checked |
| Init's snapshot alone, no text | 9.41 | the text's own work (elaboration data, instance table, 4 theorems) is about 2.3 s |

- The tactic harness (`tests/front/tactics/tactic_check.py:87`) runs every `.lf` (207 files under
  `tests/front/tactics/`) with `--env`, so each run re-checks its library slice.
- `decide/check.py:237` already uses `--snapshot`.

**Re-entrancy counts** (`python3 scripts/forth-metrics.py` over the 301 files of `src/`):
- The tool's "globals" count is 545, but most of those are tables written only while loading (dispatch tables,
  message tables, hash-table hooks). The most are in `import/ndjson.fs` (79), `front/elab-data.fs` (69) and
  `author/words.fs` (65).
- 228 context members (193 `context-record:`, 27 walks, 5 frames, 3 stores): 112 in core, 136 in kernel, 106 in
  front, 40 in author.
- Plain `VARIABLE`s/`2VARIABLE`s are few:
  - `terms.fs:261,565`: tag sets, frozen once the context is sealed;
  - `context.fs:281,294,341`: declaration lists, load time. `lf-context` and `lf-owner` are per-thread `user`
    cells, `context.fs:152`;
  - `env-snapshot.fs:173,178` and `env-import.fs:132`: written by the driving task;
  - `env-schedule.fs:243` and `environment.fs:359`: a test hook, and a test counter added atomically;
  - `check-run.fs:1008,1091`.
- Records written at run time, one per process: `check-run.fs:265-271, 351, 971-979, 1007, 1081-1082` (16 with
  the two 2variables), the `check-json.fs` writer, `run-record.fs:192`, `run-replay.fs:157`, `lf-envs`
  (`environment.fs:82`), `lf-sched` (`env-schedule.fs:109`), and the pool and queue (`task.fs:99`).

## What is parallel today

| Stage | Parallel? | Why |
| --- | --- | --- |
| Reading, parsing and decoding the export (stage) | serial | one reader over a file whose records refer to earlier ones (`import/stage.fs`); perf scan K5 |
| Feeding the input to the contexts | serial, and it grows with workers | `ck-workers-made` fills each worker in turn in the driving task (`cli/check-run.fs:498-521`); workers share the input in place but each gets its own feed |
| Readiness plan (who waits for whom) | serial, time not reported | `lf-sched-plan`, in the driving task before the run |
| Kernel check of each declaration | **parallel**, one declaration per job | `kernel/env-schedule.fs`; job pool `lib/task.fs`: POSIX threads, one mutex, two condition variables (`task.fs:4-8`), one job in flight per worker (`env-schedule.fs:591-617`) |
| Hand-over (publishing), rollback of the worker's scratch, keeping facts, printing lines | serial, in the driving task after each job | single publisher by design (ADR 0009/0012, G-P1), so the verdicts and the environment are the serial run's (`env-schedule.fs:579-590`) |
| Snapshot load and save | serial | perf scan K4 |
| Front end (`.lf`: reading, elaboration, tactics) | serial | the text runs through `EVALUATE` (`author/runner.fs:1-2`), which a job may not use (`task.fs:49-56`); `--jobs` applies to the library's check only |
| Hosts | threads only on x86-64 | `env-schedule.fs:655-661` (no memory barriers are used); elsewhere the run is serial |

## Recommendations, ranked by gain per effort

None of these may change what the kernel accepts. The front end stays untrusted: only the kernel's check of
each elaborated declaration, published in source order by the single publisher, decides a verdict.

1. **Make `--jobs` default to the core count, or at least document the curve.**
   - Today the default is 1 (`bin/leanforth --help`), so a user gets 1x unless they know the option. The owner
     chooses the default (PROJECT_PROGRESS "Parallel checking groundwork").
   - Gain: 5.5x on Init at 10 workers, measured. 4 workers give 3.5x for 7% more CPU.
   - Size: about 5 lines in `src/cli/leanforth.fs` (`task-cores` exists) and a table in
     `docs/user/COMMAND_LINE.md`.
   - Trust: none. Output is identical, as the nightly `make parallel-init` already checks.
   - Measure: this report's table, rerun.
2. **Make the kernel faster on one thread, starting with perf scan K1.**
   - K1: `lf-env-current` re-validates at every gate (`kernel/environment.fs:463`; 58.8 M calls on 9,202
     declarations; PERF1 put it at about 15% of checking CPU). Slice 1 (the environment stamp) is measured
     in [KERNEL_SPEED.md](KERNEL_SPEED.md), "Measured after slice 1".
   - The kernel check is 93% of Mathlib, and every 10% off it is about 680 s at 8 workers. That is more than a
     perfectly parallel stage and feed could save together (at most about 390 s).
   - Size: 50-150 lines in `kernel/environment.fs` and its callers (estimate).
   - Trust: kernel code. Verdicts and fuel counts must stay identical (fuel decides "exhausted"). Run the full
     tier, every pinned-Lean comparison and the nightly parallel run. Moving a fail-closed check is
     behaviour-preserving work under the owner's rule of 2026-11-19 only if nothing it guarded can now be
     reached unchecked.
   - Measure: Init check CPU at `--jobs 1` (951 s today).
3. **Report the driver's and the workers' time in `--resources`.**
   - What to add: the plan's seconds, the driving task's busy seconds (hand-over, rollback, ticks), each
     worker's busy seconds, and the seconds a finished job waited to be settled.
   - Today stalls can only be inferred from utilization. On a machine with more cores the serial hand-over
     decides the ceiling, and this is the number to watch.
   - Size: 40-60 lines in `env-schedule.fs` and `cli/leanforth.fs`, with tests. Trust: none (clocks, report
     only).
4. **Run the tactic tests through a snapshot of their slice made once per test run**, as `decide/check.py`
   already does (perf scan A11).
   - Gain: decide-slice 4.2 s to 0.43 s per run (measured). s2-slice about 1.5 of 2.1 s per run on the checking
     engine. Over about 200 runs: several minutes of CPU per `make test` (estimate).
   - Size: about 30 lines of Python in `tests/front/tactics/tactic_check.py`. Keep one `--env` run per batch so
     the export path stays tested.
   - Trust: the library's verdicts are carried from a snapshot made from the same export in the same test run;
     the text's theorems are still kernel-checked.
5. **Feed the workers in parallel, or make a worker's feed cheaper.**
   - The feed grows by 0.8 s per worker on Init (8.4 s at 10, 4.8% of the run).
   - On Mathlib it is 152 s at 8 workers. About 120 s of that is feeding the extra workers (estimate from Init's
     ratio of 5).
   - How: make `ck-worker-fill` each worker's first job, or find what `lf-feed-shared` copies per worker.
   - Size: 40-80 lines in `cli/check-run.fs` and tests.
   - Trust: none if each worker's fingerprint is still compared with the driving context's (`ck-print`) before
     any check is handed out.
6. **Keep the library loaded between texts (plan PD21).**
   - This is the front end's real cost: Init's snapshot takes 9.4 s against 2.3 s of text work, measured.
     Mathlib takes 4-5 minutes per text, recorded in PD21.
   - Size: a design, then several hundred lines (estimate).
   - Trust: none beyond today's snapshot rule (carried verdicts labelled).
   - Do it before parallel elaboration.
7. **Test front-end re-entrancy.**
   - Extend `tests/core/contexts-main.fs`. Today it exercises only the metavariable context (lines 87-96). Add
     a whole `.lf` declaration elaborated with tactics in a second context, with the dictionary unchanged
     afterwards.
   - Size: about 40 test lines.
   - This gives the owner's rule of 2026-11-18 a check for the front end and is the first step of plan
     9.4.8p(4).
8. **Parse the export on several threads (perf scan K5).**
   - The stage is 240 s on Mathlib (3.3%). Parsing alone is single-threaded at 49 MB/s.
   - How: split the file at line boundaries, parse the ranges in jobs, merge in record order.
   - Gain: about 150 s on Mathlib, about 12 s on Init (estimate).
   - Size: 300-600 lines (estimate).
   - Trust: import is a review-gate area. Malformed input must fail closed with the same error at the same line.
9. **Elaborate a text's declarations in parallel (plan 9.4.8p(4)).**
   - Read in the main task (`EVALUATE`). Each declaration is a job, ready once the statements it names are
     elaborated. Elaboration data is shared read-only. Results are published and printed in source order.
   - Size: 600-1,500 lines plus tests (estimate).
   - Gain today: near zero (the text's own work is 0.05-2.3 s of the runs measured).
   - Trust: elaboration stays untrusted; each result still goes through the kernel and the single publisher.
10. **Gather `check-run.fs`'s 16 run records into one record per run**, only if a server (6) must start a run
    while another holds the library. Size: about 100-200 lines of mechanical change. Trust: none.

Not recommended: more workers than logical cores (`task.fs` already caps at `task-cores`). The tail is no issue
either: Init's costliest declaration takes about 6.5 s, Mathlib's about 440 s of 6,836 s (estimates from fuel
per second).

## Estimates used

- Mathlib at one worker: about 39,600 CPU s of checking (53,163 / 1.34, Init's CPU inflation at 8 workers).
- Mathlib at 10 workers: check about 39,600 / 6.32 = 6,270 s. Adding stage, feed and save gives about 6,800 s,
  against 7,357 s at 8 workers (-8%). Its memory is not known: 22.8 GB at 8 was recorded.
- On a 32-core machine the kernel check would be about 1,240 s. Then the serial 520 s of stage, feed and save would
  be about 30% of the run, and items 5 and 8 would matter.

## Not measured, and why

- The driver's busy time, the time finished jobs wait, and the readiness plan's time: the program has no counters
  for them (recommendation 3). Stalls are inferred from utilization above.
- Mathlib at 1 or 10 workers, its memory per worker, and a full Mathlib run: not run, by instruction. The figures
  above are extrapolations from Init and the recorded run.
- How Lean itself parallelizes elaboration. Reading the pinned source under `.tools` was refused by the
  permission system in this session, so nothing is said about it from the source.
- Elaboration of a large text: no `.lf` text in the tree spends more than a fraction of a second elaborating.
- Light single-thread front-end runs (about 10 s in all) ran beside the one-worker p1m run and `count`. Their
  effect on those timings is negligible.

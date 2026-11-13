# Forth review of pool-fail-closed (2ff0e7b5..0201550f), 2026-11-13 — not blocking

One commit: src/lib/task.fs, src/cli/check-run.fs, src/cli/leanforth.fs, tests, 8 faults, FORTH_LIBRARY.md,
COMMAND_LINE.md, DECISIONS.md. Findings: 0 high, 0 medium, 2 low, 3 info. [runtime] gate: the owner's approval owed.
Answers: no new way for the pool to hang (one rare hang predates the fix, L1); no job lost or run twice; no verdict
depends on how many workers start (tested against the serial run for 0, 1, 2 and unlimited workers); locks taken and
released correctly on every failure path; open files do not grow over 20 refusals; Gforth 1.0's unfreeable stacks are
bounded at one task per refused pool start in normal use; 0.7.3's cooperative path is correct but its freeing of a
refused task is untested (L2).

## Summary for the owner ([runtime] approval)
1. When the computer will not give LeanForth all the worker threads it asked for, the check now runs on the threads it
   did get; before, it crashed in one test or fell back to one at a time. `--resources` says how many started.
2. Results are identical whatever the number of workers (tested against the one-at-a-time run with every worker
   refused, one, two and all); files are not leaked; the job pool tests pass on both Gforths; 8 planted faults caught.
3. Recommendation: approve. Remaining risks: a rare hang that existed before (a thread dying during its own setup) and
   a small memory leak per refused thread on Gforth 1.0, at most one per pool start in normal use.

## Traced
`job-wait 0` answers `task-refused` before reading anything (fault pool-wait-reads-zero caught: exit 139 without it).
Partial start: `pool-live` incremented only after `worker-launch` returns 0, under the lock; `pool-fill` stops at the
first refusal; `pool-fresh` gives 0 with at least one worker, `task-no-worker` with none; `pool-threads` counts only
launched workers, so `workers-join` joins exactly those; a worker cannot leave during start. Refused task on 1.0:
`task-unmade` closes `epiper`/`epipew` as Gforth's kill-task does; never recorded. On 0.7.3: `kill`. `spawn-limit!`
default -1 (no limit), set only in tests and reset. Each job taken once under the lock; with fewer workers jobs wait
in the queue; no deadlock. The report: `ck-lacked!` computes made and lacked after the pool starts; printed only when
lacked > 0.

## Findings
- **L1 (low, predates this commit):** a thread that dies during its own setup (e.g. an allocation failure in Gforth
  1.0's thread-init when memory is exhausted) would leave `pool-live` counted, so `pool-halt`'s drain would wait
  forever. Not caused by this fix (a refused thread is never created). Fix options: workers count themselves live under
  the lock once worker-life begins, pool-start waiting a bounded time; or thread-init's failures under a CATCH ending in
  worker-left. Record as a [runtime] plan task.
- **L2 (low):** 0.7.3's freeing of a refused task is untested (a fault dropping instead of `kill` survives): count heap
  blocks around 20 refusals on the cooperative host.
- Info: unfreeable stacks on 1.0 (at most one task per pool start that meets a refusal; say so in FORTH_LIBRARY.md);
  `host-refused` is 11 (EAGAIN) only for simulated refusals and 0.7.3; tests/lib/task.fs's "Cannot allocate memory"
  message predates the commit.

## Style, tests, runs
task.fs 122 → 130 words, all new ones of 1-2 lines; globals 6, shuffles 10, return-stack ops 33 unchanged; constants
18 → 19; check-run.fs +3 and leanforth.fs +1 short words. Tests: all workers refused, some, none; `job-wait 0`;
interfaces; facts equal to serial for --jobs 3 and 10 with limits 0, 1, 2, -1; the --resources line; open files after
20 refusals; the limit lifted. Runs (git archive copies, `ulimit -u 500`, nice -n 19): tests/lib/task.fs,
task-serial.fs, tests/cli/leanforth.fs on Gforth 1.0.0 and 0.7.3; `mutants --check` 1601 entries, 0 stale; the 8 new
faults caught on 1.0, the 5 that compile on 0.7.3 caught there; reviewer faults: phantom worker caught on both hosts,
the 0.7.3 kill fault survived (L2). Not run: make test/check, a real near-limit run.

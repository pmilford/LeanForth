# Opt-in profiling

## Where a check spends its time

`make profile-check EXPORT=FILE [JOBS=1]` checks an export on `gforth-fast`
under a sampling profiler and prints where the time went (added 2026-11-25;
the measurements made with it are in [KERNEL_SPEED.md](KERNEL_SPEED.md)):

- the phases (stage, feed, check);
- time by word family: instantiation and abstraction passes, universe
  substitution, term construction and hashing, `whnf_core`'s parts,
  definitional equality, type inference, validity checks, caches, the
  scheduler, import and decoding, the walk machinery, the rest. Three
  columns: *exclusive* (where the CPU was), *inclusive* (samples with the
  family anywhere on the stack, once each; they overlap) and *owner* (the
  nearest family outwards that is not a service family such as validity
  checks, term construction, caches, store reads or the walk machinery;
  the owner column adds up to 100%);
- the costliest words, exclusive and inclusive, with their files;
- the slowest declarations by time, with their fuel and nanoseconds per
  fuel unit (`scripts/slowest-declarations.py`, from the run's JSON report
  with `--resources`, which gives each declaration's own check time).

The parts, all in `scripts/`: `profile-sample.py` runs the check as a child,
stops it with `ptrace` every `PROFILE_INTERVAL` seconds (default 0.01) and
reads its Forth return stack; `profile-symbols.fs`, loaded after
`src/main.fs`, writes every word's address, name and source position for
it; `profile-summary.py` makes the tables (`--under WORD` keeps one part of
the run, such as `lf-check-declaration`); `profile-check.sh` ties them
together. The raw files (`check.prof`, `check.syms`, `check.json`) stay in
`PROFILE_OUT` (default `build/profile`). The line `profile-sample: exit 100`
is a good end: Gforth's own exit adds 100 to the check's status 0, which
`profile-check.sh` subtracts. `make test-profile-check` tests the
tools: the tables exactly on a profile made by hand, and a whole run on the
579-declaration S2 slice.

Limits: x86-64 Linux and Gforth 1.0's `gforth-fast` only (the sampler reads
its instruction pointer in `rbx` and its return-stack pointer in `r14`).
Only the first thread is sampled, so profile at `JOBS=1` (the default
here). Each sample stops the check briefly: at 0.02 s a one-worker check of
`Init` took 968 s, against 970 s recorded without the profiler
(KERNEL_SPEED.md). The tool reads the product, it does
not change it: for call counts, patch a scratch copy of `src/` instead, as
KERNEL_SPEED.md's "How it was measured" does. First written as the
perf-scan's tools (agent PERF1, 2026-11-12;
[measurements/perf-scan-2026-11-18/tools/](measurements/perf-scan-2026-11-18/tools/)).

## Profiling of existing tables

From the repository root, run `scripts/profile-existing.sh [repetitions]`;
from another directory, use the path to that script. The default
is three repetitions; the allowed range is 1–99. Set `LEAN` and `GFORTH` to
executable paths or command names if they are not on `PATH`. Lean must match
the existing differential test's 4.35.0 version and exact git hash. Configure
any toolchain-specific environment yourself, for example `ELAN_HOME`; no home
directory or local installation layout is assumed. The script needs Bash,
standard Unix utilities, Git, SHA-256, Lean and Gforth; it adds no dependency.

Each repetition independently runs the Lean and Forth universe-substitution
tables of `make test-mixed-level-substitute-plain-differential`:
`tests/reference/term-level-substitute-table.lean` (Lean's
`instantiateLevelParams`) and `tests/core/mixed-level-substitute-plain-table.fs`
(the current `lf-mixed-level-substitute`). It verifies 48 rows, normalizes
whitespace as that differential test does, compares the two outputs, and
checks consistency across repetitions. Workload failure or output mismatch stops before the report;
a later metadata failure can leave a partial report. The report
contains individual elapsed times and peak process RSS, versions, platform,
revision, worktree status, input file hashes and normalized output hash.
Capture stdout to retain a record. Input hashes cover the wrapper, both
tables and every tracked Forth source under `src/` (the Forth table loads
`src/main.fs`), but not runtime binaries, toolchain libraries, or the full
environment; a dirty worktree needs additional provenance for reproduction.

If compatible `/usr/bin/time` is available on Linux, elapsed time and maximum
RSS are reported per process in KiB. Otherwise Bash's elapsed timer is
used and RSS is unavailable. Timer resolution and scheduling noise can dominate
these tiny workloads. Startup, loading, table construction, formatting and I/O
are included. Lean and Forth have different implementations and runtime
internals, so this is a comparison of complete observed workloads, not isolated
substitution costs or equivalent checker performance. Timer overhead is not
separately measured. Run on an otherwise quiet machine and retain individual
samples; the run order alternates between implementations but has no warmup.
There is no default instrumentation or performance claim.

The table compares a finite selection of substitution syntax observations. It
checks neither types nor proof certificates, and agreement establishes no theorem,
checker correctness, program verification, or general Lean compatibility.

`make profile-existing` runs the same opt-in wrapper with its default three
repetitions and Makefile-selected `LEAN` and `GFORTH`. The current wrapper
measures whole processes only: higher-level product workflows, internal
operation timing, arena allocation counts and profiling-overhead measurement
remain future work in the development roadmap.

For a lightweight history, run `make profile-history`. It runs that same
workload and appends one JSON record with individual samples and the complete
reproducibility report to `.profiling/history.jsonl` (ignored by Git). It
prints median elapsed time and peak RSS for each implementation, plus the
change in elapsed median from the previous record. Use
`python3 scripts/profile-history.py --repetitions 5 --history /path/history.jsonl`
to choose repetitions or storage. `LEAN`, `GFORTH` and any toolchain environment
must be configured as above. The history is local, not sent anywhere; back it
up if needed. Changes in hardware, load, toolchain, code or workload can make
successive numbers incomparable; inspect the saved raw reports. These small
samples have coarse timing resolution. Stage-level time and arena-memory
instrumentation are still planned.

Each record names its workload, and a record is compared only with the
previous record of the same workload. The workload is
`mixed-level-substitution-48` from 2026-11-02, a new timing series. Until then
it was `term-level-substitution-48`, which timed the same Lean table against a
superseded Forth implementation that was retired on 2026-11-02; its timings
are not comparable with the new series, and old records stay in the history
file only as history.

The first sample of the new series is a
[local three-repetition run](measurements/mixed-substitution-profile-2026-11-02.txt)
of `make profile-existing` with the pinned toolchains under `.tools/`. The
Forth table took 0.01–0.02 s and Lean's about 0.95 s, almost all of it
process start-up and loading; this is not a measure of checking speed. The
worktree was dirty (the change that introduced the new workload was not yet
committed); the report lists the hash of every input. The sample's
normalized output has the same SHA-256 as the old series' (`844fc236…`): the
current and the retired implementation print the same 48 rows.

The last sample of the old series, a
[local two-repetition sample](measurements/substitution-profile-2026-11-01.txt)
of the retired implementation, was run from the repository root with:

```sh
ELAN_HOME="$PWD/.tools/elan" libccnameddir=/tmp/leanforth-gforth-libcc \
  LEAN="$PWD/.tools/elan/bin/lean" GFORTH="$PWD/.tools/gforth/bin/gforth" \
  bash scripts/profile-existing.sh 2
```

Both recorded worktrees were dirty; the reports include source hashes and are
not general performance comparisons. It does not establish CI status or benchmark
trusted proof checking.

# Opt-in profiling of existing tables

From the repository root, run `scripts/profile-existing.sh [repetitions]`;
from another directory, use the path to that script. The default
is three repetitions; the allowed range is 1–99. Set `LEAN` and `GFORTH` to
executable paths or command names if they are not on `PATH`. Lean must match
the existing differential test's 4.35.0 version and exact git hash. Configure
any toolchain-specific environment yourself, for example `ELAN_HOME`; no home
directory or local installation layout is assumed. The script needs Bash,
standard Unix utilities, Git, SHA-256, Lean and Gforth; it adds no dependency.

Each repetition independently runs the existing Lean and Forth term-level
substitution tables. It verifies 48 rows, normalizes whitespace as the existing
differential test does, compares the two outputs, and checks consistency across
repetitions. Workload failure or output mismatch stops before the report;
a later metadata failure can leave a partial report. The report
contains individual elapsed times and peak process RSS, versions, platform,
revision, worktree status, input file hashes and normalized output hash.
Capture stdout to retain a record. Input hashes cover the wrapper and directly
included Forth sources, but not runtime binaries, toolchain libraries, or the
full environment; a dirty worktree needs additional provenance for reproduction.

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

A [local two-repetition sample](measurements/substitution-profile-2026-11-01.txt)
was run from the repository root with:

```sh
ELAN_HOME="$PWD/.tools/elan" libccnameddir=/tmp/leanforth-gforth-libcc \
  LEAN="$PWD/.tools/elan/bin/lean" GFORTH="$PWD/.tools/gforth/bin/gforth" \
  bash scripts/profile-existing.sh 2
```

The recorded worktree was dirty; the report includes source hashes and is not
a general performance comparison. It does not establish CI status or benchmark
trusted proof checking.

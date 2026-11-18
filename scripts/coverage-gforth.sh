#!/bin/sh
# Gforth with block coverage, for make coverage (scripts/coverage.py, which
# sets both variables). Runs LF_COVERAGE_GFORTH, a Gforth 1.0, with
# scripts/coverage-prelude.fs before the arguments it is given, so it can
# stand in for GFORTH in any test. Each run writes its block counts to a
# new file in LF_COVERAGE_DIR, and beside it its working directory (the
# counts name source files relative to it), the make target that ran it
# (LF_MAKE_TARGET, which scripts/timed.sh sets; empty without) and its
# arguments.
#
# It starts no process of its own before it becomes the strict wrapper
# (EXEC): under a process limit (`ulimit -u`) a refused fork here would end
# the run with the shell's own status, which reads as a Gforth failure; so
# the only way it fails to start Gforth is the strict wrapper's, which
# reports it (scripts/start-limit.sh). The count file is named by this
# process's number; one left by an earlier process of that number is never
# overwritten (noclobber), and mktemp names it then.
set -eu
case $0 in */*) here=${0%/*} ;; *) here=. ;; esac
case $here in /*) ;; *) here=$PWD/$here ;; esac
out=$LF_COVERAGE_DIR/run.$$
set -C
if ! { : >"$out"; } 2>/dev/null; then out=$(mktemp "$LF_COVERAGE_DIR/run.XXXXXX"); fi
set +C
printf '%s\n%s\n%s\n' "$PWD" "${LF_MAKE_TARGET:-}" "$*" >"$out.cwd"
LF_COVERAGE_OUT=$out
export LF_COVERAGE_OUT
# Through the strict wrapper (nonzero status after a reported error).
LEANFORTH_GFORTH=$LF_COVERAGE_GFORTH
export LEANFORTH_GFORTH
exec "$here/gforth-strict.sh" "$here/coverage-prelude.fs" "$@"

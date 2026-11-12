#!/bin/sh
# Gforth with block coverage, for make coverage (scripts/coverage.py, which
# sets both variables). Runs LF_COVERAGE_GFORTH, a Gforth 1.0, with
# scripts/coverage-prelude.fs before the arguments it is given, so it can
# stand in for GFORTH in any test. Each run writes its block counts to a
# new file in LF_COVERAGE_DIR, and beside it its working directory (the
# counts name source files relative to it) and its arguments.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
out=$(mktemp "$LF_COVERAGE_DIR/run.XXXXXX")
printf '%s\n%s\n' "$(pwd)" "$*" >"$out.cwd"
LF_COVERAGE_OUT=$out
export LF_COVERAGE_OUT
# Through the strict wrapper (nonzero status after a reported error).
LEANFORTH_GFORTH=$LF_COVERAGE_GFORTH
export LEANFORTH_GFORTH
exec "$here/gforth-strict.sh" "$here/coverage-prelude.fs" "$@"

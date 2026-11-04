#!/bin/bash
# Run Gforth so that a reported error always gives a nonzero exit status.
#
# Gforth 1.0 exits 0 after an uncaught error when the error report itself
# fails, e.g. while BASE is 0 (the report divides by BASE: "Division by
# zero"); Gforth 0.7.3 exits 1. A test that crashed that way would pass
# silently. This wrapper runs the real Gforth (named by $LEANFORTH_GFORTH,
# else .tools/gforth/bin/gforth of this checkout, else `gforth` on PATH),
# passes stdin, stdout and the arguments through, and exits 1 when Gforth
# exited 0 but its error output contains an error report: a "Backtrace:"
# line or "uncaught exception". Any other exit status is passed through.
# Stderr is replayed after the run ends (not live). The Makefile and
# scripts/mutants.py use this wrapper as $GFORTH for every Forth test run
# (docs/development/TESTING_STRATEGY.md, "Gforth exit status").
here=$(cd "$(dirname "$0")/.." && pwd)
real=${LEANFORTH_GFORTH:-}
if [ -z "$real" ]; then
  real=$here/.tools/gforth/bin/gforth
  [ -x "$real" ] || real=gforth
fi
errf=$(mktemp) || exit 1
trap 'rm -f "$errf"' EXIT
exec 9<&0
"$real" "$@" <&9 9<&- 2>"$errf" &
pid=$!
trap 'kill -TERM "$pid" 2>/dev/null' TERM INT HUP
wait "$pid"; status=$?
trap - TERM INT HUP
cat "$errf" >&2
if [ "$status" -eq 0 ] && grep -q -e '^Backtrace:' -e 'uncaught exception' "$errf"; then
  echo "gforth-strict: Gforth exited 0 after reporting an error" >&2
  exit 1
fi
exit "$status"

#!/usr/bin/env bash
# Runs Gforth with the derivation log's test preset (src/core/derivation-log.fs,
# ADR 0013), so that any existing test runs with the log on, or on and full:
#   LF_GFORTH=.tools/gforth/bin/gforth LF_LOG_LEVEL=2 LF_LOG_RECORDS=5 \
#     make test GFORTH=tests/support/gforth-log.sh
# LF_GFORTH names the real Gforth (default: gforth). LF_LOG_LEVEL (1 steps,
# 2 terms) switches the preset on: every context then logs every checker
# call, restarting a truncated log when its outermost rule ends.
# LF_LOG_RECORDS, LF_LOG_MARKS, LF_LOG_TERMS and LF_LOG_LEVELS set the
# limits (records, open rules, term and level copies). The preset is
# defined with -e before the first argument; --version passes through.
# LF_GFORTH must be the real Gforth, never a wrapper that runs this script
# again (scripts/gforth-strict.sh with LEANFORTH_GFORTH naming this file):
# a second level is refused with exit status 2 instead of forking forever.
# Test-only.
set -euo pipefail
if [ -n "${LF_LOG_WRAPPED:-}" ]; then
  echo "gforth-log.sh: LF_GFORTH (${LF_GFORTH:-gforth}) runs this script again;" \
    "name the real Gforth" >&2
  exit 2
fi
export LF_LOG_WRAPPED=1
real="${LF_GFORTH:-gforth}"
defs=""
add() { if [ -n "${2:-}" ]; then defs="$defs ${2} constant lf-log-preset-$1"; fi; }
add level "${LF_LOG_LEVEL:-}"
add records "${LF_LOG_RECORDS:-}"
add marks "${LF_LOG_MARKS:-}"
add terms "${LF_LOG_TERMS:-}"
add levels "${LF_LOG_LEVELS:-}"
case "${1:-}" in
  --version|-v) exec "$real" "$@" ;;
esac
if [ -z "$defs" ]; then exec "$real" "$@"; fi
exec "$real" -e "$defs" "$@"

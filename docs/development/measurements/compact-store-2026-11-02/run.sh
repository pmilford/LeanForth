#!/bin/bash
# Run the compact-store prototype (ADR 0016) on one export.
# Usage: run.sh ENGINE SECONDS FORTH-COMMANDS
#   ENGINE: gforth or gforth-fast from the pinned Gforth 1.0 in .tools/
#   (override the folder with GFORTH_BIN); MAIN=portable.fs forces the
#   Forth-2012 fallback of src/lib/u32.fs. Prints wall time, user time and
#   peak resident memory (/usr/bin/time). The address space is capped at
#   8 GiB, so an oversized run fails its ALLOCATE instead of swapping.
# Example: run.sh gforth-fast 2400 's" /path/init.ndjson" full bye'
set -u
ENGINE=$1; SECS=$2; shift 2
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(git -C "$HERE" rev-parse --show-toplevel)
BIN=${GFORTH_BIN:-$ROOT/.tools/gforth/bin}
cd "$HERE"
ulimit -v 8388608
exec /usr/bin/time -f "%e s wall %U s user %M KB" timeout -k 5 "$SECS" \
  "$BIN/$ENGINE" "${MAIN:-main.fs}" -e "$*" </dev/null

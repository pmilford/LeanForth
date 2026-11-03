#!/bin/bash
# Baseline for the load times: the reader alone (src/import/ndjson-count.fs),
# timed the same way as run.sh. Usage: count.sh EXPORT ENGINE
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(git -C "$HERE" rev-parse --show-toplevel)
BIN=${GFORTH_BIN:-$ROOT/.tools/gforth/bin}
cd "$ROOT"
exec /usr/bin/time -f "%e s wall %U s user %M KB" timeout -k 5 2400 \
  "$BIN/$2" src/import/ndjson-count.fs -e "s\" $1\" count-export bye" </dev/null

#!/bin/bash
# Verify the prototype's load of one export: the reader's own field dump
# (tests/core/ndjson-dump.fs) must equal the prototype's re-emission from
# the packed store, family by family: the name lines, the level lines and
# the expression lines, each in index order (the file interleaves the
# families; within a family both streams are in index order). Prints each
# family's line counts and SHA-256 and whether they agree.
# Usage: verify.sh EXPORT [ENGINE] [SECONDS]   (MAIN=portable.fs as in run.sh)
set -u
F=$1; ENGINE=${2:-gforth-fast}; SECS=${3:-2400}
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(git -C "$HERE" rev-parse --show-toplevel)
BIN=${GFORTH_BIN:-$ROOT/.tools/gforth/bin}
OUT=$(mktemp -d)
digests() {   # stdin: dump lines; $1: prefix of the output files
  tee >(grep -E '^name\.' | tee >(wc -l > "$1.name.n") | sha256sum > "$1.name.sha") \
      >(grep -E '^level\.' | tee >(wc -l > "$1.level.n") | sha256sum > "$1.level.sha") \
    | grep -E '^expr\.' | tee >(wc -l > "$1.expr.n") | sha256sum > "$1.expr.sha"
}
cd "$ROOT"
/usr/bin/time -f "reader dump: %e s %M KB" timeout -k 5 "$SECS" "$BIN/$ENGINE" \
  tests/core/ndjson-dump.fs -e "s\" $F\" dump-export bye" </dev/null 2>"$OUT/reader.err" \
  | digests "$OUT/reader"
tail -1 "$OUT/reader.err"
cd "$HERE"
/usr/bin/time -f "prototype re-emission: %e s %M KB" timeout -k 5 "$SECS" "$BIN/$ENGINE" \
  "${MAIN:-main.fs}" -e "s\" $F\" dump-file bye" </dev/null 2>"$OUT/proto.err" \
  | digests "$OUT/proto"
tail -1 "$OUT/proto.err"; sleep 2
for fam in name level expr; do
  a=$(cut -c1-64 "$OUT/reader.$fam.sha"); b=$(cut -c1-64 "$OUT/proto.$fam.sha")
  na=$(cat "$OUT/reader.$fam.n"); nb=$(cat "$OUT/proto.$fam.n")
  if [ "$a" = "$b" ] && [ "$na" = "$nb" ]; then r=EQUAL; else r=DIFFERENT; fi
  echo "$fam: $r lines $na/$nb sha256 $a / $b"
done
echo "(work files in $OUT)"

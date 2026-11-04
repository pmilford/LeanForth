#!/usr/bin/env bash
# Verify a load into the compact store (ADR 0016, src/core/compact.fs):
# the reader's own field dump (tests/core/ndjson-dump.fs) must equal the
# compact store's re-emission (tests/support/compact-load.fs), family by
# family -- the name lines, the level lines and the expression lines, each
# in index order (the file interleaves the families; within a family both
# streams are in index order). Prints each family's line count and SHA-256
# and whether they agree; exits 1 when any family differs or a run fails.
# Usage: compact-verify.sh EXPORT [GFORTH] [SECONDS]
#   GFORTH: the engine to run (default: $GFORTH, else .tools/gforth/bin/gforth)
set -u
export_file=$1
gforth=${2:-${GFORTH:-.tools/gforth/bin/gforth}}
seconds=${3:-600}
work=$(mktemp -d)
trap 'rm -f "$work"/reader.* "$work"/store.*; rmdir "$work"' EXIT
digests() {   # stdin: dump lines; $1: prefix of the output files
  tee >(grep -E '^name\.' | tee >(wc -l > "$1.name.n") | sha256sum > "$1.name.sha") \
      >(grep -E '^level\.' | tee >(wc -l > "$1.level.n") | sha256sum > "$1.level.sha") \
    | grep -E '^expr\.' | tee >(wc -l > "$1.expr.n") | sha256sum > "$1.expr.sha"
}
timeout -k 5 "$seconds" "$gforth" tests/core/ndjson-dump.fs \
  -e "s\" $export_file\" dump-export bye" </dev/null 2>"$work/reader.err" | digests "$work/reader"
timeout -k 5 "$seconds" "$gforth" tests/support/compact-load.fs \
  -e "s\" $export_file\" compact-dump bye" </dev/null 2>"$work/store.err" | digests "$work/store"
sleep 1
status=0
for family in name level expr; do
  a=$(cut -c1-64 "$work/reader.$family.sha"); b=$(cut -c1-64 "$work/store.$family.sha")
  na=$(tr -d ' ' < "$work/reader.$family.n"); nb=$(tr -d ' ' < "$work/store.$family.n")
  if [ "$a" = "$b" ] && [ "$na" = "$nb" ]; then verdict=EQUAL; else verdict=DIFFERENT; status=1; fi
  echo "$family: $verdict lines $na/$nb sha256 $a / $b"
done
for side in reader store; do
  if [ -s "$work/$side.err" ]; then echo "$side printed to stderr:"; head -5 "$work/$side.err"; status=1; fi
done
exit $status

#!/usr/bin/env bash
# Verify a load into the compact store with the importer stage (ADR 0016,
# src/import/stage.fs): the reader's own field dump (tests/core/ndjson-dump.fs)
# must equal the stage's re-emission (tests/support/compact-load.fs), family
# by family -- the metadata line, the name lines, the level lines, the
# expression lines and the declaration lines (decl.* and the inductive
# blocks' ind.* elements), each in file order (the file interleaves the
# families; within a family both streams are in file order). The reader's
# dump must hold nothing else but its final "ok". Prints each family's line
# count and SHA-256 and whether they agree; exits 1 when any family
# differs or a run fails.
# The stage checks the export's manifest (EXPORT.manifest.json) by default;
# --unchecked loads without one, an explicit choice for exports that have
# none. The reader's dump never checks a manifest.
# Usage: compact-verify.sh [--unchecked] EXPORT [GFORTH] [SECONDS]
#   GFORTH: the engine to run (default: $GFORTH, else .tools/gforth/bin/gforth)
set -u
dump=compact-dump
if [ "${1:-}" = "--unchecked" ]; then dump=compact-dump-unchecked; shift; fi
export_file=$1
gforth=${2:-${GFORTH:-.tools/gforth/bin/gforth}}
seconds=${3:-600}
work=$(mktemp -d)
families="meta name level expr decl"
trap 'for f in $families other; do rm -f "$work"/reader.$f "$work"/store.$f; done
      rm -f "$work"/reader.err "$work"/store.err; rmdir "$work"' EXIT
split() {   # stdin: dump lines; $1: prefix of the family files
  awk -v p="$1" '
    /^meta /                { print > (p ".meta"); next }
    /^name\./               { print > (p ".name"); next }
    /^level\./              { print > (p ".level"); next }
    /^expr\./               { print > (p ".expr"); next }
    /^(decl|ind)\./         { print > (p ".decl"); next }
    $0 == "ok"              { next }
                            { print > (p ".other") }'
  for f in $families other; do touch "$1.$f"; done
}
# The two runs are independent: run them side by side and wait for both.
timeout -k 5 "$seconds" "$gforth" tests/core/ndjson-dump.fs \
  -e "s\" $export_file\" dump-export bye" </dev/null 2>"$work/reader.err" | split "$work/reader" &
timeout -k 5 "$seconds" "$gforth" tests/support/compact-load.fs \
  -e "s\" $export_file\" $dump bye" </dev/null 2>"$work/store.err" | split "$work/store" &
wait
status=0
for family in $families; do
  a=$(sha256sum < "$work/reader.$family" | cut -c1-64); b=$(sha256sum < "$work/store.$family" | cut -c1-64)
  na=$(wc -l < "$work/reader.$family"); nb=$(wc -l < "$work/store.$family")
  if [ "$a" = "$b" ] && [ "$na" = "$nb" ] && [ "$na" -gt 0 -o "$family" != meta ]; then
    verdict=EQUAL
  else verdict=DIFFERENT; status=1; fi
  echo "$family: $verdict lines $na/$nb sha256 $a / $b"
done
for side in reader store; do
  if [ -s "$work/$side.other" ]; then echo "$side printed other lines:"; head -5 "$work/$side.other"; status=1; fi
  if [ -s "$work/$side.err" ]; then echo "$side printed to stderr:"; head -5 "$work/$side.err"; status=1; fi
done
exit $status

#!/usr/bin/env bash
# One re-export measurement (README.md here): the Forth re-export of EXPORT
# into OUT/NAME.copy.ndjson with /usr/bin/time -v, then SHA-256 and cmp of
# both files and, with REIMPORT=1, the reader's field-by-field dump of each
# (tests/core/ndjson-dump.fs) through sha256sum. Appends to OUT/NAME.log.
# Usage, from the repository root:
#   docs/development/measurements/reexport-2026-11-03/measure.sh NAME EXPORT OUT
# G names the Forth system (default .tools/gforth/bin/gforth-fast); TO the
# timeout of each step in seconds (default 1800). The copy is kept; delete
# it by name afterwards.
set -u
[ $# -eq 3 ] || { printf 'usage: %s NAME EXPORT OUT\n' "$0" >&2; exit 2; }
name=$1 source_file=$2 out=$3
copy=$out/$name.copy.ndjson
forth=${G:-.tools/gforth/bin/gforth-fast}
limit=${TO:-1800}
{
  printf '== %s %s %s\n' "$name" "$(date -Is)" "$forth"
  timeout -k 5 "$limit" /usr/bin/time -v -o "$out/$name.time" "$forth" \
    src/import/ndjson-emit.fs -e "s\" $source_file\" s\" $copy\" reexport bye" </dev/null
  printf 'forth exit %s\n' "$?"
  grep -E 'Elapsed|Maximum resident|User time|System time' "$out/$name.time"
  sha256sum "$source_file" "$copy"
  wc -lc "$source_file" "$copy"
  cmp "$source_file" "$copy" && printf 'cmp: identical\n'
  if [ "${REIMPORT:-0}" = 1 ]; then
    for file in "$source_file" "$copy"; do
      timeout -k 5 "$limit" /usr/bin/time -v -o "$out/$name.dump.time" "$forth" \
        tests/core/ndjson-dump.fs -e "s\" $file\" dump-export bye" </dev/null | sha256sum
      grep -E 'Elapsed|Maximum resident' "$out/$name.dump.time"
    done
  fi
  printf '== end %s\n' "$(date -Is)"
} >>"$out/$name.log" 2>&1

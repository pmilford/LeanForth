#!/usr/bin/env bash
# Round trip of a Lean NDJSON export through LeanForth (plan task 3.2.4;
# docs/development/NDJSON_READER.md, "Re-export"): read EXPORT with the
# Forth reader, write every record back with the Forth re-exporter
# (src/import/ndjson-emit.fs) into COPY, and compare COPY with EXPORT by
# SHA-256 and byte for byte. Prints both SHA-256 sums, then "identical",
# or the first differing line, the byte within it and both lines around
# it. With --reimport, COPY is then read again with the reader and its
# field-by-field dump (tests/core/ndjson-dump.fs) compared with EXPORT's.
#
# Usage, from the repository root:
#   scripts/ndjson-reexport.sh [--reimport] EXPORT COPY
#   scripts/ndjson-reexport.sh EXPORT -        stream: no copy is kept
# Exit status: 0 identical (and equal dumps); 1 different, or a step
# failed; 2 bad usage. GFORTH names the Forth system (default: the pinned
# gforth-fast, else gforth-fast on PATH). COPY is created or overwritten
# and must not be EXPORT; file names may not hold a double quote. The
# script writes nothing else but temporary files, deleted by name.
set -u

usage() {
  printf 'usage: %s [--reimport] EXPORT COPY|-\n' "$0" >&2
  exit 2
}
reimport=false
if [ "${1:-}" = --reimport ]; then reimport=true; shift; fi
[ $# -eq 2 ] || usage
source_file=$1
copy=$2
if [ -z "${GFORTH:-}" ]; then
  GFORTH=.tools/gforth/bin/gforth-fast
  [ -x "$GFORTH" ] || GFORTH=gforth-fast
fi
case "$source_file$copy" in
  *'"'*) printf 'file names may not hold a double quote\n' >&2; exit 2 ;;
esac
[ -f "$source_file" ] || { printf 'no such file: %s\n' "$source_file" >&2; exit 2; }
if [ "$copy" = - ]; then
  $reimport && { printf -- '--reimport needs a COPY file\n' >&2; exit 2; }
elif [ -e "$copy" ] && [ "$(realpath "$source_file")" = "$(realpath "$copy")" ]; then
  printf 'COPY must not be EXPORT\n' >&2
  exit 2
fi

temporary=$(mktemp -d)
trap 'rm -f "$temporary/copy-fifo" "$temporary/cmp" "$temporary/sum"; rmdir "$temporary"' EXIT

# Re-export into the file named $1; the tool prints one line.
reexport() {
  "$GFORTH" src/import/ndjson-emit.fs -e "s\" $source_file\" s\" $1\" reexport bye" </dev/null
}
sum_of() { sha256sum <"$1" | cut -d' ' -f1; }

# Line $1 of file $2, from about 60 bytes before byte $3 of it, 160 bytes.
excerpt() {
  local from=$(( $3 > 60 ? $3 - 60 : 1 ))
  sed -n "$1{p;q}" "$2" | tail -c "+$from" | head -c 160 | tr -d '\n'
  printf '\n'
}
# Explain cmp's message $1: the first differing byte and its line, or
# which file ended first.
report() {
  local byte line before column
  byte=$(printf '%s' "$1" | sed -n 's/.*byte \([0-9]*\).*/\1/p')
  line=$(printf '%s' "$1" | sed -n 's/.*line \([0-9]*\).*/\1/p')
  case "$1" in
    *EOF*) printf 'different: %s\n' "${1#cmp: }"; return ;;
  esac
  if [ -z "$byte" ] || [ -z "$line" ]; then printf 'different: %s\n' "$1"; return; fi
  before=$(head -n "$((line - 1))" "$source_file" | wc -c)
  column=$((byte - before))
  printf 'different: first at line %s, byte %s of the line (byte %s of the file)\n' \
    "$line" "$column" "$byte"
  printf 'export: '; excerpt "$line" "$source_file" "$column"
  [ "$copy" != - ] && { printf 'copy:   '; excerpt "$line" "$copy" "$column"; }
}

status=0
printf 'export %s\n' "$(sum_of "$source_file")"
if [ "$copy" = - ]; then
  mkfifo "$temporary/copy-fifo"
  cmp "$source_file" "$temporary/copy-fifo" >"$temporary/cmp" 2>&1 &
  cmp_pid=$!
  reexport /dev/fd/3 3>&1 1>&2 | tee -p "$temporary/copy-fifo" | sha256sum | cut -d' ' -f1 \
    >"$temporary/sum"
  forth_status=${PIPESTATUS[0]}
  wait "$cmp_pid"
  cmp_status=$?
  printf 'copy   %s\n' "$(cat "$temporary/sum")"
else
  reexport "$copy"
  forth_status=$?
  cmp "$source_file" "$copy" >"$temporary/cmp" 2>&1
  cmp_status=$?
  printf 'copy   %s\n' "$(sum_of "$copy")"
fi
if [ "$forth_status" -ne 0 ]; then
  printf 'the re-export failed (status %s)\n' "$forth_status"
  status=1
fi
if [ "$cmp_status" -eq 0 ]; then
  printf 'identical\n'
else
  report "$(cat "$temporary/cmp")"
  status=1
fi

# Read both files with the reader and compare their dumps.
dump_sum() {
  "$GFORTH" tests/core/ndjson-dump.fs -e "s\" $1\" dump-export bye" </dev/null \
    | sha256sum | cut -d' ' -f1
}
if $reimport; then
  dump_export=$(dump_sum "$source_file")
  dump_copy=$(dump_sum "$copy")
  printf 'dump of export %s\ndump of copy   %s\n' "$dump_export" "$dump_copy"
  if [ "$dump_export" = "$dump_copy" ]; then
    printf 'reimport: equal dumps\n'
  else
    printf 'reimport: the dumps differ\n'
    status=1
  fi
fi
exit "$status"

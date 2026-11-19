#!/usr/bin/env bash
set -eu
. "$(dirname "${BASH_SOURCE[0]}")/../support/pinned-lean.sh"
gforth=${GFORTH:-gforth}
case "$("$lean" --version)" in
  'Lean (version 4.35.0,'*) ;;
  *) printf '%s\n' 'Expected Lean 4.35.0' >&2; exit 1 ;;
esac
if [ "$("$lean" --githash)" != eb6cafb7290e8bd5f2937522d8d804f58f02bafc ]; then
  printf '%s\n' 'Unexpected Lean revision' >&2
  exit 1
fi
temporary=$(mktemp -d)
trap 'rm -f "$temporary/lean.txt" "$temporary/forth.txt"; rmdir "$temporary"' EXIT
"$lean" -DwarningAsError=true --run tests/reference/stack-clamp.lean >"$temporary/lean.txt"
"$gforth" tests/program/clamp-table.fs >"$temporary/forth.txt"
if [ "$(wc -l <"$temporary/lean.txt")" -ne 686 ] ||
   ! cmp -s "$temporary/lean.txt" "$temporary/forth.txt"; then
  printf '%s\n' 'Lean stack model and Forth execution differ' >&2
  diff -u "$temporary/lean.txt" "$temporary/forth.txt" >&2 || true
  exit 1
fi
printf '%s\n' 'Lean stack model and Forth agree on 686 selected input triples.'

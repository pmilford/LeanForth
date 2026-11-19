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
trap 'rm -f "$temporary/lean.txt" "$temporary/forth.txt" "$temporary/lean-normalized.txt" "$temporary/forth-normalized.txt"; rmdir "$temporary"' EXIT
"$lean" -DwarningAsError=true --run tests/reference/level-substitute-table.lean >"$temporary/lean.txt"
"$gforth" tests/core/level-substitute-table.fs >"$temporary/forth.txt"
if [ "$(wc -l <"$temporary/lean.txt")" -ne 48 ] ||
   [ "$(wc -l <"$temporary/forth.txt")" -ne 48 ]; then
  printf '%s\n' 'Unexpected substitution table length' >&2
  exit 1
fi
awk '{$1=$1; print}' "$temporary/lean.txt" >"$temporary/lean-normalized.txt"
awk '{$1=$1; print}' "$temporary/forth.txt" >"$temporary/forth-normalized.txt"
if ! cmp -s "$temporary/lean-normalized.txt" "$temporary/forth-normalized.txt"; then
  diff -u "$temporary/lean-normalized.txt" "$temporary/forth-normalized.txt" >&2 || true
  exit 1
fi
printf '%s\n' 'Lean and Forth agree on 48 finite observations of simultaneous level substitution.'

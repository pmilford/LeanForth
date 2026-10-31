#!/usr/bin/env bash
set -eu
lean=${LEAN:-lean}
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
"$lean" --run tests/reference/level-compare-table.lean >"$temporary/lean.txt"
"$gforth" tests/core/level-compare-table.fs >"$temporary/forth.txt"
if ! paste "$temporary/lean.txt" "$temporary/forth.txt" | awk '
  NF != 4 || $1 != NR - 1 || $3 != $1 { exit 1 }
  (NR == 1 || NR == 2 || NR == 5) && ($2 != 1 || $4 != 0) { exit 1 }
  (NR == 3 || NR == 6) && ($2 != 0 || $4 != 3) { exit 1 }
  (NR == 4 || NR == 7 || NR == 8) && ($2 != 1 || $4 != 3) { exit 1 }
  END { if (NR != 8) exit 1 }
'; then
  printf '%s\n' 'Level comparison results differ from expectations' >&2
  paste "$temporary/lean.txt" "$temporary/forth.txt" >&2
  exit 1
fi
printf '%s\n' 'Three Forth equalities match Lean; five cases remain unknown, including three Lean equalities.'

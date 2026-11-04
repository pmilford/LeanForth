#!/usr/bin/env bash
# Level comparison against pinned Lean 4.35.0's kernel (ADR 0011,
# Amendment 1): the fifteen fixed cases of level-compare-table.lean, where
# LeanForth must answer ok (0) exactly where Lean's kernel finds the
# levels equal and unknown (3) where it does not; then random level pairs
# (level-kernel-differential.py) for is_equivalent, mk_max and mk_imax.
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
"$lean" -DwarningAsError=true tests/reference/level-compare-table.lean >"$temporary/lean.txt"
"$gforth" tests/core/level-compare-table.fs >"$temporary/forth.txt"
if ! paste "$temporary/lean.txt" "$temporary/forth.txt" | awk '
  NF != 4 || $1 != NR - 1 || $3 != $1 { exit 1 }
  !(($2 == 1 && $4 == 0) || ($2 == 0 && $4 == 3)) { exit 1 }
  $2 == 1 { equal++ }
  END { if (NR != 15 || equal != 12) exit 1 }
'; then
  printf '%s\n' 'Level comparison results differ from Lean' >&2
  paste "$temporary/lean.txt" "$temporary/forth.txt" >&2
  exit 1
fi
printf '%s\n' 'Fifteen level comparisons match Lean'"'"'s kernel: twelve equal, three not.'
LEAN=$lean GFORTH=$gforth python3 tests/core/level-kernel-differential.py

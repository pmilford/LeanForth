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
"$lean" -DwarningAsError=true --run tests/reference/name-table.lean >"$temporary/lean.txt"
"$gforth" tests/core/name-table.fs >"$temporary/forth.txt"
if [ "$(wc -l <"$temporary/lean.txt")" -ne 9 ] ||
   ! paste "$temporary/lean.txt" "$temporary/forth.txt" | awk '
     NF != 4 || $1 != NR - 1 || $1 != $3 || $2 != $4 { exit 1 }
     END { if (NR != 9) exit 1 }
   '; then
  printf '%s\n' 'Lean and Forth structured-name results differ' >&2
  paste "$temporary/lean.txt" "$temporary/forth.txt" >&2
  exit 1
fi
printf '%s\n' 'Lean and Forth agree on nine structured-name equality cases.'

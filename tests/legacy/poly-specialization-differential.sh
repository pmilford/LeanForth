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
trap 'rm -f "$temporary/LeanForthPolyIdentity.olean" "$temporary/lean.txt" "$temporary/forth.txt"; rmdir "$temporary"' EXIT
"$lean" -DwarningAsError=true -o "$temporary/LeanForthPolyIdentity.olean" tests/reference/poly-identity.lean
LEAN_PATH="$temporary" "$lean" -DwarningAsError=true tests/legacy/poly-specialization-table.lean >"$temporary/lean.txt"
GFORTH="$gforth" python3 tests/legacy/poly-specialization-table.py >"$temporary/forth.txt"
if ! paste "$temporary/lean.txt" "$temporary/forth.txt" | awk '
  NF != 10 || $1 != $6 || $2 != $7 || $1 != int((NR - 1) / 2) || $2 != (NR - 1) % 2 { exit 1 }
  $4 != $9 || $5 != $10 { exit 1 }
  $2 == 0 && ($3 != 0 || $8 != 0) { exit 1 }
  $2 == 1 && ($3 != 1 || ($8 != 1 && $8 != 3)) { exit 1 }
  END { if (NR != 8) exit 1 }
'; then
  printf '%s\n' 'Specialized declaration results differ from expectations' >&2
  paste "$temporary/lean.txt" "$temporary/forth.txt" >&2
  exit 1
fi
printf '%s\n' 'Lean and Forth specialized shapes match for four instances; altered values do not succeed.'

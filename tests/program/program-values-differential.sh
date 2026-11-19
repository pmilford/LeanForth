#!/usr/bin/env bash
# Finite comparison only; it does not prove the Forth host or any program.
set -eu
. "$(dirname "${BASH_SOURCE[0]}")/../support/pinned-lean.sh"
gforth=${GFORTH:-gforth}
case $("$lean" --version) in
  'Lean (version 4.35.0,'*) ;;
  *) printf '%s\n' 'Expected Lean 4.35.0' >&2; exit 1 ;;
esac
[ "$("$lean" --githash)" = eb6cafb7290e8bd5f2937522d8d804f58f02bafc ] || {
  printf '%s\n' 'Unexpected Lean revision' >&2; exit 1;
}
temporary=$(mktemp -d)
trap 'rm -f "$temporary/ProgramContracts.olean" "$temporary/lean.txt" "$temporary/forth.txt"; rmdir "$temporary"' EXIT
"$lean" -DwarningAsError=true -o "$temporary/ProgramContracts.olean" tests/reference/program-contracts.lean
LEAN_PATH="$temporary" "$lean" -DwarningAsError=true --run tests/reference/program-values-table.lean >"$temporary/lean.txt"
"$gforth" tests/program/program-values-table.fs >"$temporary/forth.txt"
[ "$(wc -l <"$temporary/lean.txt")" -eq 15624 ] &&
[ "$(wc -l <"$temporary/forth.txt")" -eq 15624 ] || {
  printf '%s\n' 'Unexpected execution table size' >&2; exit 1;
}
diff -u "$temporary/lean.txt" "$temporary/forth.txt"
printf '%s\n' 'Actual Forth stack values match the Lean model on 15,624 bounded cases.'

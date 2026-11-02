#!/usr/bin/env bash
# Run from the repository root. Finite comparison, not a runtime proof.
set -eu
lean=${LEAN:-lean}
gforth=${GFORTH:-gforth}
version=$("$lean" --version)
case "$version" in
  'Lean (version 4.35.0,'*) ;;
  *) printf 'Expected Lean 4.35.0; got: %s\n' "$version" >&2; exit 1 ;;
esac
[ "$("$lean" --githash)" = eb6cafb7290e8bd5f2937522d8d804f58f02bafc ] || {
  printf '%s\n' 'Unexpected Lean revision' >&2; exit 1;
}
temporary=$(mktemp -d)
trap 'rm -f "$temporary/CheckedAdd.olean" "$temporary/lean.txt" "$temporary/forth.txt"; rmdir "$temporary"' EXIT
"$lean" -DwarningAsError=true -o "$temporary/CheckedAdd.olean" tests/reference/checked-add.lean
LEAN_PATH="$temporary" "$lean" -DwarningAsError=true --run tests/reference/add-reference-table.lean >"$temporary/lean.txt"
"$gforth" tests/program/add-reference-table.fs >"$temporary/forth.txt"
[ "$(wc -l <"$temporary/lean.txt")" -eq 410 ] &&
[ "$(wc -l <"$temporary/forth.txt")" -eq 410 ] || {
  printf '%s\n' 'Unexpected execution table size' >&2; exit 1;
}
diff -u "$temporary/lean.txt" "$temporary/forth.txt"
printf '%s\n' 'checked-add agrees with Lean for 410 pairs on a 64-bit cell host; stack sentinel preserved.'

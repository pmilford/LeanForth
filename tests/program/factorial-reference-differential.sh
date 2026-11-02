#!/usr/bin/env bash
# Run from the repository root. Finite comparison, not Forth runtime proof.
# LEAN and GFORTH select binaries; Lean's toolchain environment must be set.
set -eu
lean=${LEAN:-lean}
gforth=${GFORTH:-gforth}
version=$("$lean" --version)
case "$version" in
  'Lean (version 4.35.0,'*) ;;
  *) printf 'Expected Lean 4.35.0; got: %s\n' "$version" >&2; exit 1 ;;
esac
revision=$("$lean" --githash)
[ "$revision" = eb6cafb7290e8bd5f2937522d8d804f58f02bafc ] || {
  printf 'Unexpected Lean revision: %s\n' "$revision" >&2; exit 1;
}
version=$("$gforth" --version 2>&1)
case "$version" in
  'gforth 1.0.0 '*) ;;
  *) printf 'Expected Gforth 1.0.0; got: %s\n' "$version" >&2; exit 1 ;;
esac
temporary=$(mktemp -d)
trap 'rm -f "$temporary/FactorialReference.olean" "$temporary/lean.txt" "$temporary/forth.txt"; rmdir "$temporary"' EXIT
"$lean" -DwarningAsError=true -o "$temporary/FactorialReference.olean" tests/reference/factorial-reference.lean
LEAN_PATH="$temporary" "$lean" -DwarningAsError=true --run tests/reference/factorial-table.lean >"$temporary/lean.txt"
"$gforth" tests/program/factorial-reference-table.fs >"$temporary/forth.txt"
[ "$(wc -l <"$temporary/lean.txt")" -eq 152 ] &&
[ "$(wc -l <"$temporary/forth.txt")" -eq 152 ] || {
  printf '%s\n' 'Unexpected factorial table size' >&2; exit 1;
}
diff -u "$temporary/lean.txt" "$temporary/forth.txt"
printf '%s\n' 'lf-factorial agrees with the Lean model on 152 finite 64-bit inputs, including 20 and the first overflow at 21.'

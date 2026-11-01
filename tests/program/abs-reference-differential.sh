#!/usr/bin/env bash
# From repository root. This is finite differential testing, not runtime proof.
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
temporary=$(mktemp -d)
trap 'rm -f "$temporary/ProgramExamples.olean" "$temporary/lean.txt" "$temporary/forth.txt"; rmdir "$temporary"' EXIT
"$lean" -o "$temporary/ProgramExamples.olean" tests/reference/program-examples.lean
LEAN_PATH="$temporary" "$lean" --run tests/reference/abs-reference-table.lean >"$temporary/lean.txt"
"$gforth" tests/program/abs-reference-table.fs >"$temporary/forth.txt"
[ "$(wc -l <"$temporary/lean.txt")" -eq 263 ] &&
[ "$(wc -l <"$temporary/forth.txt")" -eq 263 ] || {
  printf '%s\n' 'Unexpected execution table size' >&2; exit 1;
}
diff -u "$temporary/lean.txt" "$temporary/forth.txt"
printf '%s\n' 'lf-checked-abs agrees with the Lean model for 263 small-domain and signed 64-bit boundary inputs.'

#!/usr/bin/env bash
# Run from the repository root. Finite tests do not prove runtime behavior.
set -eu
lean=${LEAN:-lean}
gforth=${GFORTH:-gforth}
case "$("$lean" --version)" in
  'Lean (version 4.35.0,'*) ;;
  *) printf '%s\n' 'Expected Lean 4.35.0' >&2; exit 1 ;;
esac
[ "$("$lean" --githash)" = eb6cafb7290e8bd5f2937522d8d804f58f02bafc ] || {
  printf '%s\n' 'Unexpected Lean revision' >&2; exit 1;
}
temporary=$(mktemp -d)
trap 'rm -f "$temporary/ProgramExamples.olean" "$temporary/lean.txt" "$temporary/forth.txt"; rmdir "$temporary"' EXIT
"$lean" -o "$temporary/ProgramExamples.olean" tests/reference/program-examples.lean
LEAN_PATH="$temporary" "$lean" --run tests/reference/extra-program-range-table.lean >"$temporary/lean.txt"
"$gforth" tests/program/extra-program-range-table.fs >"$temporary/forth.txt"
[ "$(wc -l <"$temporary/lean.txt")" -eq 343 ] &&
[ "$(wc -l <"$temporary/forth.txt")" -eq 343 ] || {
  printf '%s\n' 'Unexpected range table size' >&2; exit 1;
}
diff -u "$temporary/lean.txt" "$temporary/forth.txt"
printf '%s\n' 'lf-in-range agrees with Lean on 343 signed 64-bit boundary triples; flags and stack shape checked.'

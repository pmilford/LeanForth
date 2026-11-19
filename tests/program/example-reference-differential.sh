#!/usr/bin/env bash
# Run from the repository root. Finite testing is not a proof of the host.
set -eu
. "$(dirname "${BASH_SOURCE[0]}")/../support/pinned-lean.sh"
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
"$lean" -DwarningAsError=true -o "$temporary/ProgramExamples.olean" tests/reference/program-examples.lean
LEAN_PATH="$temporary" "$lean" -DwarningAsError=true --run tests/reference/example-reference-table.lean >"$temporary/lean.txt"
"$gforth" tests/program/example-reference-table.fs >"$temporary/forth.txt"
[ "$(wc -l <"$temporary/lean.txt")" -eq 686 ] &&
[ "$(wc -l <"$temporary/forth.txt")" -eq 686 ] || {
  printf '%s\n' 'Unexpected execution table size' >&2; exit 1;
}
diff -u "$temporary/lean.txt" "$temporary/forth.txt"
printf '%s\n' 'lf-in-range agrees with the Lean reference for 686 small-domain and signed 32-bit boundary triples.'

#!/usr/bin/env bash
# Finite model/runtime comparison; this does not prove Forth execution.
set -eu
. "$(dirname "${BASH_SOURCE[0]}")/../support/pinned-lean.sh"
gforth=${GFORTH:-gforth}
case "$("$lean" --version)" in
  'Lean (version 4.35.0,'*) ;;
  *) printf '%s\n' 'Expected Lean 4.35.0' >&2; exit 1 ;;
esac
[ "$("$lean" --githash)" = eb6cafb7290e8bd5f2937522d8d804f58f02bafc ] || exit 1
temporary=$(mktemp -d)
trap 'rm -f "$temporary/GcdReference.olean" "$temporary/lean.txt" "$temporary/forth.txt"; rmdir "$temporary"' EXIT
"$lean" -DwarningAsError=true -o "$temporary/GcdReference.olean" tests/reference/gcd-reference.lean >/dev/null
LEAN_PATH="$temporary" "$lean" -DwarningAsError=true --run tests/reference/gcd-table.lean >"$temporary/lean.txt"
"$gforth" tests/program/gcd-reference-table.fs >"$temporary/forth.txt"
[ "$(wc -l <"$temporary/lean.txt")" -eq 150 ] && [ "$(wc -l <"$temporary/forth.txt")" -eq 150 ] || exit 1
diff -u "$temporary/lean.txt" "$temporary/forth.txt"
printf '%s\n' 'lf-gcd agrees with the Lean model on 150 finite input pairs.'

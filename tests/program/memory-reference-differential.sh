#!/usr/bin/env bash
# Run at repository root; finite test-only comparison, not runtime proof.
set -eu
lean=${LEAN:-.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean}
gforth=${GFORTH:-.tools/gforth/bin/gforth}
case "$("$lean" --version)" in 'Lean (version 4.35.0,'*) ;; *) echo 'Expected Lean 4.35.0' >&2; exit 1;; esac
[ "$("$lean" --githash)" = eb6cafb7290e8bd5f2937522d8d804f58f02bafc ] || exit 1
case "$("$gforth" --version 2>&1)" in 'gforth 1.0.0 '*) ;; *) echo 'Expected Gforth 1.0.0' >&2; exit 1;; esac
temporary=$(mktemp -d)
trap 'rm -f "$temporary/program-contracts.olean" "$temporary/memory-program-reference.olean" "$temporary/lean.txt" "$temporary/forth.txt"; rmdir "$temporary"' EXIT
"$lean" -DwarningAsError=true -o "$temporary/program-contracts.olean" tests/reference/program-contracts.lean
LEAN_PATH="$temporary" "$lean" -DwarningAsError=true -o "$temporary/memory-program-reference.olean" tests/reference/memory-program-reference.lean
LEAN_PATH="$temporary" "$lean" -DwarningAsError=true --run tests/reference/memory-reference-table.lean >"$temporary/lean.txt"
"$gforth" tests/program/memory-reference-table.fs >"$temporary/forth.txt"
[ "$(wc -l <"$temporary/lean.txt")" -eq 28 ] &&
[ "$(wc -l <"$temporary/forth.txt")" -eq 28 ] || {
  printf '%s\n' 'Unexpected memory table size' >&2; exit 1;
}
diff -u "$temporary/lean.txt" "$temporary/forth.txt"
printf '%s\n' '28 bounded memory cases agree; this is not a proof of Forth execution.'

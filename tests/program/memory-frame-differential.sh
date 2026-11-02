#!/usr/bin/env bash
# Run from the repository root; finite comparison, not a proof of execution.
set -eu
lean=${LEAN:-.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean}
gforth=${GFORTH:-.tools/gforth/bin/gforth}
case "$("$lean" --version)" in 'Lean (version 4.35.0,'*) ;; *) echo 'Expected Lean 4.35.0' >&2; exit 1;; esac
[ "$("$lean" --githash)" = eb6cafb7290e8bd5f2937522d8d804f58f02bafc ] || { echo 'Unexpected Lean commit' >&2; exit 1; }
case "$("$gforth" --version 2>&1)" in 'gforth 1.0.0 '*) ;; *) echo 'Expected Gforth 1.0.0' >&2; exit 1;; esac
temporary=$(mktemp -d)
trap 'rm -rf "$temporary"' EXIT
"$lean" -o "$temporary/program-contracts.olean" tests/reference/program-contracts.lean
LEAN_PATH="$temporary" "$lean" -o "$temporary/memory-program-reference.olean" tests/reference/memory-program-reference.lean
LEAN_PATH="$temporary" "$lean" -o "$temporary/memory-copy-reference.olean" tests/reference/memory-copy-reference.lean
LEAN_PATH="$temporary" "$lean" -o "$temporary/memory-swap-reference.olean" tests/reference/memory-swap-reference.lean
LEAN_PATH="$temporary" "$lean" --run tests/reference/memory-frame-differential.lean >"$temporary/lean.txt"
"$gforth" tests/program/memory-frame-differential.fs >"$temporary/forth.txt"
if [ "$(wc -l <"$temporary/lean.txt")" -ne 1296 ] ||
   [ "$(wc -l <"$temporary/forth.txt")" -ne 1296 ]; then
  printf '%s\n' 'Unexpected copy-then-swap observation count' >&2
  exit 1
fi
diff -u "$temporary/lean.txt" "$temporary/forth.txt"
printf '%s\n' '1296 copy-then-swap observations agree; this is not a proof of Forth execution.'

#!/usr/bin/env bash
# Finite syntax comparison only; this is not a kernel correctness proof.
set -eu
. "$(dirname "${BASH_SOURCE[0]}")/../support/pinned-lean.sh"
gforth=${GFORTH:-gforth}
version=$("$lean" --version)
case "$version" in 'Lean (version 4.35.0,'*) ;; *) printf 'Unexpected Lean: %s\n' "$version" >&2; exit 1 ;; esac
if [ "$("$lean" --githash)" != eb6cafb7290e8bd5f2937522d8d804f58f02bafc ]; then
  printf '%s\n' 'Unexpected Lean revision' >&2; exit 1
fi
temporary=$(mktemp -d)
trap 'rm -f "$temporary/lean.txt" "$temporary/forth.txt"; rmdir "$temporary"' EXIT
"$lean" -DwarningAsError=true --run tests/reference/mixed-shift-table.lean >"$temporary/lean.txt"
"$gforth" tests/core/mixed-shift-table.fs >"$temporary/forth.txt"
if ! cmp -s "$temporary/lean.txt" "$temporary/forth.txt"; then
  diff -u "$temporary/lean.txt" "$temporary/forth.txt" >&2 || true
  exit 1
fi
if [ "$(wc -l <"$temporary/lean.txt")" -ne 45 ]; then
  printf '%s\n' 'Unexpected mixed shift table size' >&2; exit 1
fi
printf '%s\n' 'Lean and Forth agree on 45 mixed-term shift cases.'

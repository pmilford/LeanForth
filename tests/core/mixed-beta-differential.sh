#!/usr/bin/env bash
# Finite weak-head syntax observations, not a kernel correctness proof.
set -eu
lean=${LEAN:-lean}
gforth=${GFORTH:-gforth}
case "$("$lean" --version)" in 'Lean (version 4.35.0,'*) ;; *) printf '%s\n' 'Expected Lean 4.35.0' >&2; exit 1 ;; esac
if [ "$("$lean" --githash)" != eb6cafb7290e8bd5f2937522d8d804f58f02bafc ]; then
  printf '%s\n' 'Unexpected Lean revision' >&2; exit 1
fi
temporary=$(mktemp -d)
trap 'rm -f "$temporary/lean.txt" "$temporary/forth.txt"; rmdir "$temporary"' EXIT
"$lean" tests/reference/mixed-beta-table.lean >"$temporary/lean.txt"
"$gforth" tests/core/mixed-beta-table.fs >"$temporary/forth.txt"
if ! cmp -s "$temporary/lean.txt" "$temporary/forth.txt"; then
  diff -u "$temporary/lean.txt" "$temporary/forth.txt" >&2 || true
  exit 1
fi
if [ "$(wc -l <"$temporary/lean.txt")" -ne 7 ]; then
  printf '%s\n' 'Unexpected mixed beta table size' >&2; exit 1
fi
printf '%s\n' 'Lean and Forth agree on 7 mixed-term weak-head cases.'

#!/usr/bin/env bash
set -eu

lean=${LEAN:-lean}
gforth=${GFORTH:-gforth}
version=$("$lean" --version)
case "$version" in
  'Lean (version 4.35.0,'*) ;;
  *) printf 'Expected Lean 4.35.0; got: %s\n' "$version" >&2; exit 1 ;;
esac
revision=$("$lean" --githash)
if [ "$revision" != eb6cafb7290e8bd5f2937522d8d804f58f02bafc ]; then
  printf 'Unexpected Lean revision: %s\n' "$revision" >&2
  exit 1
fi
temporary=$(mktemp -d)
trap 'rm -f "$temporary/lean.txt" "$temporary/forth.txt" "$temporary/lean-negative.txt" "$temporary/forth-negative.txt"; rmdir "$temporary"' EXIT
if ! "$lean" -DwarningAsError=true tests/legacy/infer-table.lean >"$temporary/lean.txt"; then
  cat "$temporary/lean.txt" >&2
  exit 1
fi
if ! "$gforth" tests/legacy/infer-table.fs >"$temporary/forth.txt"; then
  cat "$temporary/forth.txt" >&2
  exit 1
fi
if ! cmp -s "$temporary/lean.txt" "$temporary/forth.txt"; then
  printf '%s\n' 'Lean and Forth inferred-type tables differ' >&2
  diff -u "$temporary/lean.txt" "$temporary/forth.txt" >&2 || true
  exit 1
fi
if [ "$(wc -l <"$temporary/lean.txt")" -ne 7 ]; then
  printf '%s\n' 'Unexpected inferred-type table size' >&2
  exit 1
fi
if ! "$lean" -DwarningAsError=true tests/legacy/infer-negative-table.lean >"$temporary/lean-negative.txt"; then
  cat "$temporary/lean-negative.txt" >&2
  exit 1
fi
if ! "$gforth" tests/legacy/infer-negative-table.fs >"$temporary/forth-negative.txt"; then
  cat "$temporary/forth-negative.txt" >&2
  exit 1
fi
if ! paste "$temporary/lean-negative.txt" "$temporary/forth-negative.txt" | awk '
  NF != 4 || $1 != $3 || $2 != 1 || ($4 != 1 && $4 != 3) { exit 1 }
  ($1 == 0 || $1 == 2 || $1 == 5) && $4 != 1 { exit 1 }
  END { if (NR != 6) exit 1 }
'; then
  printf '%s\n' 'Negative inference results violate the reference expectations' >&2
  paste "$temporary/lean-negative.txt" "$temporary/forth-negative.txt" >&2
  exit 1
fi
printf '%s\n' 'Seven inferred types match Lean; six Lean-rejected inputs yield invalid or unknown in Forth.'

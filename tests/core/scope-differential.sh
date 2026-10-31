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
trap 'rm -f "$temporary/lean.txt" "$temporary/forth.txt"; rmdir "$temporary"' EXIT
if ! "$lean" --run tests/reference/scope-table.lean >"$temporary/lean.txt"; then
  cat "$temporary/lean.txt" >&2
  exit 1
fi
if ! "$gforth" tests/core/scope-table.fs >"$temporary/forth.txt"; then
  cat "$temporary/forth.txt" >&2
  exit 1
fi
if ! cmp -s "$temporary/lean.txt" "$temporary/forth.txt"; then
  printf '%s\n' 'Lean and Forth scope tables differ' >&2
  diff -u "$temporary/lean.txt" "$temporary/forth.txt" >&2 || true
  exit 1
fi
if [ "$(wc -l <"$temporary/lean.txt")" -ne 64 ]; then
  printf '%s\n' 'Unexpected scope table size' >&2
  exit 1
fi
printf '%s\n' 'Lean and Forth agree on 64 structural scope cases.'

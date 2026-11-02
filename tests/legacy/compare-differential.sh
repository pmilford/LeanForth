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
if ! "$lean" -DwarningAsError=true tests/legacy/compare-table.lean >"$temporary/lean.txt"; then
  cat "$temporary/lean.txt" >&2
  exit 1
fi
if ! "$gforth" tests/legacy/compare-table.fs >"$temporary/forth.txt"; then
  cat "$temporary/forth.txt" >&2
  exit 1
fi
if ! paste "$temporary/lean.txt" "$temporary/forth.txt" | awk '
  NF != 4 || $1 != $3 || ($2 != 0 && $2 != 1) || ($4 != 0 && $4 != 3) { exit 1 }
  $4 == 0 && $2 != 1 { exit 1 }
  $1 == 5 && ($2 != 1 || $4 != 3) { exit 1 }
  END { if (NR != 6) exit 1 }
'; then
  printf '%s\n' 'Comparison results violate the Lean reference expectations' >&2
  paste "$temporary/lean.txt" "$temporary/forth.txt" >&2
  exit 1
fi
printf '%s\n' 'Forth equal results agree with Lean on six closed cases; an unsupported Lean equality remains unknown.'

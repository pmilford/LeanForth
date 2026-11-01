#!/usr/bin/env bash
# Finite conversion comparison with pinned Lean; this is not proof acceptance.
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
  printf 'Unexpected Lean revision: %s\n' "$revision" >&2; exit 1
fi
temporary=$(mktemp -d)
trap 'rm -f "$temporary/lean.txt" "$temporary/forth.txt"; rmdir "$temporary"' EXIT
"$lean" tests/reference/compare-table.lean >"$temporary/lean.txt"
"$lean" tests/reference/tagged-capture-convert.lean
"$gforth" tests/core/tagged-convert-table.fs >"$temporary/forth.txt"
if ! paste "$temporary/lean.txt" "$temporary/forth.txt" | awk '
  NF != 4 || $1 != $3 || ($2 == 1 && $4 != 0) || ($2 == 0 && $4 != 3) { exit 1 }
  END { if (NR != 6) exit 1 }
'; then
  printf '%s\n' 'Tagged conversion differs from the selected Lean cases' >&2
  paste "$temporary/lean.txt" "$temporary/forth.txt" >&2
  exit 1
fi
printf '%s\n' 'Tagged conversion agrees with Lean on six selected cases.'

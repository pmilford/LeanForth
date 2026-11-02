#!/usr/bin/env bash
# Finite untrusted syntax comparison, not a theorem-validity claim.
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
"$lean" -DwarningAsError=true tests/reference/beta-table.lean >"$temporary/lean.txt"
"$gforth" tests/core/tagged-beta-table.fs >"$temporary/forth.txt"
if [ "$(wc -l <"$temporary/lean.txt")" -ne 15 ] ||
   [ "$(wc -l <"$temporary/forth.txt")" -ne 15 ]; then
  printf '%s\n' 'Unexpected beta table size' >&2; exit 1
fi
if ! diff -u "$temporary/lean.txt" "$temporary/forth.txt"; then
  printf '%s\n' 'Tagged beta results differ from Lean' >&2; exit 1
fi
printf '%s\n' 'Tagged beta matches Lean on 15 finite closed cases.'

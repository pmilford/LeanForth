#!/usr/bin/env bash
# Direct finite differential comparison; no theorem validity claim.
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
"$lean" -DwarningAsError=true tests/reference/tagged-application-table.lean >"$temporary/lean.txt"
"$gforth" tests/core/tagged-application-table.fs >"$temporary/forth.txt"
if [ "$(wc -l <"$temporary/lean.txt")" -ne 18 ]; then
  printf '%s\n' 'Unexpected Lean table size' >&2; exit 1
fi
if ! diff -u "$temporary/lean.txt" "$temporary/forth.txt"; then
  printf '%s\n' 'Tagged application inference differs from Lean' >&2; exit 1
fi
printf '%s\n' 'Tagged application inference matches Lean on 18 finite cases.'

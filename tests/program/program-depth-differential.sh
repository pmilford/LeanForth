#!/usr/bin/env bash
# Finite oracle comparison; no claim that Forth execution or code is verified.
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
trap 'rm -f "$temporary/ProgramContracts.olean" "$temporary/lean.txt" "$temporary/forth.txt"; rmdir "$temporary"' EXIT
"$lean" -o "$temporary/ProgramContracts.olean" tests/reference/program-contracts.lean
LEAN_PATH="$temporary" "$lean" --run tests/reference/program-depth-table.lean >"$temporary/lean.txt"
"$gforth" tests/program/program-depth-table.fs >"$temporary/forth.txt"
if [ "$(wc -l <"$temporary/lean.txt")" -ne 1093 ] ||
   [ "$(wc -l <"$temporary/forth.txt")" -ne 1093 ]; then
  printf '%s\n' 'Unexpected depth table size' >&2; exit 1
fi
if ! diff -u "$temporary/lean.txt" "$temporary/forth.txt"; then
  printf '%s\n' 'Forth stack-depth diagnostic differs from Lean reference' >&2; exit 1
fi
printf '%s\n' 'Stack-depth diagnostic matches Lean on 1,093 finite opcode lists.'

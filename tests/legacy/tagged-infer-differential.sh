#!/usr/bin/env bash
# A paired, finite oracle check; neither program is a trusted LeanForth kernel.
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
"$gforth" tests/legacy/tagged-infer.fs
"$lean" -DwarningAsError=true tests/legacy/symbolic-infer-oracle.lean
printf '%s\n' 'Tagged Sort and Pi results match the shared Lean universe expectations.'

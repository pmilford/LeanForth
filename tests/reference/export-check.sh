#!/usr/bin/env bash
set -eu

lean=${LEAN:-lean}
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
toolchain=$("$lean" --print-prefix)
temporary=$(mktemp -d)
trap 'rm -f "$temporary/LeanForthComposition.olean" "$temporary/LeanForthIdentity.olean" "$temporary/export.ndjson"; rmdir "$temporary"' EXIT
"$lean" -o "$temporary/LeanForthComposition.olean" tests/reference/composition.lean
PATH="$toolchain/bin:$PATH" LEAN_PATH="$temporary" \
  "$toolchain/bin/leanexport" LeanForthComposition -- composition >"$temporary/export.ndjson"
if ! cmp -s tests/reference/composition.ndjson "$temporary/export.ndjson"; then
  printf '%s\n' 'Lean export differs from the pinned fixture' >&2
  diff -u tests/reference/composition.ndjson "$temporary/export.ndjson" >&2 || true
  exit 1
fi
"$lean" -o "$temporary/LeanForthIdentity.olean" tests/reference/identity.lean
PATH="$toolchain/bin:$PATH" LEAN_PATH="$temporary" \
  "$toolchain/bin/leanexport" LeanForthIdentity -- identity >"$temporary/export.ndjson"
if ! cmp -s tests/reference/identity.ndjson "$temporary/export.ndjson"; then
  printf '%s\n' 'Lean identity export differs from the pinned fixture' >&2
  diff -u tests/reference/identity.ndjson "$temporary/export.ndjson" >&2 || true
  exit 1
fi
printf '%s\n' 'Lean composition and identity exports match their pinned fixtures.'

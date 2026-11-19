#!/usr/bin/env bash
set -eu

. "$(dirname "${BASH_SOURCE[0]}")/../support/pinned-lean.sh"
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
leanexport=${LEANEXPORT:-$toolchain/bin/leanexport}   # the Makefile's may replay a cached run
temporary=$(mktemp -d)
trap 'rm -f "$temporary/LeanForthComposition.olean" "$temporary/LeanForthIdentity.olean" "$temporary/LeanForthTypeIdentity.olean" "$temporary/LeanForthPolyIdentity.olean" "$temporary/LeanForthConstFixture.olean" "$temporary/export.ndjson"; rmdir "$temporary"' EXIT
"$lean" -DwarningAsError=true -o "$temporary/LeanForthComposition.olean" tests/reference/composition.lean
PATH="$toolchain/bin:$PATH" LEAN_PATH="$temporary" \
  "$leanexport" LeanForthComposition -- composition >"$temporary/export.ndjson"
if ! cmp -s tests/reference/composition.ndjson "$temporary/export.ndjson"; then
  printf '%s\n' 'Lean export differs from the pinned fixture' >&2
  diff -u tests/reference/composition.ndjson "$temporary/export.ndjson" >&2 || true
  exit 1
fi
"$lean" -DwarningAsError=true -o "$temporary/LeanForthIdentity.olean" tests/reference/identity.lean
PATH="$toolchain/bin:$PATH" LEAN_PATH="$temporary" \
  "$leanexport" LeanForthIdentity -- identity >"$temporary/export.ndjson"
if ! cmp -s tests/reference/identity.ndjson "$temporary/export.ndjson"; then
  printf '%s\n' 'Lean identity export differs from the pinned fixture' >&2
  diff -u tests/reference/identity.ndjson "$temporary/export.ndjson" >&2 || true
  exit 1
fi
"$lean" -DwarningAsError=true -o "$temporary/LeanForthTypeIdentity.olean" tests/reference/type-identity.lean
PATH="$toolchain/bin:$PATH" LEAN_PATH="$temporary" \
  "$leanexport" LeanForthTypeIdentity -- type_identity >"$temporary/export.ndjson"
if ! cmp -s tests/reference/type-identity.ndjson "$temporary/export.ndjson"; then
  printf '%s\n' 'Lean type identity export differs from the pinned fixture' >&2
  diff -u tests/reference/type-identity.ndjson "$temporary/export.ndjson" >&2 || true
  exit 1
fi
"$lean" -DwarningAsError=true -o "$temporary/LeanForthPolyIdentity.olean" tests/reference/poly-identity.lean
PATH="$toolchain/bin:$PATH" LEAN_PATH="$temporary" \
  "$leanexport" LeanForthPolyIdentity -- poly_identity >"$temporary/export.ndjson"
if ! cmp -s tests/reference/poly-identity.ndjson "$temporary/export.ndjson"; then
  printf '%s\n' 'Lean polymorphic identity export differs from the pinned fixture' >&2
  diff -u tests/reference/poly-identity.ndjson "$temporary/export.ndjson" >&2 || true
  exit 1
fi
"$lean" -DwarningAsError=true -o "$temporary/LeanForthConstFixture.olean" tests/reference/constant-fixture.lean
PATH="$toolchain/bin:$PATH" LEAN_PATH="$temporary" \
  "$leanexport" LeanForthConstFixture -- fixturePoly fixtureUse >"$temporary/export.ndjson"
if ! cmp -s tests/reference/constant-fixture.ndjson "$temporary/export.ndjson"; then
  printf '%s\n' 'Lean constant/dependency export differs from the pinned fixture' >&2
  diff -u tests/reference/constant-fixture.ndjson "$temporary/export.ndjson" >&2 || true
  exit 1
fi
printf '%s\n' 'Lean composition, identity and constant exports match their pinned fixtures.'

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
"$lean" tests/reference/composition.lean
"$lean" tests/reference/binders.lean
"$lean" tests/reference/universes.lean
"$lean" tests/reference/core-oracle.lean
"$lean" tests/reference/declaration-oracle.lean
"$lean" tests/reference/substitution-oracle.lean
"$lean" tests/reference/transform-model.lean
"$lean" tests/reference/type-model.lean
"$lean" tests/reference/clamp.lean
"$lean" tests/reference/stack-clamp.lean
output=$(mktemp)
trap 'rm -f "$output"' EXIT
for test_name in composition-invalid binders-invalid universes-invalid; do
  if "$lean" "tests/reference/$test_name.lean" >"$output" 2>&1; then
    printf 'Invalid case %s was unexpectedly accepted\n' "$test_name" >&2
    exit 1
  fi
  if ! grep -qi 'type mismatch' "$output"; then
    cat "$output" >&2
    printf 'Lean failed for an unexpected reason: %s\n' "$test_name" >&2
    exit 1
  fi
done
if "$lean" tests/reference/clamp-invalid.lean >"$output" 2>&1; then
  printf '%s\n' 'Incorrect clamp was unexpectedly accepted' >&2
  exit 1
fi
if ! grep -q 'is false' "$output"; then
  cat "$output" >&2
  printf '%s\n' 'Incorrect clamp failed for an unexpected reason' >&2
  exit 1
fi
printf '%s\n' 'Lean accepted valid examples and rejected incompatible terms.'

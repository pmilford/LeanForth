#!/usr/bin/env bash
set -eu
lean=${LEAN:-lean}
version=$("$lean" --version)
case "$version" in
  'Lean (version 4.35.0,'*) ;;
  *) printf 'Expected Lean 4.35.0; got: %s\n' "$version" >&2; exit 1 ;;
esac
"$lean" tests/reference/composition.lean
"$lean" tests/reference/binders.lean
"$lean" tests/reference/clamp.lean
output=$(mktemp)
trap 'rm -f "$output"' EXIT
for test_name in composition-invalid binders-invalid; do
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
printf '%s\n' 'Lean accepted valid examples and rejected incompatible terms.'

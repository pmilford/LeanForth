#!/usr/bin/env bash
set -eu
lean=${LEAN:-lean}
version=$("$lean" --version)
case "$version" in
  'Lean (version 4.35.0,'*) ;;
  *) printf 'Expected Lean 4.35.0; got: %s\n' "$version" >&2; exit 1 ;;
esac
"$lean" tests/reference/composition.lean
output=$(mktemp)
trap 'rm -f "$output"' EXIT
if "$lean" tests/reference/composition-invalid.lean >"$output" 2>&1; then
  printf '%s\n' 'Invalid composition was unexpectedly accepted' >&2
  exit 1
fi
if ! grep -q 'Application type mismatch' "$output"; then
  cat "$output" >&2
  printf '%s\n' 'Lean failed for an unexpected reason' >&2
  exit 1
fi
printf '%s\n' 'Lean accepted valid composition and rejected invalid composition.'

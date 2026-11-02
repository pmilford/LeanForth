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
"$lean" -DwarningAsError=true tests/reference/composition.lean
"$lean" -DwarningAsError=true tests/reference/binders.lean
"$lean" -DwarningAsError=true tests/reference/universes.lean
"$lean" -DwarningAsError=true tests/reference/core-oracle.lean
"$lean" -DwarningAsError=true tests/reference/declaration-oracle.lean
"$lean" -DwarningAsError=true tests/reference/constant-environment-oracle.lean
"$lean" -DwarningAsError=true tests/reference/nested-signature-oracle.lean
"$lean" -DwarningAsError=true tests/reference/mixed-infer-oracle.lean
"$lean" -DwarningAsError=true tests/reference/mixed-definition-oracle.lean
"$lean" -DwarningAsError=true tests/reference/declaration-chain-oracle.lean
"$lean" -DwarningAsError=true tests/reference/constant-application-oracle.lean
"$lean" -DwarningAsError=true tests/reference/open-context-oracle.lean
"$lean" -DwarningAsError=true tests/reference/substitution-oracle.lean
"$lean" -DwarningAsError=true tests/reference/transform-model.lean
"$lean" -DwarningAsError=true tests/reference/type-model.lean
"$lean" -DwarningAsError=true tests/reference/clamp.lean
"$lean" -DwarningAsError=true tests/reference/stack-clamp.lean
LEAN="$lean" bash tests/reference/stack-composition-check.sh
"$lean" -DwarningAsError=true tests/reference/program-contracts.lean
LEAN="$lean" bash tests/reference/memory-program-check.sh
"$lean" -DwarningAsError=true tests/reference/program-examples.lean
"$lean" -DwarningAsError=true tests/reference/checked-add.lean
"$lean" -DwarningAsError=true tests/reference/factorial-reference.lean
"$lean" -DwarningAsError=true tests/reference/gcd-reference.lean
output=$(mktemp)
trap 'rm -f "$output"' EXIT
for test_name in composition-invalid binders-invalid universes-invalid; do
  if "$lean" -DwarningAsError=true "tests/reference/$test_name.lean" >"$output" 2>&1; then
    printf 'Invalid case %s was unexpectedly accepted\n' "$test_name" >&2
    exit 1
  fi
  if ! grep -qi 'type mismatch' "$output"; then
    cat "$output" >&2
    printf 'Lean failed for an unexpected reason: %s\n' "$test_name" >&2
    exit 1
  fi
done
if "$lean" -DwarningAsError=true tests/reference/clamp-invalid.lean >"$output" 2>&1; then
  printf '%s\n' 'Incorrect clamp was unexpectedly accepted' >&2
  exit 1
fi
if ! grep -q 'is false' "$output"; then
  cat "$output" >&2
  printf '%s\n' 'Incorrect clamp failed for an unexpected reason' >&2
  exit 1
fi
# Every Lean invocation uses -DwarningAsError=true so that `sorry` fails.
if "$lean" -DwarningAsError=true tests/reference/sorry-must-fail.lean >"$output" 2>&1; then
  printf '%s\n' 'A sorry-backed false theorem was unexpectedly accepted' >&2
  exit 1
fi
if ! grep -q 'declaration uses .sorry.' "$output"; then
  cat "$output" >&2
  printf '%s\n' 'The sorry fixture failed for an unexpected reason' >&2
  exit 1
fi
printf '%s\n' 'Lean accepted valid examples and rejected incompatible terms.'

#!/usr/bin/env bash
# Check Lean's abstract stack composition model, not a Forth runtime proof.
set -eu
lean=${LEAN:-lean}
temporary=$(mktemp -d)
trap 'rm -f "$temporary/stack-clamp.olean" "$temporary/program-stack-composition.olean"; rmdir "$temporary"' EXIT
"$lean" -DwarningAsError=true -o "$temporary/stack-clamp.olean" tests/reference/stack-clamp.lean
LEAN_PATH="$temporary" "$lean" -DwarningAsError=true -o "$temporary/program-stack-composition.olean" tests/reference/program-stack-composition.lean
LEAN_PATH="$temporary" "$lean" -DwarningAsError=true tests/reference/program-stack-swap.lean

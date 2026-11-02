#!/usr/bin/env bash
# Check Lean's abstract stack composition model, not a Forth runtime proof.
set -eu
lean=${LEAN:-lean}
temporary=$(mktemp -d)
trap 'rm -f "$temporary/stack-clamp.olean"; rmdir "$temporary"' EXIT
"$lean" -o "$temporary/stack-clamp.olean" tests/reference/stack-clamp.lean
LEAN_PATH="$temporary" "$lean" tests/reference/program-stack-composition.lean

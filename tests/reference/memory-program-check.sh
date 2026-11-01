#!/usr/bin/env bash
# Compile the reference dependency in isolation; no checked Forth is implied.
set -eu
lean=${LEAN:-lean}
temporary=$(mktemp -d)
trap 'rm -f "$temporary/program-contracts.olean"; rmdir "$temporary"' EXIT
"$lean" -o "$temporary/program-contracts.olean" tests/reference/program-contracts.lean
LEAN_PATH="$temporary" "$lean" tests/reference/memory-program-reference.lean

#!/usr/bin/env bash
# Compile the reference dependency in isolation; no checked Forth is implied.
set -eu
lean=${LEAN:-lean}
temporary=$(mktemp -d)
trap 'rm -f "$temporary/program-contracts.olean" "$temporary/memory-program-reference.olean" "$temporary/memory-copy-reference.olean" "$temporary/memory-copy-properties.olean" "$temporary/memory-swap-reference.olean"; rmdir "$temporary"' EXIT
"$lean" -o "$temporary/program-contracts.olean" tests/reference/program-contracts.lean
LEAN_PATH="$temporary" "$lean" -o "$temporary/memory-program-reference.olean" tests/reference/memory-program-reference.lean
LEAN_PATH="$temporary" "$lean" -o "$temporary/memory-swap-reference.olean" tests/reference/memory-swap-reference.lean
LEAN_PATH="$temporary" "$lean" tests/reference/memory-swap-involution.lean
LEAN_PATH="$temporary" "$lean" -o "$temporary/memory-copy-reference.olean" tests/reference/memory-copy-reference.lean
LEAN_PATH="$temporary" "$lean" -o "$temporary/memory-copy-properties.olean" tests/reference/memory-copy-properties.lean
LEAN_PATH="$temporary" "$lean" tests/reference/memory-copy-twice.lean
LEAN_PATH="$temporary" "$lean" tests/reference/memory-sequence-reference.lean

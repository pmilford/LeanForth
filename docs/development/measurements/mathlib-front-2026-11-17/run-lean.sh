#!/usr/bin/env bash
# Run pinned Lean 4.35.0 on a file importing pinned Mathlib (read-only on
# .tools; never the elan proxies). Usage: run-lean.sh FILE.lean
set -u
tools=${TOOLS:-/home/peter/code/LeanForth/.tools}
M=$tools/mathlib/mathlib4/.lake
LP=$M/build/lib/lean
for p in "$M"/packages/*; do LP=$LP:$p/.lake/build/lib/lean; done
export LEAN_PATH=$LP
T=$tools/elan/toolchains/leanprover--lean4---v4.35.0
/usr/bin/time -f 'lean: %e s %M KB peak' "$T/bin/lean" "$1"
echo "exit $?"

#!/usr/bin/env bash
# Run one of this folder's Lean measurement scripts with pinned Lean 4.35.0
# (never an elan proxy) and Mathlib's build on LEAN_PATH, for
# docs/design/SIMP_DATA.md. A throwaway measurement, not a product tool.
# Usage: run.sh SCRIPT.lean OUT MODULE...
#   TOOLS  the project's .tools folder (default: the repository's own;
#          a worktree passes the main checkout's)
set -eu
here=$(cd "$(dirname "$0")/../../../.." && pwd)
tools=${TOOLS:-$here/.tools}
M=$tools/mathlib/mathlib4/.lake
LP=$M/build/lib/lean
for p in "$M"/packages/*; do LP=$LP:$p/.lake/build/lib/lean; done
L=$tools/elan/toolchains/leanprover--lean4---v4.35.0
script=$1; out=$2; shift 2
LEAN_PATH=$LP PATH=$L/bin:$PATH /usr/bin/time -f '%e s %M KB' "$L/bin/lean" --run "$script" "$@" > "$out"

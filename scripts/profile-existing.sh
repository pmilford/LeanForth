#!/usr/bin/env bash
# Profile the finite universe-substitution tables, outside the checker: pinned
# Lean's instantiateLevelParams against the current lf-mixed-level-substitute
# (workload mixed-level-substitution-48, a new timing series from 2026-11-02).
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
lean=$(python3 scripts/lean_pin.py pinned)   # $LEAN or the pinned Lean, never an elan proxy
gforth=${GFORTH:-gforth}
repetitions=${1:-3}
if [[ ! $repetitions =~ ^[1-9][0-9]?$ ]]; then
  echo 'Usage: profile-existing.sh [repetitions: 1-99] (LEAN and GFORTH select executables)' >&2
  exit 2
fi
for tool in "$lean" "$gforth" git sha256sum awk cmp wc xargs; do
  command -v "$tool" >/dev/null 2>&1 || { printf 'Missing tool: %s\n' "$tool" >&2; exit 1; }
done
lean_version=$("$lean" --version)
[[ $lean_version == 'Lean (version 4.35.0,'* ]] || { echo 'Expected Lean 4.35.0' >&2; exit 1; }
lean_hash=$("$lean" --githash)
[[ $lean_hash == eb6cafb7290e8bd5f2937522d8d804f58f02bafc ]] || { echo 'Unexpected Lean revision' >&2; exit 1; }
gforth_version=$("$gforth" --version 2>&1)
temporary=$(mktemp -d)
trap 'rm -f "$temporary/probe" "$temporary/metric" "$temporary/timing" "$temporary/Lean.out" "$temporary/Forth.out" "$temporary/Lean.normalized" "$temporary/Forth.normalized" "$temporary/results" "$temporary/baseline"; rmdir "$temporary"' EXIT
export LC_ALL=C
# GNU time reports elapsed seconds and maximum resident set size in KiB on Linux.
if [[ $(uname -s) == Linux && -x /usr/bin/time ]] && /usr/bin/time -f '%e %M' -o "$temporary/probe" true 2>/dev/null && [[ $(cat "$temporary/probe") =~ ^[0-9.]+\ [0-9]+$ ]]; then
  timer=gnu
else
  timer=bash
fi
run_one() {
  local label=$1 iteration=$2
  shift 2
  if [[ $timer == gnu ]]; then
    /usr/bin/time -f '%e %M' -o "$temporary/metric" "$@" >"$temporary/$label.out"
  else
    TIMEFORMAT='%R'; { time "$@" >"$temporary/$label.out"; } 2>"$temporary/timing"
    # Preserve program stderr in the fallback, extracting only the last timing line.
    sed '$d' "$temporary/timing" >&2
    printf '%s unavailable\n' "$(tail -n 1 "$temporary/timing")" >"$temporary/metric"
  fi
  [[ $(wc -l <"$temporary/$label.out") -eq 48 ]] || { echo "Unexpected $label table length" >&2; exit 1; }
  awk '{$1=$1; print}' "$temporary/$label.out" >"$temporary/$label.normalized"
  printf '%s %s %s\n' "$iteration" "$label" "$(cat "$temporary/metric")" >>"$temporary/results"
}
lean_table=tests/reference/term-level-substitute-table.lean
forth_table=tests/core/mixed-level-substitute-plain-table.fs
for ((i=1; i<=repetitions; i++)); do
  if (( i % 2 )); then
    run_one Lean "$i" "$lean" -DwarningAsError=true --run "$lean_table"
    run_one Forth "$i" "$gforth" "$forth_table" </dev/null
  else
    run_one Forth "$i" "$gforth" "$forth_table" </dev/null
    run_one Lean "$i" "$lean" -DwarningAsError=true --run "$lean_table"
  fi
  if ! cmp -s "$temporary/Lean.normalized" "$temporary/Forth.normalized"; then
    echo "Output mismatch in repetition $i" >&2
    diff -u "$temporary/Lean.normalized" "$temporary/Forth.normalized" >&2 || true
    exit 1
  fi
  if [[ $i -eq 1 ]]; then
    cp "$temporary/Lean.normalized" "$temporary/baseline"
  elif ! cmp -s "$temporary/baseline" "$temporary/Lean.normalized"; then
    echo "Output changed in repetition $i" >&2; exit 1
  fi
done
printf 'Mixed level substitution: 48 matching rows; %s repetitions\n' "$repetitions"
printf 'UTC: %s\nPlatform: %s\n' "$(date -u +'%Y-%m-%dT%H:%M:%SZ')" "$(uname -a)"
printf 'Revision: %s\n' "$(git rev-parse HEAD)"
if [[ -n $(git status --porcelain --untracked-files=normal) ]]; then echo 'Worktree: dirty (revision alone does not identify inputs)'; else echo 'Worktree: clean'; fi
printf 'Lean: %s; git %s\nForth: %s\n' "$lean_version" "$lean_hash" "$gforth_version"
printf 'Timer: %s; elapsed seconds and peak RSS KiB (unavailable when unsupported)\n' "$timer"
printf 'run implementation elapsed_s peak_RSS_KiB\n'
cat "$temporary/results"
printf 'Normalized output SHA-256: '; sha256sum "$temporary/baseline" | awk '{print $1}'
# The Forth table loads src/main.fs, which loads every current module, so
# every tracked Forth source under src/ is hashed (src/main.fs and
# src/kernel/mixed-level-substitute.fs among them).
printf 'Input SHA-256 (individual files):\n'
sha256sum scripts/profile-existing.sh "$lean_table" "$forth_table"
git ls-files -z -- 'src/*.fs' | xargs -0 sha256sum

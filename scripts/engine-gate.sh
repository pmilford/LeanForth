#!/usr/bin/env bash
# engine-gate: the evidence that bin/leanforth's default engine, gforth-fast,
# gives the same verdicts as Gforth's checking engine (--checked).
#
# Usage: scripts/engine-gate.sh [INIT_EXPORT [ARENA_DIR]]   (make engine-gate)
#   INIT_EXPORT  Lean's Init as a lean4export NDJSON file (default:
#                .claude/work/IM/init.ndjson of the main checkout);
#   ARENA_DIR    the Lean Kernel Arena tests, folders good/ and bad/ of
#                *.ndjson files (default: .claude/work/arena/tests435 there).
# Both are machine-local, large and not in the repository; the gate says so
# and exits 4 when one is missing. It runs bin/leanforth check --no-manifest
# on all of Init with --jobs 8, and on every arena test, once on each engine
# (GFORTH unset, so the wrapper chooses: gforth-fast by default, gforth with
# --checked), then compares the verdict lines and exit codes (not the
# times). Exit 0 only if everything is identical; 1 on a difference; 5 when a
# run was killed. About 15 minutes. Not part of make check.
set -u
root=$(cd "$(dirname "$0")/.." && pwd -P)
common=$(git -C "$root" rev-parse --path-format=absolute --git-common-dir 2>/dev/null)
work=${common%/.git}/.claude/work
[ -d "$work" ] || work=$root/.claude/work
init=${1:-$work/IM/init.ndjson}
arena=${2:-$work/arena/tests435}
for need in "$init" "$arena"; do
  [ -e "$need" ] || { echo "engine-gate: missing $need" >&2; exit 4; }
done
out=${ENGINE_GATE_OUT:-$root/.claude/work/engine-gate}
mkdir -p "$out" || exit 4
ulimit -u 500
unset GFORTH

# run ENGINE-OPTION NAME FILE [CHECK-OPTION]...: verdicts and exit code
run() {
  local option=$1 name=$2 file=$3; shift 3
  timeout -k 5 3600 setsid "$root/bin/leanforth" check --no-manifest $option "$@" \
    "$file" </dev/null >"$out/$name.out" 2>"$out/$name.err"
  echo "exit $?" >>"$out/$name.out"
}
for engine in fast checked; do
  option=
  [ "$engine" = checked ] && option=--checked
  echo "engine-gate: $engine: Init"
  run "$option" "init-$engine" "$init" --jobs 8
  echo "engine-gate: $engine: arena tests"
  : >"$out/arena-$engine.txt"
  while IFS= read -r f; do
    run "$option" "arena-one-$engine" "$f"
    { echo "== ${f#"$arena"/}"; cat "$out/arena-one-$engine.out"; } >>"$out/arena-$engine.txt"
  done < <(find "$arena" -name '*.ndjson' | sort)
done
status=0
for part in init arena; do
  suffix=out; [ $part = arena ] && suffix=txt
  if cmp -s "$out/$part-fast.$suffix" "$out/$part-checked.$suffix"; then
    echo "engine-gate: $part identical ($(wc -l <"$out/$part-fast.$suffix") lines)"
  else
    echo "engine-gate: $part DIFFERS:"
    diff "$out/$part-fast.$suffix" "$out/$part-checked.$suffix" | head -20
    status=1
  fi
done
grep -q '^exit 5$' "$out"/init-*.out && status=5
[ $status = 0 ] && echo "engine-gate: PASSED" || echo "engine-gate: FAILED ($status)"
exit $status

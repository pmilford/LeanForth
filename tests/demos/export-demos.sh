#!/usr/bin/env bash
# Re-export the demos (docs/user/DEMOS.md) with the pinned Lean 4.35.0: compile
# each tests/demos/DemoX.lean (a theorem pinned Lean proves, warnings are errors)
# and export the theorem with the pinned exporter (scripts/export.sh), which
# writes tests/demos/X.ndjson and its manifest. The exports are committed;
# run this only to rebuild them. Usage: LEAN=... bash tests/demos/export-demos.sh
set -eu
here=$(cd "$(dirname "$0")/../.." && pwd)
lean=${LEAN:-$here/.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean}
work=$(mktemp -d)
trap 'rm -f "$work"/*.olean; rmdir "$work"' EXIT
export LEAN_PATH=$work LEAN=$lean
cd "$here"
for pair in AddComm:add_comm_by_induction Gauss:gauss_sum OddSum:odd_sum \
            Cantor:cantor Sqrt2:sqrt2_irrational; do
  name=${pair%%:*}
  theorem=${pair##*:}
  "$lean" -DwarningAsError=true -o "$work/Demo$name.olean" "tests/demos/Demo$name.lean"
  bash scripts/export.sh "tests/demos/$name.ndjson" "Demo$name" -- "$theorem"
done

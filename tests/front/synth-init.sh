#!/usr/bin/env bash
# The instance table against pinned Lean on all of Init (plans FE1e2 and
# FE1e3; make reference-synth): Init exported with the pinned leanexport
# (checked by its SHA-256, as tests/front/elab-init.sh), its elaboration
# data written by scripts/export-elab.sh, then tests/front/check_synth.py:
# every instance's class and keys recomputed by LeanForth, and
# getInstances' candidates for S1's problems and a sample of Init's
# classes, compared with pinned Lean's #synth traces. Needs pinned Lean
# 4.35.0 (LEAN), Gforth (GFORTH; gforth-fast beside it when there is one)
# and Python 3.
set -eu
lean=${LEAN:-lean}
toolchain=$("$lean" --print-prefix)
leanexport=${LEANEXPORT:-$toolchain/bin/leanexport}   # the Makefile's may replay a cached run
work=$(mktemp -d)
names="init.ndjson init.ndjson.manifest.json init.elab.ndjson"
trap 'for n in $names; do rm -f "$work/$n"; done; rmdir "$work"' EXIT
PATH="$toolchain/bin:$PATH" "$leanexport" Init >"$work/init.ndjson"
digest=$(sha256sum "$work/init.ndjson" | cut -c1-64)
if [ "$digest" != c1b2071a6d2132ace8c4711499f078aab2117d925213d5a222a1fe843a59a179 ]; then
  printf 'Unexpected Init export: %s\n' "$digest" >&2
  exit 1
fi
python3 scripts/export_manifest.py "$work/init.ndjson"
LEAN="$lean" bash scripts/export-elab.sh "$work/init.elab.ndjson" "$work/init.ndjson" Init >/dev/null
LEAN="$lean" python3 tests/front/check_synth.py "$work/init.ndjson" "$work/init.elab.ndjson"

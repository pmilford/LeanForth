#!/usr/bin/env bash
# The elaboration data against pinned Lean (plan rows FE1d and FE1e1; make
# reference-elab-data): scripts/export-elab.sh reproduces the init slice's
# and the whnf slice's data (tests/front/init-slice.elab.ndjson,
# whnf-slice.elab.ndjson) byte for byte; then for all of
# Init, exported with the pinned leanexport (the export of
# tests/core/compact-init.sh, checked by its SHA-256), the data's records
# have the pinned SHA-256, the records it writes plus the ones it leaves
# out equal pinned Lean's own counts (tests/reference/elab-data-counts.lean,
# through Lean's queries one constant at a time), LeanForth reads the data
# against Init's export and finds the same counts, reducibility statuses and
# samples (tests/front/elab-init.fs), and the data's ranks and priorities
# give Lean's own candidate order for 19 instance problems
# (tests/reference/elab-instance-order.lean), all compared by
# tests/front/compare_elab_init.py. Uses gforth-fast beside $GFORTH when
# there is one. Needs pinned Lean 4.35.0 (LEAN), Gforth (GFORTH) and
# Python 3.
set -eu
lean=${LEAN:-lean}
gforth=${GFORTH:-gforth}
version=$("$lean" --version)
case "$version" in
  'Lean (version 4.35.0,'*) ;;
  *) printf 'Expected Lean 4.35.0; got: %s\n' "$version" >&2; exit 1 ;;
esac
toolchain=$("$lean" --print-prefix)
leanexport=${LEANEXPORT:-$toolchain/bin/leanexport}   # the Makefile's may replay a cached run
fast="$(dirname "$gforth")/gforth-fast"
if [ -x "$fast" ]; then gforth=$fast; fi
work=$(mktemp -d)
names="init.ndjson init.ndjson.manifest.json init.elab.ndjson slice.elab.ndjson whnf.elab.ndjson finish.txt
  lean.txt forth.txt order.txt"
trap 'for n in $names; do rm -f "$work/$n"; done; rmdir "$work"' EXIT

LEAN="$lean" bash scripts/export-elab.sh "$work/slice.elab.ndjson" tests/author/init-slice.ndjson \
  Init >/dev/null
cmp "$work/slice.elab.ndjson" tests/front/init-slice.elab.ndjson
echo "scripts/export-elab.sh reproduces tests/front/init-slice.elab.ndjson byte for byte"
LEAN="$lean" bash scripts/export-elab.sh "$work/whnf.elab.ndjson" tests/front/whnf-slice.ndjson \
  Init >/dev/null
cmp "$work/whnf.elab.ndjson" tests/front/whnf-slice.elab.ndjson
echo "scripts/export-elab.sh reproduces tests/front/whnf-slice.elab.ndjson byte for byte"

PATH="$toolchain/bin:$PATH" "$leanexport" Init >"$work/init.ndjson"
digest=$(sha256sum "$work/init.ndjson" | cut -c1-64)
if [ "$digest" != c1b2071a6d2132ace8c4711499f078aab2117d925213d5a222a1fe843a59a179 ]; then
  printf 'Unexpected Init export: %s\n' "$digest" >&2
  exit 1
fi
python3 scripts/export_manifest.py "$work/init.ndjson"
LEAN="$lean" bash scripts/export-elab.sh "$work/init.elab.ndjson" "$work/init.ndjson" Init \
  >"$work/finish.txt"
cat "$work/finish.txt"
# The records' SHA-256 of format 2 for Init (2026-11-12): any change to the
# exporter's output shows here first.
records=$(head -1 "$work/init.elab.ndjson" | sed 's/.*"records_sha256":"\([0-9a-f]*\)".*/\1/')
if [ "$records" != b31ba2cf7f1490fab60d5e1bf650ed39282d73cb783e4dabc359b0d1b7d32eda ]; then
  printf 'Unexpected records of Init'"'"'s elaboration data: %s\n' "$records" >&2
  exit 1
fi
echo "Init's elaboration data has the pinned records_sha256"
# Two threads each: under a per-user process limit (ulimit -u, which counts
# threads) a default Lean on a busy machine could not start its workers.
PATH="$toolchain/bin:$PATH" "$lean" -j 2 -DwarningAsError=true --run \
  tests/reference/elab-data-counts.lean >"$work/lean.txt"
PATH="$toolchain/bin:$PATH" "$lean" -j 2 -DwarningAsError=true --run \
  tests/reference/elab-instance-order.lean >"$work/order.txt"
"$gforth" tests/front/elab-init.fs -e "s\" $work/init.ndjson\" s\" $work/init.elab.ndjson\" \
  elab-init-report bye" </dev/null >"$work/forth.txt"
python3 tests/front/compare_elab_init.py "$work/finish.txt" "$work/lean.txt" "$work/forth.txt" \
  "$work/init.elab.ndjson" "$work/order.txt"

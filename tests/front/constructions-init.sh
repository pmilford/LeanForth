#!/usr/bin/env bash
# Lean's generated definitions built by LeanForth against Lean's own, on all
# of Init (plan row FE6; make reference-constructions): Init exported with
# the pinned leanexport (the export of tests/core/compact-init.sh, checked
# by its SHA-256) and its manifest written; then for every inductive type
# whose T.casesOn or T.recOn is in the export, src/front/constructions.fs
# builds it from T.rec and tests/front/constructions-init.fs compares it
# with Lean's node for node. The counts must be the pinned ones below:
# every definition equal, exactly or up to binder names and binder
# information (which the kernel ignores and Lean's exporter shares terms
# by), none different; the unsupported ones are listed with their reasons.
# Uses gforth-fast beside $GFORTH when there is one. Needs pinned Lean
# 4.35.0 (LEAN), Gforth (GFORTH) and Python 3.
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
names="init.ndjson init.ndjson.manifest.json forth.txt"
trap 'for n in $names; do rm -f "$work/$n"; done; rmdir "$work"' EXIT

PATH="$toolchain/bin:$PATH" "$leanexport" Init >"$work/init.ndjson"
digest=$(sha256sum "$work/init.ndjson" | cut -c1-64)
if [ "$digest" != c1b2071a6d2132ace8c4711499f078aab2117d925213d5a222a1fe843a59a179 ]; then
  printf 'Unexpected Init export: %s\n' "$digest" >&2
  exit 1
fi
python3 scripts/export_manifest.py "$work/init.ndjson" >/dev/null
"$gforth" tests/front/constructions-init.fs -e "s\" $work/init.ndjson\" fe6-report bye" \
  </dev/null >"$work/forth.txt"
cat "$work/forth.txt"
expected="casesOn generated 597 equal 430 equal-up-to-binders 160 different 0 unsupported 7
recOn generated 576 equal 533 equal-up-to-binders 37 different 0 unsupported 6"
actual=$(grep ' generated ' "$work/forth.txt")
if [ "$actual" != "$expected" ]; then
  printf 'Counts differ from the pinned ones:\n%s\n' "$expected" >&2
  exit 1
fi
echo "casesOn and recOn: the pinned counts, none different"

#!/usr/bin/env bash
# The export step end to end with pinned Lean (plan task 3.2.6): rebuild the
# composition theorem, export it with scripts/export.sh, and require the
# export and its manifest to equal the committed fixture and manifest byte
# for byte; then the Forth reader must accept the new export with its
# manifest (checked by default) and refuse a copy with one byte changed,
# which it would read without the manifest.
set -eu

. "$(dirname "${BASH_SOURCE[0]}")/../support/pinned-lean.sh"
gforth=${GFORTH:-gforth}
temporary=$(mktemp -d)
trap 'rm -f "$temporary/LeanForthComposition.olean" "$temporary/composition.ndjson" "$temporary/composition.ndjson.manifest.json" "$temporary/changed.ndjson" "$temporary/changed.ndjson.manifest.json"; rmdir "$temporary"' EXIT
"$lean" -DwarningAsError=true -o "$temporary/LeanForthComposition.olean" tests/reference/composition.lean
LEAN="$lean" LEAN_PATH="$temporary" \
  bash scripts/export.sh "$temporary/composition.ndjson" LeanForthComposition -- composition >/dev/null
cmp tests/reference/composition.ndjson "$temporary/composition.ndjson"
cmp tests/reference/composition.ndjson.manifest.json "$temporary/composition.ndjson.manifest.json"
count() {
  "$gforth" src/import/ndjson-count.fs -e "s\" $1\" $2 bye" </dev/null
}
count "$temporary/composition.ndjson" count-export >/dev/null
sed '2s/"composition"/"compositioN"/' "$temporary/composition.ndjson" >"$temporary/changed.ndjson"
cp "$temporary/composition.ndjson.manifest.json" "$temporary/changed.ndjson.manifest.json"
count "$temporary/changed.ndjson" count-export-unchecked >/dev/null
if out=$(count "$temporary/changed.ndjson" count-export); then
  printf 'A changed export was accepted: %s\n' "$out" >&2
  exit 1
fi
case "$out" in
  'error: invalid: export differs from its manifest (field sha256, line 0)') ;;
  *) printf 'Unexpected refusal of a changed export: %s\n' "$out" >&2; exit 1 ;;
esac
printf '%s\n' 'scripts/export.sh reproduces the composition export and its manifest; the check holds.'

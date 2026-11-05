#!/usr/bin/env bash
# The command line's four Lean fixtures with pinned Lean: Lean accepts
# tests/cli/chain.lean (larger than check --record holds), unfold.lean (a
# proof that needs a definition unfolded), irrelevance.lean (one that needs proof
# irrelevance) and inductive.lean (an inductive
# type, a theorem proved with its recursor and a definition computed with
# it), each without axioms, and scripts/export.sh reproduces the committed
# exports and their manifests byte for byte. LEAN names the pinned Lean
# 4.35.0 binary.
set -eu

lean=${LEAN:-lean}
temporary=$(mktemp -d)
# Delete exactly the files this script writes, by name, then the folder.
cleanup() {
  local name
  for name in LeanForthChain.olean LeanForthUnfold.olean LeanForthInductive.olean \
    LeanForthIrrelevance.olean \
    chain.ndjson chain.ndjson.manifest.json unfold.ndjson unfold.ndjson.manifest.json \
    inductive.ndjson inductive.ndjson.manifest.json \
    irrelevance.ndjson irrelevance.ndjson.manifest.json; do
    rm -f "$temporary/$name"
  done
  rmdir "$temporary"
}
trap cleanup EXIT

# Build tests/cli/STEM.lean as MODULE, whose #print axioms names THEOREM,
# and export the declarations given.
reproduce() {
  local stem=$1 module=$2 theorem=$3 out
  shift 3
  out=$("$lean" -DwarningAsError=true -o "$temporary/$module.olean" "tests/cli/$stem.lean")
  if [ "$out" != "'$theorem' does not depend on any axioms" ]; then
    printf 'Unexpected output from Lean for %s: %s\n' "$stem" "$out" >&2
    exit 1
  fi
  LEAN="$lean" LEAN_PATH="$temporary" \
    bash scripts/export.sh "$temporary/$stem.ndjson" "$module" -- "$@" >/dev/null
  cmp "tests/cli/$stem.ndjson" "$temporary/$stem.ndjson"
  cmp "tests/cli/$stem.ndjson.manifest.json" "$temporary/$stem.ndjson.manifest.json"
}
reproduce chain LeanForthChain chain chain
reproduce unfold LeanForthUnfold impliesSelf Implies impliesSelf
reproduce inductive LeanForthInductive Two.cases Two.cases Two.swap
reproduce irrelevance LeanForthIrrelevance irrelevant irrelevant
printf '%s\n' 'Lean accepts chain, impliesSelf, Two.cases, Two.swap and irrelevant;' \
  'scripts/export.sh reproduces the four exports and their manifests.'

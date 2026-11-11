#!/usr/bin/env bash
# The command line's seven Lean fixtures with pinned Lean: Lean accepts
# tests/cli/chain.lean (larger than check --record holds), unfold.lean (a
# proof that needs a definition unfolded), irrelevance.lean (one that needs proof
# irrelevance), inductive.lean (an inductive
# type, a theorem proved with its recursor and a definition computed with
# it), sharing.lean (proofs that share subterms along 2^40 paths, whose
# wrong twins it rejects), sharing-universe.lean (such a statement
# instantiated at a universe argument, whose wrong twins it rejects) and
# nested.lean (nested inductive types through an indexed family and a
# mutual block, and theorems that reduce through their recursors), each
# without axioms, and scripts/export.sh reproduces the committed
# exports and their manifests byte for byte. LEAN names the pinned Lean
# 4.35.0 binary.
set -eu

lean=${LEAN:-lean}
temporary=$(mktemp -d)
# Delete exactly the files this script writes, by name, then the folder.
cleanup() {
  local name
  for name in LeanForthChain.olean LeanForthUnfold.olean LeanForthInductive.olean \
    LeanForthIrrelevance.olean LeanForthSharing.olean LeanForthSharingUniverse.olean \
    LeanForthNested.olean \
    chain.ndjson chain.ndjson.manifest.json unfold.ndjson unfold.ndjson.manifest.json \
    inductive.ndjson inductive.ndjson.manifest.json \
    irrelevance.ndjson irrelevance.ndjson.manifest.json \
    sharing.ndjson sharing.ndjson.manifest.json \
    sharing-universe.ndjson sharing-universe.ndjson.manifest.json \
    nested.ndjson nested.ndjson.manifest.json; do
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
reproduce sharing LeanForthSharing sharing sharedAnd sharedBeta sharing
reproduce sharing-universe LeanForthSharingUniverse useU sharedAndU useU
reproduce nested LeanForthNested RvNest.VT.size_two RvNest.VT.size_leaf RvNest.VT.size_two \
  RvNest.R.count_mk RvNest.AT RvNest.Q   # the theorem #print axioms names, then the roots
printf '%s\n' 'Lean accepts chain, impliesSelf, Two.cases, Two.swap, irrelevant,' \
  'sharedAnd, sharedBeta, sharing, sharedAndU, useU and the nested blocks of' \
  'nested.lean, and rejects their wrong twins; scripts/export.sh reproduces the' \
  'seven exports and their manifests.'

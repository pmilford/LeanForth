#!/usr/bin/env bash
# Inductive types, recursors, reductions and quotients against pinned Lean
# 4.35.0 (ADR 0015, docs/adr/0015-inductive-types.md; plan task 5.1.1).
#
# 1. inductive-expected.lean asks Lean's kernel for its verdict on 139 cases
#    (inductive declarations, reductions, Lean's replay of exported blocks,
#    primitive names, quotient initialisation). It fails unless every
#    verdict is the recorded one, and prints one row per case; the rows
#    must equal inductive-expected.tsv byte for byte. After the rows it
#    prints every case as an export, which tests/core/inductive-table.py
#    checks with LeanForth (plan task 5.2.1a); this script ignores them.
# 2. The three small exports of tests/reference/inductive/ are reproduced
#    with the toolchain's leanexport and must equal the committed files and
#    their manifests byte for byte: blocks.ndjson (from blocks.lean),
#    nat-add-zero.ndjson (the closure of Nat.add_zero and Nat.zero_add,
#    plan task 5.4.1) and axioms.ndjson (propext, Classical.choice,
#    Quot.sound and what they use).
# 3. Each committed export is staged by LeanForth's Forth importer
#    (src/import/stage.fs) with its manifest and re-emitted equal to the
#    reader's own dump (tests/core/compact-verify.sh).
#
# Usage, from the repository root:
#   LEAN=.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean \
#   GFORTH=.tools/gforth/bin/gforth bash tests/reference/inductive-check.sh
set -eu
lean=${LEAN:-lean}
gforth=${GFORTH:-.tools/gforth/bin/gforth}
version=$("$lean" --version)
case "$version" in
  'Lean (version 4.35.0,'*) ;;
  *) printf 'Expected Lean 4.35.0; got: %s\n' "$version" >&2; exit 1 ;;
esac
revision=$("$lean" --githash)
if [ "$revision" != eb6cafb7290e8bd5f2937522d8d804f58f02bafc ]; then
  printf 'Unexpected Lean revision: %s\n' "$revision" >&2
  exit 1
fi
here=tests/reference/inductive
work=$(mktemp -d)
trap 'rm -f "$work/out" "$work/rows" "$work/LeanForthBlocks.olean" "$work/LeanForthBlocks.ilean" \
  "$work/blocks.ndjson" "$work/blocks.ndjson.manifest.json" \
  "$work/nat-add-zero.ndjson" "$work/nat-add-zero.ndjson.manifest.json" \
  "$work/axioms.ndjson" "$work/axioms.ndjson.manifest.json" "$work/stage.out"; rmdir "$work"' EXIT

# 1. Kernel verdicts: the rows, before the cases written as exports (which
#    tests/core/inductive-table.py reads; plan task 5.2.1a).
if ! "$lean" -DwarningAsError=true tests/reference/inductive-expected.lean >"$work/out" 2>&1; then
  cat "$work/out" >&2
  printf '%s\n' 'A Lean kernel answer differs from inductive-expected.lean' >&2
  exit 1
fi
sed -n '/^ndjson-begin/q;p' "$work/out" >"$work/rows"
if ! cmp -s tests/reference/inductive-expected.tsv "$work/rows"; then
  diff -u tests/reference/inductive-expected.tsv "$work/rows" >&2 || true
  printf '%s\n' 'Kernel rows differ from inductive-expected.tsv' >&2
  exit 1
fi
rows=$(($(wc -l <"$work/rows") - 1))
printf 'Lean kernel answers match inductive-expected.tsv (%d cases).\n' "$rows"

# 2. The exports, reproduced byte for byte with their manifests.
same() {   # $1: committed export name; the fresh copy is in $work
  for f in "$1" "$1.manifest.json"; do
    if ! cmp -s "$here/$f" "$work/$f"; then
      diff -u "$here/$f" "$work/$f" >&2 || true
      printf 'Lean export differs from the committed %s\n' "$here/$f" >&2
      exit 1
    fi
  done
}
"$lean" -DwarningAsError=true -o "$work/LeanForthBlocks.olean" "$here/blocks.lean"
LEAN="$lean" LEAN_PATH="$work" bash scripts/export.sh "$work/blocks.ndjson" LeanForthBlocks -- \
  LeanForthBlocks.N LeanForthBlocks.Both LeanForthBlocks.Same LeanForthBlocks.Either \
  LeanForthBlocks.Even LeanForthBlocks.Tree LeanForthBlocks.Point.x >/dev/null
same blocks.ndjson
LEAN="$lean" bash scripts/export.sh "$work/nat-add-zero.ndjson" Init.Data.Nat.Basic -- \
  Nat.add_zero Nat.zero_add >/dev/null
same nat-add-zero.ndjson
LEAN="$lean" bash scripts/export.sh "$work/axioms.ndjson" Init -- \
  propext Classical.choice Quot.sound >/dev/null
same axioms.ndjson
printf '%s\n' 'Lean exports match blocks.ndjson, nat-add-zero.ndjson and axioms.ndjson with their manifests.'

# 3. Staged by the Forth importer, with the manifest checked.
for f in blocks nat-add-zero axioms; do
  if ! bash tests/core/compact-verify.sh "$here/$f.ndjson" "$gforth" 120 >"$work/stage.out" 2>&1; then
    cat "$work/stage.out" >&2
    printf 'The Forth importer did not stage %s exactly\n' "$here/$f.ndjson" >&2
    exit 1
  fi
done
printf '%s\n' 'The Forth importer stages all three exports exactly (manifests checked).'

#!/usr/bin/env bash
# Comparing under binders whose domains differ, against pinned Lean 4.35.0
# (plan task 2.1.2, docs/adr/0003-conversion.md "Amendment 1").
#
# binder-domains.lean checks every case in Lean's kernel: each comparison in
# both orders with Kernel.isDefEq after Kernel.check of both terms, each
# declaration with addDeclCore. It fails unless Lean gives the recorded
# answer, and prints one row per case; the rows must equal
# binder-domains.tsv byte for byte. That table also holds the answers
# LeanForth must give before and after the amendment (not checked by Lean).
#
# Usage, from the repository root:
#   LEAN=.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean \
#     bash tests/reference/binder-domains-check.sh
set -eu
. "$(dirname "${BASH_SOURCE[0]}")/../support/pinned-lean.sh"
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
output=$(mktemp)
trap 'rm -f "$output"' EXIT

if ! "$lean" -DwarningAsError=true tests/reference/binder-domains.lean >"$output" 2>&1; then
  cat "$output" >&2
  printf '%s\n' 'A Lean kernel answer differs from binder-domains.lean' >&2
  exit 1
fi
if ! cmp -s tests/reference/binder-domains.tsv "$output"; then
  diff -u tests/reference/binder-domains.tsv "$output" >&2 || true
  printf '%s\n' 'Kernel rows differ from binder-domains.tsv' >&2
  exit 1
fi
rows=$(($(wc -l <"$output") - 1))
compared=$(grep -c '^compare\.' "$output" || true)
printf 'Lean kernel answers match binder-domains.tsv (%d cases: %d comparisons, each in both orders, and %d declarations).\n' \
  "$rows" "$compared" "$((rows - compared))"

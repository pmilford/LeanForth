#!/usr/bin/env bash
# Definitional equality as Lean's kernel decides it, against pinned Lean 4.35.0
# (plan task 4.1.1, docs/adr/0014-definitional-equality.md).
#
# definitional-equality.lean adds each case to a scratch kernel environment
# with addDeclCore and kernel diagnostics on (or asks Kernel.whnf), and fails
# unless Lean gives the recorded verdict and, for an accepted declaration, the
# recorded number of unfoldings of each constant. It prints one row per case;
# the rows must equal definitional-equality.tsv byte for byte. The table also
# holds the answers LeanForth must give under ADR 0011 and ADR 0014 (checked
# by the Lean file only for not contradicting Lean, and for ADR 0014 equalling
# Lean's verdict outside the deferred features).
#
# Usage, from the repository root:
#   LEAN=.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean \
#     bash tests/reference/definitional-equality-check.sh
set -eu
lean=${LEAN:-lean}
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

if ! "$lean" -DwarningAsError=true tests/reference/definitional-equality.lean >"$output" 2>&1; then
  cat "$output" >&2
  printf '%s\n' 'A Lean kernel answer differs from definitional-equality.lean' >&2
  exit 1
fi
if ! cmp -s tests/reference/definitional-equality.tsv "$output"; then
  diff -u tests/reference/definitional-equality.tsv "$output" >&2 || true
  printf '%s\n' 'Kernel rows differ from definitional-equality.tsv' >&2
  exit 1
fi
rows=$(($(wc -l <"$output") - 1))
accepted=$(awk -F '\t' 'NR > 1 && $2 == "accepted"' "$output" | wc -l)
whnf=$(grep -c '^whnf\.' "$output" || true)
printf 'Lean kernel answers match definitional-equality.tsv (%d cases: %d accepted with their unfold counts, %d failures, %d whnf).\n' \
  "$rows" "$accepted" "$((rows - accepted - whnf))" "$whnf"

#!/usr/bin/env bash
# First-checker expected results against pinned Lean 4.35.0 (plan task 2.1.4,
# docs/adr/0011-definite-rejection.md, docs/reviews/FIRST_CHECKER_EXPECTED.md).
#
# 1. Lean accepts the five pinned fixtures.
# 2. first-checker-expected.lean checks each original and broken copy in
#    Lean's kernel, failing unless Lean gives the recorded verdict, and prints
#    one row per case; the rows must equal first-checker-expected.tsv byte for
#    byte. That table also holds the outcome LeanForth must give.
# 3. first-checker-invalid.lean holds broken copies as Lean source. Lean must
#    reject the file, report each line marked `-- expect <case>: <message>`
#    with that message ("Lean rejected this, as expected"), and report no
#    error on any other line. An error elsewhere, a marked line without its
#    message, or acceptance of the file fails the check.
#
# Usage, from the repository root:
#   LEAN=.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean \
#     bash tests/reference/first-checker-check.sh
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

for fixture in composition identity type-identity poly-identity constant-fixture; do
  "$lean" -DwarningAsError=true "tests/reference/$fixture.lean"
done
printf '%s\n' 'Lean accepted the five pinned fixtures.'

if ! "$lean" -DwarningAsError=true tests/reference/first-checker-expected.lean >"$output" 2>&1; then
  cat "$output" >&2
  printf '%s\n' 'A Lean kernel verdict differs from first-checker-expected.lean' >&2
  exit 1
fi
if ! cmp -s tests/reference/first-checker-expected.tsv "$output"; then
  diff -u tests/reference/first-checker-expected.tsv "$output" >&2 || true
  printf '%s\n' 'Kernel rows differ from first-checker-expected.tsv' >&2
  exit 1
fi
printf 'Lean kernel verdicts match first-checker-expected.tsv (%d cases).\n' \
  "$(($(wc -l <"$output") - 1))"

file=tests/reference/first-checker-invalid.lean
if "$lean" -DwarningAsError=true "$file" >"$output" 2>&1; then
  printf '%s\n' 'Broken source copies were unexpectedly accepted' >&2
  exit 1
fi
expected=$(grep -nE -- '-- expect [a-z-]+\.[a-z-]+: ' "$file" |
  sed -E 's/^([0-9]+):.*-- expect ([^:]+): (.*)$/\1\t\2\t\3/')
if [ -z "$expected" ]; then
  printf '%s\n' "No expected rejections found in $file" >&2
  exit 1
fi
count=0
while IFS=$'\t' read -r line name message; do
  if ! awk -v at="$file:$line:" -v message="$message" \
      'index($0, at) == 1 && index($0, ": error") && index($0, message) { found = 1 }
       END { exit !found }' "$output"; then
    cat "$output" >&2
    printf 'Lean did not reject %s (line %s) with "%s"\n' "$name" "$line" "$message" >&2
    exit 1
  fi
  printf 'Lean rejected %s, as expected: %s\n' "$name" "$message"
  count=$((count + 1))
done <<EOF
$expected
EOF
lines=$(printf '%s\n' "$expected" | cut -f1 | tr '\n' ' ')
unexpected=$(awk -v file="$file" -v lines="$lines" '
  BEGIN { n = split(lines, wanted, " "); for (i = 1; i <= n; i++) marked[wanted[i]] = 1 }
  index($0, file ":") == 1 {
    rest = substr($0, length(file) + 2)
    split(rest, part, ":")
    if (rest ~ /^[0-9]+:[0-9]+: error/ && !(part[1] in marked)) print
  }' "$output")
if [ -n "$unexpected" ]; then
  printf '%s\n' "$unexpected" >&2
  printf '%s\n' 'Lean reported errors on unmarked lines' >&2
  exit 1
fi
printf 'Lean rejected all %d broken source copies, each for the expected reason.\n' "$count"

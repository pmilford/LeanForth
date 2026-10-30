#!/usr/bin/env bash
set -eu
gforth=${GFORTH:-gforth}
"$gforth" tests/harness/pass.fs
output=$(mktemp)
trap 'rm -f "$output"' EXIT
for case_name in bad-value bad-depth; do
  if "$gforth" "tests/harness/$case_name.fs" >"$output" 2>&1; then
    printf 'Harness accepted %s\n' "$case_name" >&2
    exit 1
  fi
  case "$case_name" in
    bad-value) expected='INCORRECT RESULT' ;;
    bad-depth) expected='WRONG NUMBER OF RESULTS' ;;
  esac
  if ! grep -q "$expected" "$output"; then
    cat "$output" >&2
    printf 'Unexpected failure for %s\n' "$case_name" >&2
    exit 1
  fi
done
printf '%s\n' 'Forth tester accepted a passing suite and rejected both intentional failures.'

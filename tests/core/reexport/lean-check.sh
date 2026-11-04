#!/usr/bin/env bash
# The re-exporter against pinned Lean's own exports (`make reference-reexport`;
# docs/development/NDJSON_READER.md, "Re-export"). Run from the repository
# root with LEAN naming the pinned Lean 4.35.0 binary and GFORTH a Gforth.
# 1. Export tests/core/reexport/kinds.lean (every record kind) with the
#    pinned exporter and compare it with tests/core/reexport/kinds.ndjson,
#    byte for byte; with --write, write that fixture instead and stop.
# 2. Export tests/core/reexport/strings.lean (a string literal with every
#    class of byte the printer escapes apart), check that the export holds
#    the escapes as this script expects them, re-export it with
#    scripts/ndjson-reexport.sh --reimport and require identical bytes and
#    equal dumps. That export (about 11,000 lines) is not kept.
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
toolchain=$("$lean" --print-prefix)
fixture=tests/core/reexport/kinds.ndjson
temporary=$(mktemp -d)
trap 'rm -f "$temporary/LeanForthReexportKinds.olean" "$temporary/LeanForthReexportStrings.olean" \
  "$temporary/kinds.ndjson" "$temporary/strings.ndjson" "$temporary/strings-copy.ndjson"
  rmdir "$temporary"' EXIT

# export MODULE OUTPUT NAME...: the pinned exporter, with mdata and unsafe
# declarations, of the named constants and what they depend on.
export_names() {
  local module=$1 output=$2
  shift 2
  PATH="$toolchain/bin:$PATH" LEAN_PATH="$temporary" \
    "$toolchain/bin/leanexport" --export-mdata --export-unsafe "$module" -- "$@" >"$output"
}

"$lean" -DwarningAsError=true -o "$temporary/LeanForthReexportKinds.olean" \
  tests/core/reexport/kinds.lean
names=(big twice kept Small first pairType arrow parity hidden risky spin
  iffEq Even Odd Tree Wide Point '«with space»' '«quote"and\back»' αβγ)
export_names LeanForthReexportKinds "$temporary/kinds.ndjson" "${names[@]/#/ReexportKinds.}"
if [ "${1:-}" = --write ]; then
  cp "$temporary/kinds.ndjson" "$fixture"
  printf 'Wrote %s.\n' "$fixture"
  exit 0
fi
if ! cmp -s "$fixture" "$temporary/kinds.ndjson"; then
  printf 'Lean export differs from %s\n' "$fixture" >&2
  diff -u "$fixture" "$temporary/kinds.ndjson" >&2 || true
  exit 1
fi
printf 'Lean export of every record kind matches %s.\n' "$fixture"

"$lean" -DwarningAsError=true -o "$temporary/LeanForthReexportStrings.olean" \
  tests/core/reexport/strings.lean
export_names LeanForthReexportStrings "$temporary/strings.ndjson" ReexportStrings.text
expected='"strVal":"tab\u0009 nl\n cr\r bs\u0008 ff\u000c nul\u0000 us\u001f esc\u001b del'
if ! grep -qF "$expected" "$temporary/strings.ndjson"; then
  printf 'Lean writes the string literal with other escapes than expected\n' >&2
  grep -F '"strVal":"tab' "$temporary/strings.ndjson" >&2 || true
  exit 1
fi
GFORTH=${GFORTH:-gforth} bash scripts/ndjson-reexport.sh --reimport \
  "$temporary/strings.ndjson" "$temporary/strings-copy.ndjson"
printf '%s\n' 'Lean export of the string literal re-exports byte for byte.'

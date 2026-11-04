#!/usr/bin/env bash
# LeanForth's export step (plan task 3.2.6): export Lean declarations with
# the pinned toolchain's leanexport, then write the manifest beside the
# export (scripts/export_manifest.py), which LeanForth's reader checks by
# default (src/import/manifest.fs; docs/development/NDJSON_READER.md).
#
# Usage: scripts/export.sh OUTPUT.ndjson MODULE... [-- DECLARATION...]
#   The arguments after OUTPUT go to leanexport unchanged: the modules to
#   export, and after -- the declarations to keep (all when none).
#   Writes OUTPUT.ndjson and OUTPUT.ndjson.manifest.json; the export is
#   written to OUTPUT.ndjson.partial first and renamed only when leanexport
#   succeeds, so a failed export never leaves a file that looks complete.
# Environment:
#   LEAN            the pinned Lean 4.35.0 binary, never an elan proxy
#                   (default: the project's .tools toolchain)
#   LEAN_PATH       where leanexport finds the modules' .olean files, as for
#                   leanexport itself (for Mathlib: its .lake build folders)
#   MATHLIB_COMMIT  the Mathlib commit exported, recorded in the manifest
#                   (optional; 40 lowercase hexadecimal digits)
set -eu

here=$(cd "$(dirname "$0")/.." && pwd)
lean=${LEAN:-$here/.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean}
if [ $# -lt 2 ]; then
  sed -n '7,9p' "$0" >&2
  exit 2
fi
output=$1
shift

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

partial="$output.partial"
trap 'rm -f "$partial"' EXIT   # only this script's own partial file
PATH="$toolchain/bin:$PATH" "$toolchain/bin/leanexport" "$@" >"$partial"
mv "$partial" "$output"
python3 "$here/scripts/export_manifest.py" ${MATHLIB_COMMIT:+--mathlib-commit "$MATHLIB_COMMIT"} \
  "$output"
printf 'Wrote %s and %s.manifest.json\n' "$output" "$output"

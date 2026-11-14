#!/usr/bin/env bash
# LeanForth's elaboration-data export (plan row FE1d; ADR 0021 D10;
# docs/programming/ELABORATION_DATA.md): for the modules of a Lean export,
# run scripts/export_elab.lean with the pinned toolchain, then
# scripts/export_elab.py, which keeps the records of the export's own
# declarations and writes the file `leanforth check --elab-data` reads
# (format 3: with every smart-unfolding body and the match_pattern tag).
# A development tool, run when a library is exported, like scripts/export.sh
# (owner decision of 2026-11-12, "Front-end syntax", answer 8); a user who
# only checks LeanForth text needs no Lean.
#
# Usage: scripts/export-elab.sh OUTPUT EXPORT MODULE...
#   EXPORT is the export made by scripts/export.sh for the same modules,
#   with its manifest beside it (its SHA-256 goes into OUTPUT's header).
#   Writes OUTPUT only when both steps succeed (OUTPUT.partial first), then
#   names OUTPUT's records SHA-256 in EXPORT's manifest (elab_records_sha256,
#   S1 note M6): `leanforth check` refuses any other data for that export.
# Environment:
#   LEAN       the pinned Lean 4.35.0 binary, never an elan proxy (default:
#              the project's .tools toolchain)
#   LEAN_PATH  where Lean finds the modules' .olean files, as for
#              scripts/export.sh (Init needs none)
set -eu

here=$(cd "$(dirname "$0")/.." && pwd)
lean=${LEAN:-$here/.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean}
if [ $# -lt 3 ]; then
  sed -n '11,16p' "$0" >&2
  exit 2
fi
output=$1
export_file=$2
shift 2

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

raw=$(mktemp)
trap 'rm -f "$raw"' EXIT   # only this script's own temporary file
PATH="$toolchain/bin:$PATH" "$lean" -DwarningAsError=true --run \
  "$here/scripts/export_elab.lean" "$@" >"$raw"
python3 "$here/scripts/export_elab.py" "$raw" "$export_file" "$output" --bind

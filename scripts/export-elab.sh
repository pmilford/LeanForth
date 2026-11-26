#!/usr/bin/env bash
# LeanForth's elaboration-data export (plan row FE1d; ADR 0021 D10;
# docs/programming/ELABORATION_DATA.md): for the modules of a Lean export,
# run scripts/export_elab.lean with the pinned toolchain, then
# scripts/export_elab.py, which keeps the records of the export's own
# declarations and writes the file `leanforth check --elab-data` reads
# (format 3 or 3.1: every smart-unfolding body, the match_pattern tag; with
# ELAB_FORMAT=4, format 4: also the @[congr] lemmas and defeq tags simp reads,
# docs/design/SIMP_DATA.md section 3, slice SD-a of docs/design/TACTIC_SIMP.md;
# with ELAB_FORMAT=4.1, format 4.1: also the congruence theorems Lean
# realized in the library, slice SD-b). The simp records are
# scripts/export_simp.lean's, whose output joins export_elab.lean's under
# its header (which says "simp": true) before the finisher reads both.
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
#   ELAB_FORMAT  3 (the default), 4 or 4.1
set -eu

here=$(cd "$(dirname "$0")/.." && pwd)
lean=${LEAN:-$here/.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean}
if [ $# -lt 3 ]; then
  sed -n '14,19p' "$0" >&2
  exit 2
fi
output=$1
export_file=$2
shift 2
case ${ELAB_FORMAT:-3} in
  3) simp= ;;
  4|4.1) simp=yes ;;
  *) printf 'ELAB_FORMAT is 3, 4 or 4.1, not %s\n' "$ELAB_FORMAT" >&2; exit 2 ;;
esac

# Never run an elan proxy, nor anything not known to be a toolchain's Lean
# (scripts/lean_pin.py, review F5): it is judged before it is asked its version.
python3 "$here/scripts/lean_pin.py" check "$lean" || exit 1
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
simp_raw=$(mktemp)
joined=$(mktemp)
trap 'rm -f "$raw" "$simp_raw" "$joined"' EXIT   # only this script's own temporary files
PATH="$toolchain/bin:$PATH" "$lean" -DwarningAsError=true --run \
  "$here/scripts/export_elab.lean" "$@" >"$raw"
if [ -n "$simp" ]; then
  PATH="$toolchain/bin:$PATH" "$lean" -DwarningAsError=true --run \
    "$here/scripts/export_simp.lean" "$@" >"$simp_raw"
  # Both programs ran on the same modules with the same Lean: the simp
  # header is the plain one with "simp": true last (Lean sorts the keys).
  # The key's name comes from a variable: a quoted folder name on this line would
  # make scripts/changed-tests.py count src/front/simp as this script's input.
  key=simp
  if [ "$(head -n 1 "$raw" | sed 's/}$/,"'"$key"'":true}/')" != "$(head -n 1 "$simp_raw")" ]; then
    printf 'export_elab.lean and export_simp.lean disagree on Lean or the modules\n' >&2
    exit 1
  fi
  { head -n 1 "$simp_raw"; tail -n +2 "$raw"; tail -n +2 "$simp_raw"; } >"$joined"
  cp "$joined" "$raw"
fi
# Formats 4 and 4.1 are finished by export_simp.py, which hands every record
# but the default simp set's to export_elab.py's finish() and, for 4.1, adds
# the default set's (export_elab.py itself is not changed: its digest keys the
# Mathlib slice's data step).
if [ -n "$simp" ]; then
  python3 "$here/scripts/export_simp.py" "$raw" "$export_file" "$output" --bind \
    --format "$ELAB_FORMAT"
else
  python3 "$here/scripts/export_elab.py" "$raw" "$export_file" "$output" --bind \
    --format "${ELAB_FORMAT:-3}"
fi

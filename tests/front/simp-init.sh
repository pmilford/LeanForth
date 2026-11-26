#!/usr/bin/env bash
# by-simp on Init's one-line simp proofs against pinned Lean (simp group 4, pass 3; make
# reference-simp-init, part of make daily only): Init exported with the pinned leanexport
# (checked by its SHA-256, as tests/front/synth-init.sh), its format-4.1 elaboration data
# written by scripts/export-elab.sh, pinned Lean's re-run of the one-line simp proofs with each
# theorem as LeanForth text (tests/front/simp-init.lean), then tests/front/check_simp_init.py:
# every text run by tests/front/simp-init.fs, the ones that ran checked by bin/leanforth's check
# against Init's snapshot (SNAPSHOT, which make parallel-init writes), each accepted term
# compared with Lean's node for node. Needs pinned Lean 4.35.0 (LEAN), Gforth 1.0 (GFORTH;
# gforth-fast beside it for the check) and Python 3. INIT_EXPORT, when set, is an Init export
# of that SHA-256 to use instead of a new one (its manifest is copied, never written).
# Without the snapshot a user's run says SKIPPED, NOT RUN and exits 0; a recorded run
# (REQUIRE_INIT_SNAPSHOT=1) fails.
# Usage: LEAN=... GFORTH=... bash tests/front/simp-init.sh SNAPSHOT
set -eu
snapshot=$1
if [ ! -f "$snapshot" ]; then
  if [ "${REQUIRE_INIT_SNAPSHOT:-}" = 1 ]; then
    printf 'reference-simp-init: FAILED, NOT RUN: no Init snapshot at %s (make parallel-init writes it)\n' \
      "$snapshot" >&2
    exit 1
  fi
  printf 'reference-simp-init: SKIPPED, NOT RUN: no Init snapshot at %s; make daily requires it\n' \
    "$snapshot"
  exit 0
fi
lean=$(python3 "$(dirname "$0")/../../scripts/lean_pin.py" pinned)   # $LEAN or the pinned Lean, never a proxy
toolchain=$("$lean" --print-prefix)
leanexport=${LEANEXPORT:-$toolchain/bin/leanexport}
work=$(mktemp -d)
names="init.ndjson init.ndjson.manifest.json init.elab.ndjson lean.ndjson"
trap 'for n in $names; do rm -f "$work/$n"; done; rm -rf "$work/run"; rmdir "$work"' EXIT
if [ -n "${INIT_EXPORT:-}" ]; then
  ln -s "$(cd "$(dirname "$INIT_EXPORT")" && pwd)/$(basename "$INIT_EXPORT")" "$work/init.ndjson"
else
  PATH="$toolchain/bin:$PATH" "$leanexport" Init >"$work/init.ndjson"
fi
digest=$(sha256sum "$work/init.ndjson" | cut -c1-64)
if [ "$digest" != c1b2071a6d2132ace8c4711499f078aab2117d925213d5a222a1fe843a59a179 ]; then
  printf 'Unexpected Init export: %s\n' "$digest" >&2
  exit 1
fi
python3 scripts/export_manifest.py "$work/init.ndjson"
ELAB_FORMAT=4.1 LEAN="$lean" bash scripts/export-elab.sh "$work/init.elab.ndjson" "$work/init.ndjson" \
  Init >/dev/null
PATH="$toolchain/bin:$PATH" "$lean" -DwarningAsError=true --run tests/front/simp-init.lean >"$work/lean.ndjson"
python3 tests/front/check_simp_init.py "$work/lean.ndjson" "$work/init.ndjson" "$work/init.elab.ndjson" \
  "$snapshot" "$work/run"

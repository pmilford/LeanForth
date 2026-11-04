#!/usr/bin/env bash
# The compact store's load test on Lean's own Init (ADR 0016): export Init
# with the pinned leanexport, check the export is the one ADR 0016 and the
# NDJSON reader's notes measured, then load it into the compact store and
# compare the re-emission with the reader's dump, family by family
# (tests/core/compact-verify.sh). Uses gforth-fast beside $GFORTH when there
# is one. Needs pinned Lean 4.35.0 (LEAN) and Gforth (GFORTH).
set -eu
lean=${LEAN:-lean}
gforth=${GFORTH:-gforth}
version=$("$lean" --version)
case "$version" in
  'Lean (version 4.35.0,'*) ;;
  *) printf 'Expected Lean 4.35.0; got: %s\n' "$version" >&2; exit 1 ;;
esac
toolchain=$("$lean" --print-prefix)
fast="$(dirname "$gforth")/gforth-fast"
if [ -x "$fast" ]; then gforth=$fast; fi
temporary=$(mktemp -d)
trap 'rm -f "$temporary/init.ndjson"; rmdir "$temporary"' EXIT
PATH="$toolchain/bin:$PATH" "$toolchain/bin/leanexport" Init >"$temporary/init.ndjson"
digest=$(sha256sum "$temporary/init.ndjson" | cut -c1-64)
if [ "$digest" != c1b2071a6d2132ace8c4711499f078aab2117d925213d5a222a1fe843a59a179 ]; then
  printf 'Unexpected Init export: %s\n' "$digest" >&2
  exit 1
fi
bash tests/core/compact-verify.sh "$temporary/init.ndjson" "$gforth" 900

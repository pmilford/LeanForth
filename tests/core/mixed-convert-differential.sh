#!/usr/bin/env bash
# Lean N means unequal; Forth U is inconclusive and is never treated as N.
set -eu
lean=${LEAN:-lean}
gforth=${GFORTH:-gforth}
case "$("$lean" --version)" in 'Lean (version 4.35.0,'*) ;; *) printf '%s\n' 'Expected Lean 4.35.0' >&2; exit 1 ;; esac
if [ "$("$lean" --githash)" != eb6cafb7290e8bd5f2937522d8d804f58f02bafc ]; then
  printf '%s\n' 'Unexpected Lean revision' >&2; exit 1
fi
temporary=$(mktemp -d)
trap 'rm -f "$temporary/lean.txt" "$temporary/forth.txt"; rmdir "$temporary"' EXIT
"$lean" tests/reference/mixed-convert-table.lean >"$temporary/lean.txt"
"$gforth" tests/core/mixed-convert-table.fs >"$temporary/forth.txt"
python3 - "$temporary/lean.txt" "$temporary/forth.txt" <<'PY'
import sys
from pathlib import Path
lean = [line.split() for line in Path(sys.argv[1]).read_text().splitlines()]
forth = [line.split() for line in Path(sys.argv[2]).read_text().splitlines()]
if len(lean) != 7 or len(forth) != 7:
    raise SystemExit("Unexpected mixed conversion table size")
for i, (lrow, frow) in enumerate(zip(lean, forth)):
    if len(lrow) != 2 or len(frow) != 2 or lrow[0] != str(i) or frow[0] != str(i):
        raise SystemExit(f"Malformed conversion row {i}")
    if lrow[1] not in ("E", "N") or frow[1] not in ("E", "U"):
        raise SystemExit(f"Unexpected conversion status at {i}")
    if frow[1] == "E" and lrow[1] != "E":
        raise SystemExit(f"False equality at {i}")
print(f"Seven Lean comparisons: {sum(row[1] == 'E' for row in forth)} Forth equal, "
      f"{sum(row[1] == 'U' for row in forth)} unknown; no false equality.")
PY

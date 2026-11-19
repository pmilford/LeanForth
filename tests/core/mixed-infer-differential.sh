#!/usr/bin/env bash
# Finite inference observations under an assumed candidate; no theorem claims.
set -eu
. "$(dirname "${BASH_SOURCE[0]}")/../support/pinned-lean.sh"
gforth=${GFORTH:-.tools/gforth/bin/gforth}
version=$("$lean" --version)
case "$version" in 'Lean (version 4.35.0,'*) ;; *) printf '%s\n' 'Expected Lean 4.35.0' >&2; exit 1 ;; esac
revision=$("$lean" --githash)
if [ "$revision" != eb6cafb7290e8bd5f2937522d8d804f58f02bafc ]; then
  printf '%s\n' 'Unexpected Lean revision' >&2; exit 1
fi
temporary=$(mktemp -d)
trap 'rm -f "$temporary/lean.txt" "$temporary/forth.txt"; rmdir "$temporary"' EXIT
"$lean" -DwarningAsError=true tests/reference/mixed-infer-differential.lean >"$temporary/lean.txt"
"$gforth" tests/core/mixed-infer-differential.fs >"$temporary/forth.txt"
if [ "$(wc -l <"$temporary/lean.txt")" -ne 21 ] || [ "$(wc -l <"$temporary/forth.txt")" -ne 21 ]; then
  printf '%s\n' 'Unexpected differential table size' >&2; exit 1
fi
python3 - "$temporary/lean.txt" "$temporary/forth.txt" <<'PY'
import sys
from pathlib import Path
lean = [line.split() for line in Path(sys.argv[1]).read_text().splitlines()]
forth = [line.split() for line in Path(sys.argv[2]).read_text().splitlines()]
for i, (lrow, frow) in enumerate(zip(lean, forth)):
    expected_key = [str(i // 7), str(i % 7)]
    expected_lean = "ACCEPT" if i % 7 < 4 else "REJECT"
    # Case 4 applies id.{u} to Sort u, a type one universe too high: rule D1
    # of ADR 0011 rejects it; case 5's constant has no candidate signature.
    expected_forth = ("OK" if i % 7 < 4 else "INVALID" if i % 7 == 6
                      else "REJECTED" if i % 7 == 4 else "UNKNOWN")
    if lrow != expected_key + [expected_lean] or frow != expected_key + [expected_forth]:
        raise SystemExit(f"Unexpected observation at case {i}: Lean={lrow}, Forth={frow}")
print("21 finite cases: independent Lean verdicts and expected Forth statuses matched.")
PY

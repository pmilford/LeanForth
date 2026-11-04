#!/bin/bash
# Correctness mode against today's golden IR: the prototype loads the REAL
# source files, unchanged, and its output must equal tests/program/ir/*.ir
# byte for byte. Usage: golden.sh GFORTH (from the repository root).
here=$(dirname "$0")
g=$1
status=0
for pair in src/program/clamp.fs:tests/program/ir/clamp.ir \
            src/program/examples.fs:tests/program/ir/examples.ir \
            tests/program/ir/all-primitives.fs:tests/program/ir/all-primitives.ir; do
  src=${pair%%:*}; gold=${pair##*:}
  out=$(bash "$here/ir-of.sh" "$g" "$src" 2>/dev/null)
  last=$(printf '%s\n' "$out" | tail -n 1)
  if [ "$last" != "outcome 0 " ]; then
    echo "FAIL $src: $last"; status=1; continue
  fi
  if printf '%s\n' "$out" | sed '$d' | cmp -s - "$gold"; then
    echo "identical: $src -> $gold ($(wc -l < "$gold") lines, sha256 $(sha256sum < "$gold" | cut -c1-16)...)"
  else
    echo "DIFFERENT: $src -> $gold"; printf '%s\n' "$out" | sed '$d' | diff - "$gold" | head -20; status=1
  fi
done
exit $status

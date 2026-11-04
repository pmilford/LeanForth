#!/bin/bash
# The draft IR v1 words (defining words and loops) in both designs, on one
# Gforth: run mode of the demo, its IR in the alias design and with the
# mode shift (they must be identical), IR 0.1's golden files unchanged
# with v1.fs loaded, and the edge inputs (identical diagnostics).
# Usage: v1.sh GFORTH (from the repository root).
here=$(dirname "$0")
g=$1
status=0
tmp=$(mktemp -d)
echo "-- run mode"
timeout -k 5 60 "$g" "$here/v1-demo.fs" "$here/v1-run.fs" </dev/null 2>/dev/null || status=1
echo "-- correctness mode: alias (cv) and mode shift (ms)"
for m in cv ms; do
  bash "$here/v1-of.sh" "$g" $m "$here/v1-demo.fs" 2>/dev/null > "$tmp/demo-$m.ir"
  echo "$m: $(tail -n 1 "$tmp/demo-$m.ir"), $(grep -c . "$tmp/demo-$m.ir") lines"
done
cmp -s "$tmp/demo-cv.ir" "$tmp/demo-ms.ir" && echo "IR v1 identical in both designs" \
  || { echo "IR v1 differs"; status=1; }
echo "-- IR 0.1 golden files with v1.fs loaded"
for m in cv ms; do
  for pair in src/program/clamp.fs:tests/program/ir/clamp.ir \
              src/program/examples.fs:tests/program/ir/examples.ir; do
    out=$(bash "$here/v1-of.sh" "$g" $m "${pair%%:*}" 2>/dev/null | sed '$d')
    if [ "$out" = "$(cat "${pair##*:}")" ]; then echo "$m ${pair%%:*}: identical"
    else echo "$m ${pair%%:*}: DIFFERENT"; status=1; fi
  done
done
echo "-- edge inputs"
for m in cv ms; do
  timeout -k 5 60 "$g" "$here/cv.fs" "$here/ms.fs" "$here/v1.fs" -e "' $m-run constant adv-mode" \
    "$here/v1-adversarial.fs" </dev/null 2>/dev/null > "$tmp/adv-$m.txt"
done
cat "$tmp/adv-cv.txt"
cmp -s "$tmp/adv-cv.txt" "$tmp/adv-ms.txt" && echo "diagnostics identical in both designs" \
  || { echo "diagnostics differ"; diff "$tmp/adv-cv.txt" "$tmp/adv-ms.txt"; status=1; }
cat "$tmp/demo-cv.ir" > "$here/v1-demo.ir"
rm -r "$tmp"
exit $status

#!/bin/bash
# The alias vocabulary and the two mode-shift prototypes side by side, on
# one Gforth: golden IR, today's reader tests and the hostile inputs; the
# hostile inputs must give the same diagnostics in every mode.
# Usage: modes.sh GFORTH (from the repository root). g1 needs Gforth 1.0.
here=$(dirname "$0")
g=$1
status=0
modes="cv ms"
"$g" --version 2>&1 | grep -q '^gforth 1\.' && modes="cv ms g1"
tmp=$(mktemp -d)
for m in $modes; do
  echo "-- mode $m"
  OF=$m-of.sh; [ "$m" = cv ] && OF=ir-of.sh
  OF=$OF bash "$here/golden.sh" "$g" || status=1
  python3 "$here/reader_cases.py" "$g" "$m" | tail -n 3 || status=1
  bash "$here/adversarial.sh" "$g" "$m" > "$tmp/$m.txt"
  tail -n 1 "$tmp/$m.txt"
  if ! cmp -s "$tmp/cv.txt" "$tmp/$m.txt"; then
    echo "hostile inputs: diagnostics differ from mode cv"; diff "$tmp/cv.txt" "$tmp/$m.txt"; status=1
  else
    echo "hostile inputs: diagnostics identical to mode cv"
  fi
done
rm -r "$tmp"
# A polluted host: MAX redefined (as MIN) before the run, so run mode on
# this image would compute the wrong clamp. The alias vocabulary finds its
# own MAX by name and cannot see it; the mode shift knows Forth's MAX by
# its identity and refuses.
echo "-- MAX redefined before the run"
for m in $modes; do
  files="$here/cv.fs"; run=cv-run-file
  [ "$m" != cv ] && files="$files $here/ms.fs" && run=ms-run-file
  [ "$m" = g1 ] && files="$files $here/ms-gforth1.fs" && run=g1-run-file
  # shellcheck disable=SC2086
  out=$(timeout -k 5 60 "$g" $files -e ": max min ;" \
        -e "true cv-quiet ! s\" src/program/clamp.fs\" $run .\" outcome \" . cr bye" \
        </dev/null 2>/dev/null)
  echo "mode $m: $(echo "$out" | tr '\n' ' ')"
done
exit $status

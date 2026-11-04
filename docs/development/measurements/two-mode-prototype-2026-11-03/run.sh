#!/bin/bash
# Every check of the ADR 0019 prototype, on one Gforth.
# Usage: run.sh GFORTH (from the repository root). Exit 0 if all pass.
here=$(dirname "$0")
g=$1
status=0
echo "== host: $("$g" --version 2>&1 | head -n 1)"
echo "== 1. correctness mode against the golden IR"
bash "$here/golden.sh" "$g" || status=1
echo "== 2. run mode: the same files in plain Forth"
bash "$here/run-mode.sh" "$g" 2>&1 | grep -v warning || status=1
echo "== 3. today's reader tests, replayed"
python3 "$here/reader_cases.py" "$g" | tail -n 5 || status=1
echo "== 4. adversarial inputs"
timeout -k 5 60 "$g" "$here/cv.fs" "$here/adversarial.fs" </dev/null 2>/dev/null | tail -n 1
echo "== 5. round trip IR -> Forth -> IR, awkward names"
python3 "$here/roundtrip.py" "$g" tests/program/ir/clamp.ir tests/program/ir/examples.ir \
  tests/program/ir/all-primitives.ir "$here/awkward.ir" || status=1
echo "== 6. planted faults in a copy of the vocabulary"
for planted in 's/s" else" f-if f-else cv-turn/s" then" f-if f-else cv-turn/' \
               's/cv-digits if negate true else false then exit/cv-digits if true else false then exit/' \
               's/2r> cv-fold align ;/2r> 2drop align ;/' \
               's/cv-tok# @ 31 > if why-long-name/cv-tok# @ 99 > if why-long-name/'; do
  fault=$(mktemp -d)
  cp "$here"/*.fs "$here"/*.sh "$here"/*.py "$here"/*.ir "$fault/"
  sed -i "$planted" "$fault/cv.fs"
  cmp -s "$here/cv.fs" "$fault/cv.fs" && { echo "fault not planted: $planted"; status=1; }
  golden=$(bash "$fault/golden.sh" "$g" 2>/dev/null | grep -c -E 'DIFFERENT|FAIL')
  cases=$(python3 "$fault/reader_cases.py" "$g" 2>/dev/null | grep -c '^DIFF')
  echo "fault $planted: golden files differing $golden of 3, replayed reader checks differing $cases"
  [ "$golden$cases" = 00 ] && status=1
  rm -r "$fault"
done
echo "== 7. symbolic mode (question 4(b)), clamp and examples"
bash "$here/sym-of.sh" "$g" src/program/clamp.fs 2>/dev/null
bash "$here/sym-of.sh" "$g" src/program/examples.fs 2>/dev/null
exit $status

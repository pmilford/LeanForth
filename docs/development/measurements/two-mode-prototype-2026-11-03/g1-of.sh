#!/bin/bash
# Mode shift on Gforth 1.0 only: Gforth's own interpreter in a third state
# (ms-gforth1.fs). Usage: g1-of.sh GFORTH-1.0 SOURCE (from the repository
# root). The last line is "outcome N", as in ir-of.sh.
here=$(dirname "$0")
exec timeout -k 5 60 "$1" "$here/cv.fs" "$here/ms.fs" "$here/ms-gforth1.fs" \
  -e "s\" $2\" g1-run-file .\" outcome \" . cr bye" </dev/null

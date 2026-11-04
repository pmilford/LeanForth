#!/bin/bash
# Draft IR v1 for one source file, in either design: MODE cv (alias
# vocabulary) or ms (mode shift). Usage: v1-of.sh GFORTH MODE SOURCE (from
# the repository root). The last line is "outcome N".
here=$(dirname "$0")
run=v1-run-file; [ "$2" = ms ] && run=v1-ms-run-file
exec timeout -k 5 60 "$1" "$here/cv.fs" "$here/ms.fs" "$here/v1.fs" \
  -e "s\" $3\" $run .\" outcome \" . cr bye" </dev/null

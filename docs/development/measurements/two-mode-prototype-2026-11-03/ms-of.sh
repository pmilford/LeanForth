#!/bin/bash
# Mode shift (portable third interpreter state): the IR one source file
# gives in verification state. Usage: ms-of.sh GFORTH SOURCE (from the
# repository root). The last line is "outcome N", as in ir-of.sh.
here=$(dirname "$0")
exec timeout -k 5 60 "$1" "$here/cv.fs" "$here/ms.fs" \
  -e "s\" $2\" ms-run-file .\" outcome \" . cr bye" </dev/null

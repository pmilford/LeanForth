#!/bin/bash
# Symbolic mode (ADR 0019, question 4(b)): the paths of each word of one
# source file. Usage: sym-of.sh GFORTH SOURCE (from the repository root).
here=$(dirname "$0")
exec timeout -k 5 60 "$1" "$here/cv.fs" "$here/sym.fs" \
  -e "s\" $2\" sym-run-file .\" outcome \" . cr bye" </dev/null

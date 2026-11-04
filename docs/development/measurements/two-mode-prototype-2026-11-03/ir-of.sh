#!/bin/bash
# Correctness mode: print the IR the prototype vocabulary emits for one
# source file. Usage: ir-of.sh GFORTH SOURCE (run from the repository root).
# The last line is "outcome N" (0 ok, 1 invalid, 2 unsupported, 3 full).
here=$(dirname "$0")
exec timeout -k 5 60 "$1" "$here/cv.fs" -e "s\" $2\" cv-run-file .\" outcome \" . cr bye" </dev/null

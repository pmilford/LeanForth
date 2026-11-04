#!/bin/bash
# Run mode: plain Forth loads the two unchanged source files with its own
# interpreter and words, then run-mode.fs calls the six words.
# Usage: run-mode.sh GFORTH (from the repository root).
here=$(dirname "$0")
sha256sum src/program/clamp.fs src/program/examples.fs
exec timeout -k 5 60 "$1" src/program/clamp.fs src/program/examples.fs "$here/run-mode.fs" </dev/null

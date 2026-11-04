#!/usr/bin/env bash
# The trial digest: 2,000 checker trials of 300 steps each
# (tests/support/trial-digest.fs), run with gforth-fast, and the first 12
# hex digits of the MD5 digest of their output. A change meant to keep the
# checker's behaviour keeps it; reports quote it (for example 175cba45dbdc
# for main cae8075). Takes about 15 s.
#
# Usage, from the repository root (any of the three numbers may be given):
#   bash scripts/trial-digest.sh [FIRST [N [STEPS]]]
# GFORTH_FAST names the engine (default .tools/gforth/bin/gforth-fast, else
# gforth-fast on the PATH).
set -eu
first=${1:-1} n=${2:-2000} steps=${3:-300}
engine=${GFORTH_FAST:-}
if [ -z "$engine" ]; then
  if [ -x .tools/gforth/bin/gforth-fast ]; then engine=.tools/gforth/bin/gforth-fast
  else engine=gforth-fast; fi
fi
"$engine" tests/support/trial-digest.fs -e "$first $n $steps trials .tally bye" </dev/null \
  | md5sum | cut -c1-12

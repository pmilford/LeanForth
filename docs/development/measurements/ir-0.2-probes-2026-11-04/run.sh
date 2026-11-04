#!/bin/bash
# Run the IR 0.2 probes (ADR 0019 Amendment 1) on one Gforth and print what
# each writes to standard output; standard error (Gforth's warnings) is
# kept apart, then shown filtered to the lines that are not "original
# location" notes.
#   bash docs/development/measurements/ir-0.2-probes-2026-11-04/run.sh GFORTH
# GFORTH is the path of a Gforth binary or wrapper script, for example
# .tools/gforth/bin/gforth. Run from the repository root or this folder.
set -u
gforth=$(realpath "$1")
cd "$(dirname "$0")"
err=$(mktemp)
trap 'rm -f "$err"' EXIT
echo "== host: $("$gforth" --version 2>&1 </dev/null | head -n 1)"
for probe in p0*.fs; do
  echo "== $probe"
  timeout -k 5 30 "$gforth" "$probe" </dev/null 2>"$err"
  echo "== exit $?"
  echo "== $probe, standard error without 'original location' lines:"
  grep -v 'original location' "$err" | sed -e 's|/[^ ]*/share/gforth/[^ ]*/||'
done

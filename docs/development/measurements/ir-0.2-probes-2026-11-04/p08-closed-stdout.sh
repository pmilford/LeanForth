#!/bin/bash
# IR 0.2 probe 8 (ADR 0019 Amendment 1): what an output word does when
# standard output is closed or is a pipe whose reader has gone. The Forth
# text prints 5 with . once, then 100,000 times (more than any output
# buffer), each time under CATCH; after each, if Forth is still running,
# it writes the THROW code to standard error, and it leaves with exit
# code 3.
#   bash docs/development/measurements/ir-0.2-probes-2026-11-04/p08-closed-stdout.sh GFORTH
set -u
gforth=$(realpath "$1")
text=': print-once 5 . ;  : print-many 100000 0 do 5 . loop ;
: report ( code -- ) stderr to outfile-id ." THROW code " . cr stdout to outfile-id ;
'"' print-once catch report  ' print-many catch report  3 (bye)"
echo "== host: $("$gforth" --version 2>&1 </dev/null | head -n 1)"
echo "== standard output closed:"
timeout -k 5 30 "$gforth" -e "$text" </dev/null >&-
echo "== exit $?"
echo "== standard output a pipe already closed by its reader:"
timeout -k 5 30 "$gforth" -e "1000 ms $text" </dev/null | true
echo "== exit ${PIPESTATUS[0]}"

\ The trial digest (plan task 6.2.0; review rvKC): checker trials of
\ checker-trial.fs -- random terms, levels, names and references through
\ inference, conversion, comparison, beta, shift, instantiation, the level
\ passes, universe substitution, the signature index and the definition
\ probe, each step folding every outcome, result, fuel, count and
\ diagnostic into a digest -- printed one line per trial, then the mix of
\ outcomes. A change meant to keep behaviour keeps this output byte for
\ byte; scripts/trial-digest.sh prints its MD5 digest's first 12 hex
\ digits, the "trial digest" that agents' reports quote.
\ Usage: gforth-fast tests/support/trial-digest.fs -e "FIRST N STEPS trials .tally bye"
include ./tester.fs
include ./checks.fs
require ../../src/lib/task.fs
require ../../src/kernel/mixed-definition-probe.fs
require ../../src/kernel/env-publish.fs
include ./plain-terms.fs
include ./plain-cases.fs
include ./checker-trial.fs
create tally 8 cells allot  tally 8 cells erase
: count-outcome ( outcome -- outcome )
  dup 0 7 within if dup cells tally + else tally 7 cells + then 1 swap +! ;
' count-outcome is checked
: trials ( first n steps -- )
  >r over + swap ?do i r@ 0 trial-start trial-run i 0 .r space digest 0 .r cr loop r> drop ;
: .tally ( -- ) ." TALLY" 8 0 do space i cells tally + @ 0 .r loop cr ;

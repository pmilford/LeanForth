\ Resource test of tactic batch 3a (plan row TB2; class 5 of
\ docs/development/TEST_COVERAGE_REVIEW.md), apart from batch-d's
\ test.fs so that no test file runs past 30 s: by-change at a hypothesis
\ through LeanForth text (tests/support/tactic-text.fs) with every heap
\ allocation of the run refused in turn (about 3,000 runs): accepted, or
\ full, never another error, and change's frames given back.
require ../../../support/tester.fs
include ../../../support/heap-watch.fs
include ../../../support/meta-sweeps.fs
require ../../../../src/load/checker.fs
require ../../../../src/load/front.fs
require ../../../../src/cli/check-lf.fs
require ../../../support/tactic-text.fs
decimal

4000000 lf-term-capacity! drop  100000 lf-cref-capacity! drop
T{ s" tests/front/decide-slice.ndjson" true lfc-library-open -> outcome-ok }T
T{ s" tests/front/decide-slice.elab.ndjson" lfc-elab-file! lfc-elab-read lfc-rooms
   -> outcome-ok outcome-ok }T
lf-author-begin
: frames-anew ( -- ) mat-frames sweep-slab-anew mrw-frames sweep-slab-anew
  tl-frames sweep-slab-anew mrv-frames sweep-slab-anew mti-frames sweep-slab-anew
  tlc-frames sweep-slab-anew ;
' frames-anew sweep-slabs-xt !
: p-change-text ( x -- code outcome )
  drop s" Nat explicit: a Nat explicit: b Nat explicit: c a 0 + b = explicit: h a b ="
  s\" a b = by-change at[ h ]\n ' h by-exact" text-full ;
T{ 0 ' p-change-text heap-sweep swept? tlc-frames slab-count -> true 0 }T
lf-tac-forget
.( batch-d-sweep test.fs: all tests passed) cr

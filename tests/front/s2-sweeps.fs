\ Resource sweeps of S2's tactics (plan S2, branch s2-tactics) through
\ the text's run of `leanforth check FILE.lf` (src/cli/check-lf.fs's
\ lfc-run) over tests/front/s2-slice.ndjson and its elaboration data;
\ run by tests/front/check_s2.py. tests/front/01-zero-add-rw.lf
\ (induction, rfl, rw [Nat.add_succ, ih] and its with_reducible rfl):
\ 1. the heap refusing its k-th allocation, for every k until a run
\    elaborates: each refused run ends full, never ok, and nothing it
\    left changes the next run;
\ 2. the declaration's elaboration fuel (--elab-fuel) at every limit
\    from 1 until a run elaborates: each
\    run that runs out ends exhausted (error 91, or 138 in the statement's
\    elaboration), never with the goal
\    left open (error 89) as though rfl inside try had failed (Lean's try
\    never catches a runtime exception; review s2-tactics M2).
\ Every T{ }T checks the data stack's depth.
include ../support/tester.fs
include ../support/heap-watch.fs
require ../../src/load/checker.fs
require ../../src/load/front.fs
require ../../src/cli/check-lf.fs
decimal

T{ s" tests/front/s2-slice.ndjson" true lfc-library-open -> outcome-ok }T
T{ s" tests/front/s2-slice.elab.ndjson" lfc-elab-file! lfc-elab-read -> outcome-ok }T
: file ( -- c-addr u ) s" tests/front/01-zero-add-rw.lf" ;
: run ( -- outcome ) file ['] lfc-run lfc-making ;
T{ run -> outcome-ok }T

\ ---- 1. The heap refusing each allocation in turn, every k until a run
\ makes fewer allocations than k (the refusal never fires; review
\ s2-tactics re-check H1: the sweep went on past induction, rw, rfl and
\ try, not only until the first run that ends ok). A fired refusal ends
\ full, or is absorbed (the run still elaborates the same theorem, which
\ the kernel then checks): never another outcome. The absorbed ones are
\ pinned by count, so a step that starts to swallow a refusal (tryClear's
\ full read as "cannot clear", review re-check M4) changes the count.
variable absorbed   variable bad
: refused-at ( k -- outcome fired? )
  heap-refusals ! run heap-refusals @ 0= 0 heap-refusals ! ;
: tally ( outcome -- )
  dup outcome-full = if drop exit then ok? if 1 absorbed +! else 1 bad +! then ;
: each-refused ( -- k ) 0 begin 1+ dup refused-at while tally repeat drop ;
T{ 0 absorbed ! 0 bad ! each-refused 1000 > bad @ -> true 0 }T
T{ absorbed @ -> 2 }T
T{ run -> outcome-ok }T

\ ---- 2. The elaboration fuel at each limit.
variable worst-code
: fuel-at ( n -- outcome code )
  lf-elab-fuel! run lf-author-code lf-meta-default-budget lf-elab-fuel! ;
: fuel-code? ( code -- flag ) dup lfa-e-tac-fuel = swap lfa-e-elab-fuel = or ;
: fuel-fit? ( outcome code -- flag )
  fuel-code? over outcome-exhausted = and swap ok? or ;
: each-fuel ( -- n )
  0 begin 1+ dup fuel-at 2dup fuel-fit? 0= if dup worst-code ! then drop ok? until ;
T{ 0 worst-code ! each-fuel 1 > worst-code @ -> true 0 }T
T{ run -> outcome-ok }T
bye

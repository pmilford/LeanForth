\ Checker contexts with every module src/main.fs loads (review M2 of the
\ context conversion): the dictionary that the library, the job pool and
\ all of src/main.fs lay down while loading is unchanged after real work
\ in contexts (tests/support/dictionary-check.fs: a trial of checker work
\ and a run of the checked environment), here with also a batch of the
\ loader (src/import/load.fs), the program reader (a file, and fed lines
\ whose IR the interpreter then loads and runs) and the term printer run
\ over the trial's terms, levels and names in all three modes; a new
\ context starts as the main context did right after src/main.fs loaded;
\ and the state words of the loader, the printer, the program reader, the
\ interpreter, the staging of exports and the command line lie inside the
\ context, at the same offset in every context. tests/core/contexts.fs does the rest with the core and kernel
\ modules alone. Nothing here checks or accepts a theorem.
include ../support/tester.fs
include ../support/checks.fs
here constant dict-start
require ../../src/lib/task.fs
require ../../src/main.fs
variable planted  0 planted !   \ a shared cell for a planted fault (below)
here constant dict-end
\ The main context right after loading, before any test changes it: its
\ bytes with the heap addresses of its heap-owning members blanked, and
\ the digest of what those members hold (tests/support/context-canon.fs).
include ../support/context-canon.fs
context-bytes constant loaded-bytes
create loaded loaded-bytes allot
context-main loaded loaded-bytes move  loaded canon-zero
canon-digest constant loaded-digest
include ../support/plain-terms.fs
include ../support/plain-cases.fs
include ../support/checker-trial.fs
include ../support/env-cases.fs
include ../support/dictionary-check.fs

\ Members outside the core and kernel modules.
create state-words
  ' lf-load-batch , ' lf-pjob , ' lf-pres , ' lf-pp-scan-walk , ' lf-pp-level-walk ,
  ' lf-ir-reader , ' irx-state , ' cin-state , ' cli-state ,
here state-words - 1 cells / constant state-count
: state-word ( i -- addr ) cells state-words + @ execute ;
: state-offset ( addr -- n ) lf-context @ - ;
: inside? ( addr -- flag ) state-offset 0 context-bytes within ;
: all-inside? ( -- flag ) true state-count 0 ?do i state-word inside? and loop ;
: offsets ( -- x ) 0 state-count 0 ?do 31 * i state-word state-offset + loop ;
T{ all-inside? -> true }T
context-new throw constant other
other context-use
T{ all-inside? offsets -> true context-main context-use offsets }T
\ A new context starts as the main context did after loading (after the
\ header, whose size grew; the members the tests declared start zeroed).
: past-header ( addr -- addr' u ) /context-header + loaded-bytes /context-header - ;
create other-bytes loaded-bytes allot
other other-bytes loaded-bytes move  other-bytes canon-zero
: other-digest ( -- h ) other context-use canon-digest context-main context-use ;
T{ other-bytes past-header loaded past-header compare other-digest -> 0 loaded-digest }T
T{ other loaded-bytes + context-bytes loaded-bytes - 1 cells / cells-zero? -> true }T
T{ other context-free -> 0 }T

\ The loader stages a batch and rolls it back; the printer prints every
\ term (also as a statement), level and name of the trial's context to a
\ sink that drops the text, in each mode, counting the prints that ended
\ ok (most of the random terms are not closed).
variable prints-ok  0 prints-ok !
: staged ( -- )
  lf-load-begin drop 0 lf-tag-sort 0 0 lf-load-node drop
  1 lf-tag-bvar 0 0 lf-load-node drop lf-load-abort ;
: sink ( c-addr u -- ) 2drop ;
: tally ( outcome -- ) ok? if 1 prints-ok +! then ;
: print-terms ( -- )
  lf-term-count @ 0 ?do i 500 lf-print-term tally i 500 lf-print-statement tally loop ;
: print-rest ( -- )
  lf-level-count @ 0 ?do i 500 lf-print-level tally loop
  lf-name-count @ 0 ?do i lf-print-name tally loop ;
: print-all ( mode -- ) ['] sink swap lf-print-setup print-terms print-rest ;
\ The program reader reads a source file, then fed lines whose IR the
\ interpreter loads and runs, then a line it refuses; counting the steps
\ that ended ok.
variable reads-ok  0 reads-ok !
: read-tally ( outcome -- ) ok? if 1 reads-ok +! then ;
: read-file ( -- ) ['] sink s" src/program/examples.fs" lf-ir-read-file read-tally ;
: read-fed ( -- )
  irx-load-start ['] irx-load-line s" fed.fs" lf-ir-start
  s" : sq ( n -- n*n ) dup * ;" lf-ir-feed s" 5 constant five : f five sq ;" lf-ir-feed
  lf-ir-finish read-tally irx-load-finish read-tally 1000 s" f" irx-run read-tally
  ['] sink s" bad.fs" lf-ir-start s" : g ( -- ) here ;" lf-ir-feed lf-ir-finish drop ;
: printed ( -- )
  dict-trial @ context-use staged read-file read-fed
  lf-print-unicode print-all lf-print-ascii print-all lf-print-latex print-all
  context-main context-use ;
dict-prepare dict-snap
T{ dict-work -> outcome-ok }T
printed
T{ dict-changes dict-first -> 0 0 }T
T{ prints-ok @ 0> reads-ok @ -> true 4 }T
." dictionary unchanged with src/main.fs: " dict-bytes . ." bytes, after "
prints-ok @ . ." prints that ended ok among others; a context is " loaded-bytes .
." bytes after src/main.fs loads" cr
dict-finish

\ A parallel check (check --jobs 3; kernel/env-schedule.fs, plan task
\ 7.3.1) of the nested-blocks export leaves the dictionary unchanged too,
\ but for the records that only the driving task writes, outside jobs:
\ the run's (cli/check-run.fs: ck-state, ck-stage and the two feed
\ records), the scheduler's (lf-sched), the environment registry and the
\ job pool's (task-pool, task-queue, the worker threads' ids). A planted
\ fault, a check that writes a shared cell inside its job, is caught.
\ The copy is in the heap: the dictionary may have less room left than it
\ holds (under make coverage's counters it overflowed).
dict-bytes allocate throw constant par-copy
: in-record? ( addr record size -- flag ) over + within ;
: par-run-records? ( addr -- flag )
  dup ck-state /ck in-record? over ck-stage /stage in-record? or
  over ck-feeding-record /feed in-record? or swap ck-worker-feed /feed in-record? or ;
\ On Gforth 1.0 also the worker threads' ids and the pool's mutex and its
\ two conditions, laid down from task-lock up to pool-lock.
[defined] worker-ids [if]
: par-sync? ( addr -- flag ) ['] task-lock >body ['] pool-lock within ;
: par-ids? ( addr -- flag )
  dup worker-ids task-cores pthreads in-record? swap par-sync? or ;
[else]
: par-ids? ( addr -- flag ) drop false ;
[then]
: par-pool? ( addr -- flag )
  dup task-pool /pool in-record? over task-queue task-queue-jobs cells in-record? or
  swap par-ids? or ;
: par-allowed? ( addr -- flag )
  dup par-run-records? over lf-sched /lf-sched in-record? or
  over lf-envs /lf-envs in-record? or swap par-pool? or ;
: par-changed? ( i -- flag )
  dup dict-start + dup par-allowed? if 2drop false exit then c@ swap par-copy + c@ <> ;
: par-changes ( -- n ) 0 dict-bytes 0 ?do i par-changed? - loop ;
variable planting  false planting !
: planted-check ( -- ) planting @ if 1 planted +! then lf-check-declaration ;
: par-check ( -- )
  20000000 ck-start 3 ck-jobs! ['] planted-check ck-check-word!
  s" tests/cli/nested.ndjson" false ck-load drop ck-check ck-release ;
: par-run ( -- )
  context-new throw dup context-use par-check context-main context-use context-free throw
  task-cores pool-workers! ;
dict-start par-copy dict-bytes move
par-run
T{ par-changes -> 0 }T
true planting ! par-run false planting !
T{ par-changes 0> planted @ 0> -> true true }T
T{ lf-context @ context-main = -> true }T
T{ depth -> 0 }T
bye

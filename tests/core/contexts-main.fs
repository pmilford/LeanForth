\ Checker contexts with every module src/main.fs loads (review M2 of the
\ context conversion): the dictionary that the library, the job pool and
\ all of src/main.fs lay down while loading is unchanged after real work
\ in contexts (tests/support/dictionary-check.fs: a trial of checker work
\ and a run of the checked environment), here with also a batch of the
\ loader (src/import/load.fs) and the term printer run over the trial's
\ terms, levels and names in all three modes; a new context starts as the
\ main context did right after src/main.fs loaded; and the state words of
\ the loader and the printer lie inside the context, at the same offset
\ in every context. tests/core/contexts.fs does the rest with the core and
\ kernel modules alone. Nothing here checks or accepts a theorem.
include ../support/tester.fs
include ../support/checks.fs
here constant dict-start
require ../../src/lib/task.fs
require ../../src/main.fs
here constant dict-end
\ The main context right after loading, before any test changes it.
context-bytes constant loaded-bytes
create loaded loaded-bytes allot
context-main loaded loaded-bytes move
include ../support/plain-terms.fs
include ../support/plain-cases.fs
include ../support/checker-trial.fs
include ../support/env-cases.fs
include ../support/dictionary-check.fs

\ Members outside the core and kernel modules.
create state-words
  ' lf-load-batch , ' lf-pjob , ' lf-pres , ' lf-pp-scan-walk , ' lf-pp-level-walk ,
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
T{ other past-header loaded past-header compare -> 0 }T
T{ other loaded-bytes + context-bytes loaded-bytes - 1 cells / cells-zero? -> true }T
T{ other context-free -> 0 }T

\ The loader stages a batch and rolls it back; the printer prints every
\ term (also as a statement), level and name of the trial's context to a
\ sink that drops the text, in each mode, counting the prints that ended
\ ok (most of the random terms are not closed).
variable prints-ok  0 prints-ok !
: staged ( -- )
  lf-load-begin drop 0 lf-tag-sort 0 0 lf-load-node drop 1 lf-tag-bvar 0 0 lf-load-node drop
  lf-load-abort ;
: sink ( c-addr u -- ) 2drop ;
: tally ( outcome -- ) ok? if 1 prints-ok +! then ;
: print-terms ( -- )
  lf-term-count @ 0 ?do i 500 lf-print-term tally i 500 lf-print-statement tally loop ;
: print-rest ( -- )
  lf-level-count @ 0 ?do i 500 lf-print-level tally loop
  lf-name-count @ 0 ?do i lf-print-name tally loop ;
: print-all ( mode -- ) ['] sink swap lf-print-setup print-terms print-rest ;
: printed ( -- )
  dict-trial @ context-use staged
  lf-print-unicode print-all lf-print-ascii print-all lf-print-latex print-all
  context-main context-use ;
dict-prepare dict-snap
T{ dict-work -> outcome-ok }T
printed
T{ dict-changes dict-first -> 0 0 }T
T{ prints-ok @ 0> -> true }T
." dictionary unchanged with src/main.fs: " dict-bytes . ." bytes, after "
prints-ok @ . ." prints that ended ok among others; a context is " loaded-bytes .
." bytes after src/main.fs loads" cr
dict-finish
T{ lf-context @ context-main = -> true }T
T{ depth -> 0 }T
bye

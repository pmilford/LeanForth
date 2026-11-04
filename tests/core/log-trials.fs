\ Randomized differential of the derivation log (src/core/derivation-log.fs;
\ ADR 0013, test plan item 1): the checker trials of
\ tests/support/checker-trial.fs (random terms through inference,
\ conversion, comparison, beta, shift, instantiation, the level passes,
\ universe substitution, the signature index and the definition probe, and
\ the pinned fixtures; every outcome, result, fuel left, store count and
\ serial, and diagnostic folded into a digest) run for each seed with the
\ log off; with it on at level terms and at level steps; with it on at
\ three sets of limits drawn from the seed, so that it is truncated (and
\ restarts, as the test preset does) all through the trial; and
\ interleaved step by step, one context logging and one not. Every digest
\ must equal the seed's digest with the log off, and every log left at a
\ trial's end must pass the structural check (tests/support/log-check.fs).
\ Prints the seeds, steps, the outcome mix of the checker calls, and the
\ records written and the logs truncated. Test-only.
\ This test sets the log's options itself: under the test preset
\ (tests/support/gforth-log.sh) it has nothing to add and is skipped.
[defined] lf-log-preset-level [if] .( log-trials: skipped under the log preset) cr bye [then]
include ../support/tester.fs
include ../support/checks.fs
require ../../src/lib/task.fs
require ../../src/kernel/mixed-definition-probe.fs
require ../../src/kernel/env-publish.fs
include ../support/plain-terms.fs
include ../support/plain-cases.fs
include ../support/checker-trial.fs
require ../support/log-check.fs

[defined] log-trial-jobs [if] log-trial-jobs [else] 8 [then] constant jobs
[defined] log-trial-steps [if] log-trial-steps [else] 1000 [then] constant steps
create off-digests jobs cells allot
: off-digest ( k -- addr ) cells off-digests + ;

\ The outcome mix of every checker call of every run.
create outcome-mix 7 cells allot  outcome-mix 7 cells erase
: count-outcome ( outcome -- outcome ) dup outcome-sane cells outcome-mix + 1 swap +! ;
: outcome-mix. ( -- ) 7 0 do i cells outcome-mix + @ . loop ;
' count-outcome is checked
variable written
variable restarts
variable invalid-logs

: fresh ( -- context ) context-new throw dup context-use ;
: home ( -- ) context-main context-use ;
: retire ( context -- )
  lf-log-written written +! lf-log-restarts restarts +!
  lf-log-level if lc-valid? 0= if 1 invalid-logs +! then then
  home context-free throw ;

\ Modes: 0 off; 1 terms, ample; 2 steps, ample; 3-5 terms at limits drawn
\ from the seed and the mode.
: ample ( -- ) lf-log-capacities lf-log-limits ;
: draw ( k mode n -- u ) >r 7919 * swap 104729 * + 2147483647 and 16 rshift r> mod ;
: drawn ( k mode -- )
  2dup 60 draw >r 2dup 1+ 12 draw 1+ >r 2dup 2 + 30 draw >r 3 + 8 draw r> r> r>
  swap 2swap swap lf-log-limits ;
: log-options ( k mode -- )
  case 0 of drop 0 lf-log-set ample endof
    1 of drop lf-log-terms lf-log-set ample endof
    2 of drop lf-log-steps lf-log-set ample endof
    >r lf-log-terms lf-log-set r@ drawn r> endcase ;
: logging ( k mode -- ) log-options lf-log-options lf-logopt-level @ if lf-log-auto then ;
\ Trial k in a new context in mode: its digest.
: trial-in ( k mode -- digest )
  fresh >r 2dup logging drop steps 0 trial-start trial-run digest r> retire ;

\ Interleaved: trial k in a logging context (mode) and a silent one, one
\ step each in turn; both digests.
variable loud
variable quiet
: both-steps ( -- more? )
  loud @ context-use step? quiet @ context-use step? or home ;
: interleave ( k mode -- loud-digest quiet-digest )
  fresh loud ! 2dup logging drop dup steps 0 trial-start home
  fresh quiet ! steps 0 trial-start home
  begin both-steps 0= until
  loud @ context-use trial-finish digest quiet @ context-use trial-finish digest
  loud @ context-use loud @ retire quiet @ context-use quiet @ retire ;

: baseline ( -- ) jobs 0 ?do i 0 trial-in i off-digest ! loop ;
baseline
\ Different seeds give different digests, so a mix-up would show.
: distinct? ( -- flag ) true jobs 1 ?do i off-digest @ i 1- off-digest @ <> and loop ;
T{ distinct? -> true }T

: same? ( k mode -- flag ) over swap trial-in swap off-digest @ = ;
: all-same? ( mode -- flag ) true jobs 0 ?do i 2 pick same? and loop nip ;
T{ 1 all-same? -> true }T
T{ 2 all-same? -> true }T
T{ 3 all-same? -> true }T
T{ 4 all-same? -> true }T
T{ 5 all-same? -> true }T
: interleaved? ( k mode -- flag )
  over >r interleave r> off-digest @ tuck = >r = r> and ;
: all-interleaved? ( -- flag ) true jobs 0 ?do i 1 interleaved? i 4 interleaved? and and loop ;
T{ all-interleaved? -> true }T
T{ invalid-logs @ -> 0 }T
T{ restarts @ 0> written @ 0> -> true true }T

0 lf-log-set ample
." log-trials: " jobs . ." seeds of " steps . ." steps, 5 log modes and 2 interleavings each;"
cr ." checker calls ok/invalid/exhausted/unknown/rejected/unsupported/full: "
outcome-mix. cr
." records written: " written @ . ." logs truncated and restarted: " restarts @ . cr
cases-done
bye

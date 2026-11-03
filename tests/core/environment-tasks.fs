\ Row 9 of ADR 0012's test matrix: checks of one environment run as jobs
\ in two contexts at once (src/lib/task.fs: threads on Gforth 1.0,
\ cooperative tasks on 0.7.3, which switch at every step of the synthetic
\ check; the serial host in environment-tasks-serial.fs) give exactly the
\ serial verdicts and environment, as tests/core/contexts.fs does for
\ checker work. The environment is shared, outside every context; the
\ input is per context in v0 (src/core/input.fs), so each lane's context
\ builds the same world and loads the same input, and its fingerprint must
\ match the one the environment was made over. A small scheduler starts a
\ declaration only when lf-env-ready? holds for its own name and every
\ name it uses (G-P5), waits for both jobs, and publishes them in the
\ order opposite to their submission; it picks the lowest ready
\ declarations in one run and the highest in another, so the order of
\ publication differs from the input's. A context without the input, or
\ with another one, sees no environment; a check started before a slot it
\ needs is final ends invalid, never accepted.
include ../support/tester.fs
include ../support/checks.fs
require ../../src/lib/task.fs
require ../support/env-cases.fs

: cooperative? ( -- flag ) task-host task-cooperative = ;

\ Each step of a check counts a shared tick and records, in its context,
\ the first and last tick it saw, then yields. Two checks interleaved
\ when their tick ranges overlap (exact on the cooperative host, where
\ only one task runs at a time; on threads the shared tick is only a hint).
variable ticks  0 ticks !
begin-structure /trace
  field: trace-first
  field: trace-last
end-structure
/trace context-record: trace
: tick ( -- n ) 1 ticks +! ticks @ ;
: traced ( -- )
  tick trace trace-first @ 0= if dup trace trace-first ! then trace trace-last ! task-yield ;
' traced is syn-pause

\ The serial reference, in the main context.
main-input
lf-input-fingerprint constant main-print
8 fresh-env
T{ ' syn-check lf-env-run -> outcome-ok }T
env-content constant serial-content
T{ main-count verdicts-match? -> true }T
env-free

\ Two lanes, each a context holding the same world and input, with its
\ job and the job's result.
2 constant lanes
create lane-contexts lanes cells allot
create lane-jobs lanes cells allot
create lane-iors lanes cells allot
create pending decls cells allot
variable faults
variable published
variable overlaps
: lane ( k table -- addr ) swap cells + ;
: in-lane ( k -- ) lane-contexts lane @ context-use ;
: home ( -- ) context-main context-use ;
: fault ( -- ) 1 faults +! ;
: lane-input ( -- ) world-again main-input ;
: make-lane ( k -- )
  context-new throw dup rot lane-contexts lane ! context-use lane-input home ;
: make-lanes ( -- ) lanes 0 ?do i make-lane loop ;
: free-lanes ( -- ) lanes 0 ?do i lane-contexts lane @ context-free throw loop ;
make-lanes
: lane-print ( k -- h ) in-lane lf-input-fingerprint home ;
T{ 0 lane-print 1 lane-print -> main-print main-print }T

\ A context without the input, or with another input, sees no environment.
8 fresh-env
context-new throw constant bare
bare context-use
T{ 0 lf-env-begin lf-env-view 0 lf-env-outcome 0 lf-env-handle -> outcome-invalid outcome-invalid outcome-invalid 0 -1 outcome-invalid }T
T{ lf-diag-code@ -> lf-diag-no-snapshot }T
world-again lf-input-reset n.A def add ends
T{ 0 lf-env-begin lf-env-view -> outcome-invalid outcome-invalid }T
home
T{ bare context-free -> 0 }T
\ ... while a lane holding the same input sees it.
0 in-lane
T{ 0 lf-env-begin -> outcome-ok }T
home
env-free

\ Readiness (G-P5): the declaration's own name and every name it uses.
: used ( i k -- name ) cells swap plan plan-uses + @ ;
: used-ready? ( i k -- flag ) over swap used swap lf-env-ready? ;
: ready? ( i -- flag )
  dup lf-input-name over lf-env-ready?
  over plan plan-count @ 0 ?do over i used-ready? and loop nip ;
: pending? ( i -- flag ) cells pending + @ ;
: unpend ( i -- ) false swap cells pending + ! ;
: mark-pending ( -- ) main-count 0 ?do true i cells pending + ! loop ;
: ready-pending? ( i -- flag ) dup pending? if ready? else drop false then ;
variable high?
: choose-low ( -- i | -1 ) main-count 0 ?do i ready-pending? if i unloop exit then loop -1 ;
: choose-high ( -- i | -1 )
  0 main-count 1- ?do i ready-pending? if i unloop exit then -1 +loop -1 ;
: choose ( -- i | -1 ) high? @ if choose-high else choose-low then ;

\ Submitting declaration i in lane k: begin its check and clear its trace
\ in the lane's context, then hand the context to a job.
: begin-in ( i k -- )
  in-lane trace /trace erase lf-env-begin ok? 0= if fault then home ;
: submit ( i k -- )
  over unpend tuck begin-in
  dup lane-contexts lane @ ['] syn-check job-submit throw swap lane-jobs lane ! ;
\ Waiting for n lanes, then publishing them, the last lane first, each in
\ its own context, whose scratch is then rolled back; a job that did not
\ return cleanly makes its declaration invalid (G-P6).
: await-all ( n -- ) 0 ?do i lane-jobs lane @ job-wait i lane-iors lane ! loop ;
: rollback ( -- ) lf-input-rollback ok? 0= if fault then ;
: publish-lane ( k -- )
  dup lane-iors lane @ swap in-lane if outcome-invalid lf-env-finish then
  lf-env-hand-over nip if fault then rollback 1 published +! home ;
: publish-all ( n -- ) begin dup while 1- dup publish-lane repeat drop ;
: trace@ ( k -- first last ) in-lane trace trace-first @ trace trace-last @ home ;
: overlap? ( -- flag ) 0 trace@ 1 trace@ rot < >r < r> and ;
: count-overlap ( n -- ) 2 = if overlap? if 1 overlaps +! then then ;

\ One round fills up to two lanes; the schedule ends when a round finds
\ nothing ready (then every declaration has been published).
: fill-lanes ( -- n )
  lanes 0 ?do choose dup 0< if drop i unloop exit then i submit loop lanes ;
: round ( -- n ) fill-lanes dup await-all dup count-overlap dup publish-all ;
: schedule ( -- ) mark-pending begin round 0= until ;
: parallel-run ( high? -- )
  high? ! 0 faults ! 0 published ! 0 overlaps ! 8 fresh-env schedule ;

false parallel-run
T{ faults @ published @ main-count verdicts-match? -> 0 main-count true }T
T{ env-content serial-content = -> true }T
T{ cooperative? overlaps @ 0> and cooperative? 0= or -> true }T
env-free
true parallel-run
T{ faults @ published @ main-count verdicts-match? -> 0 main-count true }T
T{ env-content serial-content = -> true }T
T{ cooperative? overlaps @ 0> and cooperative? 0= or -> true }T
env-free

\ A check started before a slot it needs is final ends invalid: 1 uses 0,
\ which is published only after both jobs have ended.
: early ( -- ) 0 0 submit 1 1 submit 2 await-all 2 publish-all ;
8 fresh-env
0 faults !
T{ early faults @ 0 lf-env-outcome 1 lf-env-outcome -> 0 outcome-ok outcome-invalid }T
T{ 1 lf-env-handle nip nip -> outcome-invalid }T
1 in-lane
T{ lf-diag@ nip -> 0 1 lf-diag-too-early }T
home
env-free
free-lanes
T{ depth -> 0 }T
bye

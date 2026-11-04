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
\ with another one, even one that differs only in the text of its names,
\ sees no environment; a check started before a slot it needs is final
\ ends invalid, never accepted. The scheduler publishes each job through
\ lf-env-hand-over-job, which records a THROW and refuses a job whose
\ snapshot moved to another declaration. A check that throws in its job is
\ invalid and its lane's context is replaced (G-P6), giving the verdicts
\ of the serial run with the same THROW. Inside a job nothing publishes,
\ makes, chooses or frees an environment, no internal word writes one, no
\ context is claimed or released and readiness says false (G-P1).
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

\ The serial reference, in the main context; and, with a check that
\ throws for declaration 1, in a context the run's maker gives.
main-input
lf-input-fingerprint constant main-print
8 fresh-env
T{ ' syn-check ' main-maker lf-env-run -> outcome-ok }T
env-content constant serial-content
T{ main-count verdicts-match? -> true }T
env-free
variable throw-in  -1 throw-in !
: lane-check ( -- ) me throw-in @ = if -79 throw then syn-check ;
main-maker throw constant spare
spare context-use
1 throw-in ! 8 fresh-env
T{ ' lane-check ' main-maker lf-env-run lf-env-spent? -> outcome-ok true }T
env-content constant thrown-content
-1 throw-in !
env-free context-main context-use
T{ spare context-free -> 0 }T

\ Two lanes, each a context holding the same world and input, with its
\ job and the job's result.
2 constant lanes
create lane-contexts lanes cells allot
create lane-jobs lanes cells allot
create lane-iors lanes cells allot
create lane-decls lanes cells allot
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
\ Nor does a context whose input differs only in the text of its names:
\ the same structure, lengths and IDs, other letters. The environment
\ holds the main input's verdicts; nothing named a was checked there.
: lower ( -- c-addr u ) s" abcdefghijklmnpqrstxyzUVW" ;
: lower-world ( -- )
  lower nip 0 ?do lower drop i + 1 intern i name-at ! loop
  s" Nzt" intern dup 25 name-at ! s" adx" sub 26 name-at !
  0 sort-term t-type <> 1 sort-term t-value <> or abort" lower: terms" ;
8 fresh-env
T{ ' syn-check ' main-maker lf-env-run -> outcome-ok }T
name-ids ids-before most-names cells move
context-new throw constant other
other context-use lower-world main-input
T{ lf-input-fingerprint main-print = lf-env-view 0 lf-env-outcome -> false outcome-invalid outcome-invalid }T
T{ 0 s" a" lf-name-str drop lf-env-lookup 0 lf-env-handle -> -1 outcome-invalid 0 -1 outcome-invalid }T
home ids-before name-ids most-names cells move
T{ other context-free -> 0 }T
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
\ in the lane's context, then hand the context to a job running xt.
: begin-in ( i k -- )
  2dup lane-decls lane !
  in-lane trace /trace erase lf-env-begin ok? 0= if fault then home ;
: submit-with ( i k xt -- )
  >r over unpend tuck begin-in
  dup lane-contexts lane @ r> job-submit throw swap lane-jobs lane ! ;
: submit ( i k -- ) ['] lane-check submit-with ;
\ Waiting for n lanes, then publishing them, the last lane first, each in
\ its own context, whose scratch is then rolled back. A job that did not
\ return cleanly makes its declaration invalid and spends its context,
\ which is then freed and replaced (G-P6).
variable renewals
: await-all ( n -- ) 0 ?do i lane-jobs lane @ job-wait i lane-iors lane ! loop ;
: rollback ( -- ) lf-input-rollback ok? 0= if fault then ;
: renew-lane ( k -- ) dup lane-contexts lane @ context-free throw make-lane 1 renewals +! ;
: hand-lane ( ior i -- spent? )
  lf-env-hand-over-job nip if fault then rollback lf-env-spent? ;
: lane-result ( k -- ior i ) dup lane-iors lane @ swap lane-decls lane @ ;
: publish-lane ( k -- )
  dup dup lane-result rot in-lane hand-lane home 1 published +!
  if renew-lane else drop then ;
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
  high? ! 0 faults ! 0 published ! 0 overlaps ! 0 renewals ! 8 fresh-env schedule ;

false parallel-run
T{ faults @ published @ main-count verdicts-match? -> 0 main-count true }T
T{ env-content serial-content = renewals @ -> true 0 }T
T{ cooperative? overlaps @ 0> and cooperative? 0= or -> true }T
env-free
true parallel-run
T{ faults @ published @ main-count verdicts-match? -> 0 main-count true }T
T{ env-content serial-content = renewals @ -> true 0 }T
T{ cooperative? overlaps @ 0> and cooperative? 0= or -> true }T
env-free
\ The check of declaration 1 throws in its job: it is invalid, its lane's
\ context is replaced once, and the environment is the serial run's with
\ the same THROW.
1 throw-in !
false parallel-run
T{ faults @ published @ renewals @ env-content thrown-content = -> 0 main-count 1 true }T
lf-env-view drop
T{ 1 lf-env-outcome 8 lf-env-outcome 26 lf-env-outcome -> outcome-invalid outcome-unknown outcome-ok }T
env-free
true parallel-run
T{ faults @ published @ renewals @ env-content thrown-content = -> 0 main-count 1 true }T
env-free
-1 throw-in !

\ Inside a job nothing publishes, makes, chooses or frees an environment
\ (G-P1): a job that checks declaration 1 and then tries all four is
\ refused each time, and slot 1 stays open until the scheduler publishes.
\ Internal words that write the environment, the undo words among them,
\ throw lf-env-refused before writing, and readiness says false.
create tries 20 cells allot
: try! ( x k -- ) cells tries + ! ;
: job-internals ( -- )
  1 slot@ -77 ['] lf-env-unpublish catch nip nip 6 try!
  1 slot@ ['] lf-env-guarded catch nip 7 try!  n.A 1 lf-env-ready? 8 try! ;
\ The undo words: on the open slot 1, the final slot 0 and the pool's mark.
: marked-ior ( -- ior ) ['] lf-env-marked? catch dup 0= if nip then ;
: job-undoes ( -- )
  1 slot@ ['] lf-env-undo catch nip 9 try!  0 slot@ ['] lf-env-undo catch nip 10 try!
  lf-diag-clear outcome-ok 1 slot@ ['] lf-env-unfinished catch nip nip 11 try!
  lf-diag-code@ 12 try!  outcome-ok 0 slot@ ['] lf-env-ended catch nip nip 13 try!
  marked-ior 14 try! ;
\ Contexts (the round-4 review's M1): claiming lane 1's idle context
\ gives false, and releasing the job's own context aborts.
: job-contexts ( -- )
  lf-owner @ 1 lane-contexts lane @ context-claim 15 try!
  lf-context @ ['] context-release catch dup if nip then 16 try! ;
\ The scheduler's own entry, with the ior of a job that threw (the fifth
\ review's probe p7): refused before it records the THROW, so the job's
\ candidate stays as the check left it and its context is not spent.
: job-entry ( -- )
  -5 1 lf-env-hand-over-job 18 try! 17 try! lf-env-spent? 19 try! ;
: job-tries ( -- )
  syn-check lf-env-hand-over 1 try! 0 try! 8 lf-env-new 3 try! 2 try!
  lf-env lf-env-use 4 try! lf-env lf-env-free 5 try! job-internals job-undoes
  job-contexts job-entry ;
: try@ ( k -- x ) cells tries + @ ;
: refused-try? ( k -- flag ) try@ lf-env-refused = ;
8 fresh-env
0 0 submit 1 await-all 1 publish-all
1 0 begin-in
T{ 0 lane-contexts lane @ ' job-tries job-submit throw job-wait -> 0 }T
T{ 0 try@ 1 try@ 2 try@ 3 try@ -> outcome-invalid true 0 outcome-invalid }T
T{ 4 try@ 5 try@ 1 slot@ lf-slot-final? -> outcome-invalid outcome-invalid false }T
T{ 6 try@ lf-env-refused = 7 try@ lf-env-refused = 8 try@ -> true true false }T
T{ 9 refused-try? 10 refused-try? 11 refused-try? 12 try@ -> true true true lf-diag-none }T
T{ 13 refused-try? 14 refused-try? 0 slot@ lf-slot-accepted? -> true true true }T
T{ 15 try@ 16 try@ 1 lane-contexts lane @ context-idle? -> false -2 true }T
T{ 17 try@ 18 try@ 19 try@ -> outcome-invalid true false }T
0 in-lane
T{ lf-env-hand-over rollback -> outcome-ok false }T
home
T{ 1 slot@ lf-slot-final? lf-env-view 1 lf-env-outcome n.A 1 lf-env-ready? -> true outcome-ok outcome-ok true }T
env-free
\ The scheduler's entry makes sure the job's snapshot is still of its
\ declaration (L5): a job submitted for 2 that checks 1 instead publishes
\ nothing, and the hand-over is a fault.
: hijack ( -- ) 1 lf-env-begin drop syn-check ;
8 fresh-env
0 0 submit 1 await-all 1 publish-all
0 faults !
2 0 ' hijack submit-with 1 await-all 1 publish-all
T{ faults @ 1 slot@ lf-slot-final? 2 slot@ lf-slot-final? -> 1 false false }T
0 in-lane
T{ lf-diag@ nip -> 2 lf-recheck-moved lf-diag-recheck }T
home
env-free

\ A check started before a slot it needs is final ends invalid: 1 uses 0,
\ which is published only after both jobs have ended.
: early ( -- ) 0 0 submit 1 1 submit 2 await-all 2 publish-all ;
8 fresh-env
0 faults !
T{ early faults @ lf-env-view 0 lf-env-outcome 1 lf-env-outcome -> 0 outcome-ok outcome-ok outcome-invalid }T
T{ 1 lf-env-handle nip nip -> outcome-invalid }T
1 in-lane
T{ lf-diag@ nip -> 0 1 lf-diag-too-early }T
home
env-free
free-lanes
T{ depth -> 0 }T
bye

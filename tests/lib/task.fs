\ Tests of the task adapter (src/lib/task.fs) with checker contexts: jobs
\ run in tasks, each with its own context, and contexts interleaved in one
\ task, must give exactly the results of the same jobs run one after
\ another. Each job builds and walks random DAGs and ends with a recursive
\ pass about dag-depth frames deep, inside its task (tests/lib/task-job.fs).
\ On Gforth 1.0 the tasks are threads; on 0.7.3 they are cooperative and
\ yield every few visits; task-serial.fs runs this file on the serial host.
include ../support/tester.fs
include ../support/checks.fs
require ../../src/lib/task.fs
include ./task-job.fs

4 constant jobs
3 constant job-rounds
16 constant job-every
create serial-sums jobs cells allot
create serial-visits jobs cells allot
create job-contexts jobs cells allot
create job-tasks jobs cells allot
: slot ( k table -- addr ) swap cells + ;

\ Job k, yielding every so many visits (0: never), in the current context.
: dag-job ( k every -- ) >r 7919 * 17 + job-rounds r> dag-start ;
: fresh ( -- context ) context-new throw dup context-use ;

\ The serial reference: each job alone, to the end, in a fresh context.
: record-serial ( k sum visits -- ) rot tuck serial-visits slot ! serial-sums slot ! ;
: serial@ ( k -- sum visits ) dup serial-sums slot @ swap serial-visits slot @ ;
: serial-job ( k -- )
  fresh swap dup 0 dag-job dag-run dag-results record-serial context-free throw ;
: serial-all ( -- ) jobs 0 ?do i serial-job loop ;
serial-all
T{ lf-context @ context-main = -> true }T
T{ depth -> 0 }T

\ Checking job k's results in its own context against the serial ones.
: wrong? ( k -- flag ) dup job-contexts slot @ context-use serial@ dag-results d= 0= ;
: wrong-count ( -- n ) 0 jobs 0 ?do i wrong? - loop context-main context-use ;
\ The recursive pass used over 900 cells of each stack inside the task.
: deep? ( k -- flag )
  job-contexts slot @ context-use
  dag-state dag-deep @ 900 > dag-state dag-data @ 900 > and ;
: deep-count ( -- n ) 0 jobs 0 ?do i deep? - loop context-main context-use ;

\ Tasks: a context per job, then every task started, then all waited for.
: prepare ( k -- context )
  fresh tuck over job-contexts slot ! job-every dag-job context-main context-use ;
: start-job ( k -- ior )
  dup prepare ['] dag-run task-start >r swap job-tasks slot ! r> ;
: start-all ( -- failures ) 0 jobs 0 ?do i start-job 0<> - loop ;
: wait-all ( -- failures ) 0 jobs 0 ?do i job-tasks slot @ task-wait 0<> - loop ;
: free-all ( -- failures ) 0 jobs 0 ?do i job-contexts slot @ context-free 0<> - loop ;

T{ ' start-all rs-checked ' wait-all rs-checked -> 0 0 }T
T{ wrong-count deep-count -> 0 jobs }T
T{ lf-context @ context-main = -> true }T
T{ free-all -> 0 }T
\ A second batch, which reuses freed memory, gives the same results.
T{ start-all wait-all wrong-count free-all -> 0 0 0 0 }T

\ A word that throws ends its own task with that THROW code, while other
\ tasks run on unaffected.
: thrower ( -- ) 37 throw ;
: run-thrower ( -- ior )
  fresh context-main context-use dup ['] thrower task-start throw task-wait
  swap context-free throw ;
T{ ' run-thrower rs-checked -> 37 }T
T{ start-all run-thrower wait-all wrong-count free-all -> 0 37 0 0 0 }T

\ A task given an address that is not a context ends with ABORT's code
\ (-2) and runs nothing.
create not-a-context 4 cells allot  not-a-context 4 cells erase
T{ not-a-context ' dag-run task-start swap task-wait -> 0 -2 }T

\ Two contexts interleaved in one task, switching at every step, give the
\ serial results; so do all four.
: step-in ( context -- more? ) context-use dag-step ;
: both-step ( a b -- a b more? ) over step-in over step-in or ;
: interleave ( a b -- ) begin both-step 0= until 2drop context-main context-use ;
: prepare-pair ( -- a b ) 0 prepare 1 prepare ;
: pair-wrong ( -- n ) 0 wrong? 1 wrong? + negate context-main context-use ;
: free-job ( k -- ) job-contexts slot @ context-free throw ;
: free-pair ( -- ) 0 free-job 1 free-job ;
T{ prepare-pair ' interleave rs-checked pair-wrong -> 0 }T
free-pair
: all-step ( -- more? ) false jobs 0 ?do i job-contexts slot @ step-in or loop ;
: interleave-all ( -- ) begin all-step 0= until context-main context-use ;
: prepare-all ( -- ) jobs 0 ?do i prepare drop loop ;
T{ prepare-all interleave-all wrong-count deep-count free-all -> 0 jobs 0 }T

\ The comparison detects interference: with the random seed planted in one
\ shared variable instead of each context, interleaved jobs no longer give
\ the serial results.
variable shared-seed
: shared-seed-cell ( -- addr ) shared-seed ;
' shared-seed-cell is dag-seed-cell
T{ prepare-pair interleave pair-wrong -> 2 }T
free-pair
' dag-own-seed is dag-seed-cell
T{ prepare-pair interleave pair-wrong -> 0 }T
free-pair

\ Every context was freed and the main context is selected again.
T{ lf-context @ context-main = -> true }T
T{ depth -> 0 }T
." task host " task-host . ." (0 serial, 1 cooperative, 2 threads); recursive pass used "
fresh 0 0 dag-job dag-run dag-state dag-deep @ . ." return and "
dag-state dag-data @ . ." data-stack cells" cr
lf-context @ context-free throw
bye

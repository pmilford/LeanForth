\ Report-only speed-up of the task adapter (not part of make test): for 1,
\ 2, 6 and 12 jobs of tests/lib/task-job.fs, the time to run them one after
\ another in one task and as that many tasks, and the ratio. Each job runs
\ bench-rounds rounds and never yields. Uses Gforth's utime; run with
\ `gforth tests/lib/task-bench.fs`. On a host without threads the ratio is
\ about 1.
require ../../src/lib/task.fs
include ./task-job.fs

400 constant bench-rounds
12 constant bench-max
create bench-contexts bench-max cells allot
create bench-tasks bench-max cells allot
: slot ( k table -- addr ) swap cells + ;
: fresh ( -- context ) context-new throw dup context-use ;
: bench-job ( k -- ) 7919 * 17 + bench-rounds 0 dag-start ;
: prepare ( n -- )
  0 ?do fresh i bench-contexts slot ! i bench-job loop context-main context-use ;
: release ( n -- ) 0 ?do i bench-contexts slot @ context-free throw loop ;
: run-serial ( n -- )
  0 ?do i bench-contexts slot @ context-use dag-run loop context-main context-use ;
: start ( k -- )
  dup bench-contexts slot @ ['] dag-run task-start throw swap bench-tasks slot ! ;
: run-tasks ( n -- )
  dup 0 ?do i start loop 0 ?do i bench-tasks slot @ task-wait throw loop ;
: ms-of ( n xt -- ms ) utime 2>r execute utime 2r> d- 1000 um/mod nip ;
: timed ( n xt -- ms ) over prepare over >r ms-of r> release ;
: row ( n -- )
  dup . ." jobs: " dup ['] run-serial timed dup . ." ms serial, "
  swap ['] run-tasks timed dup . ." ms in tasks, speed-up "
  100 swap */ 0 <# # # [char] . hold #s #> type cr ;
." task host " task-host . ." (0 serial, 1 cooperative, 2 threads)" cr
1 row 2 row 6 row 12 row
bye

\ Report-only speed-up of the job pool (not part of make test): twelve
\ jobs of tests/lib/task-job.fs, run one after another in one task and on
\ a pool of 1, 2, 6 and 12 workers (at most task-cores), and the ratio.
\ Each job runs bench-rounds rounds and never yields; the pool is started
\ before the clock starts. Uses Gforth's utime; run with
\ `gforth tests/lib/task-bench.fs`. On a host without threads the ratio
\ is about 1.
require ../../src/lib/task.fs
include ./task-job.fs

400 constant bench-rounds
12 constant bench-jobs
create bench-contexts bench-jobs cells allot
create bench-handles bench-jobs cells allot
: slot ( k table -- addr ) swap cells + ;
: fresh ( -- context ) context-new throw dup context-use ;
: bench-job ( k -- ) 7919 * 17 + bench-rounds 0 dag-start ;
: prepare ( -- )
  bench-jobs 0 ?do fresh i bench-contexts slot ! i bench-job loop
  context-main context-use ;
: release ( -- ) bench-jobs 0 ?do i bench-contexts slot @ context-free throw loop ;
: run-serial ( -- )
  bench-jobs 0 ?do i bench-contexts slot @ context-use dag-run loop
  context-main context-use ;
: submit ( k -- )
  dup bench-contexts slot @ ['] dag-run job-submit throw swap bench-handles slot ! ;
: run-pool ( -- )
  bench-jobs 0 ?do i submit loop
  bench-jobs 0 ?do i bench-handles slot @ job-wait throw loop ;
: ms-of ( xt -- ms ) utime 2>r execute utime 2r> d- 1000 um/mod nip ;
: timed ( xt -- ms ) prepare ms-of release ;
: with-workers ( n -- ) pool-stop to task-workers pool-start throw ;
: .ratio ( serial pool -- ) 100 swap */ 0 <# # # [char] . hold #s #> type ;
: row ( n -- )
  with-workers pool-size . ." workers: " ['] run-serial timed dup . ." ms serial, "
  ['] run-pool timed dup . ." ms pool, speed-up " .ratio cr ;
." task host " task-host . ." (0 serial, 1 cooperative, 2 threads), " bench-jobs .
." jobs" cr
1 row 2 row 6 row 12 row
bye

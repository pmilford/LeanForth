\ Task adapter (ADR 0009): run a word in another Forth task with its own
\ context, and wait for it. The few host-specific words of parallel
\ checking live here. The host is chosen when this file loads:
\ - threads: Gforth 1.0, whose tasks are POSIX threads and use all cores;
\ - cooperative: Gforth 0.7.3 with its tasker.fs; tasks take turns on one
\   core, switching only at task-yield and task-wait;
\ - serial: any other Forth, or when forced (below); task-start runs the
\   word at once, to the end.
\ Words that share no mutable data give the same results on all three.
\ Requires: lib.fs (context.fs). Loads tasker.fs on Gforth 0.7.3, which
\ also makes TYPE, EMIT and KEY switch tasks.
\
\ task-start ( context xt -- task ior ) seals the context layout and runs
\ xt ( -- ) in a new task with context selected. On failure (ior nonzero,
\ task 0) nothing runs. task-wait ( task -- ior ) waits until xt has
\ returned or thrown, frees the task's record and gives xt's THROW code, 0
\ when it returned normally. The task that started a task waits for it,
\ exactly once.
\
\ Rules for a task's word: it reaches mutable state only through its own
\ context; it may read data that no task changes while tasks run; it never
\ ALLOTs or compiles (all tasks share one dictionary); it never selects
\ another task's context. A new task's data and return stacks are at least
\ task-data-cells and task-return-cells deep, and never smaller than the
\ main task's. A stack overflow in a task is a THROW that task-wait
\ reports on Gforth 1.0, but crashes the program on 0.7.3 (its task stacks
\ have no guard pages), so a recursive pass must bound its depth well
\ below them.
\ State: one ALLOCATEd job record per started task; on Gforth, task-job
\ (a USER variable: the job the current task runs); on Gforth 1.0, one
\ mutex, task-lock, around every job's done flag. Untrusted.

require ./lib.fs

begin-structure /job
  field: job-xt          \ the word the task runs ( -- )
  field: job-context     \ the context selected for it
  field: job-done        \ true once the word has returned or thrown
  field: job-ior         \ its THROW code, 0 when it returned normally
  field: job-owner       \ threads: the task told when the job is done
end-structure

\ Hosts, and the stack depth of a new task in cells. Gforth's main task
\ has 2,048 data and 1,920 return cells on 0.7.3 and 3,968 to 4,096 per
\ stack on 1.0; checker passes measured up to about 720 return cells, and
\ nested passes may approach 1,500.
0 constant task-serial
1 constant task-cooperative
2 constant task-threads
8192 constant task-data-cells
8192 constant task-return-cells

\ Run a job's word in its context, catching any THROW.
: job-body ( job -- ) dup job-context @ context-use job-xt @ execute ;
: job-run ( job -- ) dup ['] job-body catch dup if nip then swap job-ior ! ;

\ A word named task-serial-only, defined before this file loads, forces the
\ serial host, so that tests reach it on every Forth.
[defined] task-serial-only 0=
[defined] newtask4 and [defined] initiate and [defined] send-event and [if]
task-threads constant task-host
user task-job
mutex task-lock
\ The done flag is written and read under task-lock, so the job's results
\ are visible to the owner once it sees the flag; the event then wakes the
\ owner if it is waiting.
: job-done? ( job -- flag ) task-lock lock job-done @ task-lock unlock ;
: job-finish ( job -- )
  dup job-owner @ swap task-lock lock true swap job-done ! task-lock unlock
  ['] noop swap send-event ;
: task-body ( -- ) task-job @ dup job-run job-finish ;
: task-stacks ( -- u-data u-return u-fp u-locals )
  stacksize4 2>r task-return-cells cells max swap task-data-cells cells max swap 2r> ;
: task-new ( -- task ) task-stacks newtask4 ;
: job-launch ( job -- ior )
  up@ over job-owner ! ['] task-new catch ?dup if nip exit then
  tuck task-job swap 's ! ['] task-body swap initiate 0 ;
: job-wait ( job -- ) begin dup job-done? 0= while stop repeat drop ;
: task-yield ( -- ) pause ;
[else] [defined] task-serial-only 0= [defined] next-task and [defined] udp and [if]
require tasker.fs
task-cooperative constant task-host
user task-job
: job-done? ( job -- flag ) job-done @ ;
: job-finish ( job -- ) true swap job-done ! ;
\ THROW saves the return stack up to backtrace-rp0, which a new task
\ inherits pointing into its creator's stack: point it at the task's own
\ (as Gforth 1.0's thread-init does).
: task-body ( -- ) rp@ cell+ backtrace-rp0 ! task-job @ dup job-run job-finish ;
\ A user variable's address in another task; next-task is the first one.
: task-user ( addr task -- addr' ) + next-task - ;
\ The caller continues at once; the new task runs task-body when its turn comes.
: task-go ( task -- ) activate task-body ;
: task-new ( -- task ) task-data-cells task-return-cells max cells newtask ;
: job-launch ( job -- ior )
  ['] task-new catch ?dup if nip exit then
  tuck task-job swap task-user ! task-go 0 ;
: job-wait ( job -- ) begin dup job-done? 0= while pause repeat drop ;
: task-yield ( -- ) pause ;
[else]
task-serial constant task-host
: job-launch ( job -- ior )
  lf-context @ >r dup job-run true swap job-done ! r> lf-context ! 0 ;
: job-wait ( job -- ) drop ;
: task-yield ( -- ) ;
[then] [then]

\ Starting and waiting.
: job-new ( context xt -- job ior )
  /job allocate ?dup if nip nip nip 0 swap exit then
  dup /job erase tuck job-xt ! tuck job-context ! 0 ;
: job-started ( job ior -- task ior ) dup if swap free drop 0 swap then ;
: task-start ( context xt -- task ior )
  context-seal job-new dup if exit then drop dup job-launch job-started ;
: task-wait ( task -- ior )
  dup job-wait dup job-ior @ swap free over if drop else nip then ;

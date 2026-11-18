\ Job pool (ADR 0009): run words as jobs, each in its own context, on a
\ fixed pool of long-lived worker tasks fed from a bounded queue, and wait
\ for them. The few host-specific words of parallel checking live here.
\ The host is chosen when this file loads:
\ - threads: Gforth 1.0, whose tasks are POSIX threads on all cores; one
\   mutex guards the queue and the jobs' results, and idle workers and
\   waiting tasks sleep on two condition variables;
\ - cooperative: Gforth 0.7.3 with its tasker.fs; the workers take turns on
\   one core, switching only at task-yield and while a task waits;
\ - serial: any other Forth, or when forced (below); there are no workers,
\   and job-submit runs the word at once, to the end, in the calling task.
\ Words that share no mutable data give the same results on all three.
\ Loads tasker.fs on Gforth 0.7.3, which also makes TYPE, EMIT and KEY
\ switch tasks.
\
\ job-submit ( context xt -- job ior ) claims the context for a new job
\ (see context.fs) and queues the job; a worker runs xt ( -- ) with that
\ context selected. job-wait ( job -- ior ) waits until xt has returned or
\ thrown, releases the context, frees the job and gives 0 when xt returned
\ with the stack depth unchanged; otherwise xt's THROW code,
\ task-unbalanced, task-overflow, or FREE's ior. 0 means only that the
\ word returned, never that a check was accepted; on any other value the
\ context's contents must be discarded. The task that submitted a job
\ waits for it, exactly once, outside any job; job-wait refuses job 0
\ (task-refused), reading nothing. A refused submission (job
\ 0, ior nonzero) runs and claims nothing; refused are: an address that
\ is not a context, the main context, the caller's current context or a
\ context another job owns, and any submission inside a job
\ (task-refused); a full queue (task-queue-full); a pool none of whose
\ workers could be created (task-no-worker); stack settings below the
\ largest need a module stated (task-stacks-small); and, on the
\ cooperative host, every submission after an overflow that left a guard
\ zone (task-overflow).
\
\ job-wait-any ( addr n -- k ) waits until the first of the n jobs whose
\ handles are the cells at addr (0 for none) has finished and gives its
\ position, for job-wait (a scheduler keeping one job per worker).
\
\ The pool starts at the first job-submit, or at pool-start, with
\ task-workers workers (at least 1, at most task-cores; pool-workers!
\ sets it, stopping a running pool), and runs until pool-stop, which lets
\ the workers finish every queued job first. One task outside the pool
\ (normally the main task) drives it: it alone submits, waits, and starts
\ and stops the pool. When the host refuses a worker (no thread near the
\ process limit, ulimit -u; no memory for its stacks), the pool runs with
\ the workers made before it, which workers-running ( -- n ) gives, and
\ is refused (task-no-worker) only when it made none; results do not
\ depend on the number of workers. spawn-limit! ( n -- ) makes the host
\ refuse every worker beyond n running, as it would near its limit, so
\ that tests reach that failure deterministically (-1, the default: no
\ limit but the host's).
\
\ Rules for a job's word: it reaches mutable state only through its own
\ context; it may read data that no task changes while jobs run; it never
\ ALLOTs or compiles (all tasks share one dictionary), never selects
\ another context, and never makes, frees or waits for contexts or jobs.
\ Nor does it parse (EVALUATE, WORD, PARSE) or use PAD: on Gforth 1.0,
\ HERE, PAD and WORD's buffer are one for all tasks. Each task has its own
\ BASE, a worker's copied from the main task's when the pool starts, so a
\ word that changes BASE restores it. The pictured numeric output buffer
\ is each task's own on Gforth 1.0 but one for all on 0.7.3, so a word
\ uses the text of <# ... #> before it yields, types or emits. Each
\ Gforth 1.0 worker has its own THROW backtrace and error strings
\ (worker-start).
\
\ Stacks: each worker's data and return stacks hold task-data-cells and
\ task-return-cells cells, less task-slack-cells for the worker's own
\ words; job-stacks-cover? tells whether that covers a requirement, and
\ pool-start refuses settings that do not cover the needs modules stated
\ with context-need (lib/context.fs) while they loaded. On
\ Gforth 1.0 an overflow is a THROW (-3 or -5) behind a guard page. Gforth
\ 0.7.3's task stacks have no guard pages, so each worker keeps
\ task-guard-cells canary cells beyond the far end of each stack, checked
\ after every job: an overflow into them gives task-overflow; one that went
\ beyond them may already have corrupted other memory, so it also breaks
\ the pool, and every later job fails. On the serial host a job runs on
\ the caller's stacks, where an overflow is the host's THROW.
\
\ Example: two jobs, each in a context of its own, waited for in turn.
\   variable a  variable b
\   : job-a ( -- ) 6 7 * a ! ;   : job-b ( -- ) 100 b ! ;
\   context-new throw constant c1  context-new throw constant c2
\   c1 ' job-a job-submit throw  c2 ' job-b job-submit throw
\   job-wait . job-wait .  a @ . b @ .   \ 0 0 42 100
\   c1 context-free throw  c2 context-free throw  pool-stop
\   \ prints: 0 0 42 100
\
\ State: the pool record task-pool and the ring task-queue (shared; on
\ Gforth 1.0 guarded by task-lock), and one ALLOCATEd job record per
\ submitted job, until it is waited for. Untrusted.

require ./lib.fs

\ THROW codes of the pool, outside Forth-2012's reserved range.
-4096 constant task-unbalanced  \ the job's word changed the stack depth
-4097 constant task-overflow    \ a job overran its worker's stacks (0.7.3)
-4098 constant task-refused     \ submission or wait not allowed
-4099 constant task-queue-full  \ task-queue-jobs jobs are queued already
-4100 constant task-no-worker   \ a worker task could not be created
-4101 constant task-stacks-small \ the workers' stacks are below the stated need

0 constant task-serial
1 constant task-cooperative
2 constant task-threads

\ Settings, read when the pool starts. Stack depths of each worker in
\ cells: 8,192, or the main task's if larger (Gforth 0.7.3: 2,048 data and
\ 1,920 return cells; 1.0: 4,096 and 3,968); raise them with TO while the
\ pool is stopped. The largest need the checker states is inference with
\ beta nested at its deepest level, 1,664 return and 1,280 data cells
\ (mixed-infer.fs); pool-start refuses settings that do not cover it.
: env-cells ( c-addr u -- n ) environment? 0= if 0 then ;
8192 s" STACK-CELLS" env-cells max value task-data-cells
8192 s" RETURN-STACK-CELLS" env-cells max value task-return-cells
64 constant task-slack-cells      \ cells the worker's own words use
1024 constant task-guard-cells    \ canary cells beyond each stack (0.7.3)
1024 constant task-scratch-bytes  \ for HERE, PAD and WORD below them (0.7.3)
1024 constant task-queue-jobs     \ most jobs queued at once

\ Logical cores online, from Linux's /sys/devices/system/cpu/online (a
\ list such as 0-5,8,10-11, read into PAD while this file loads); 1 where
\ that cannot be read.
: cpu-read ( -- c-addr u )
  s" /sys/devices/system/cpu/online" r/o open-file if drop pad 0 exit then
  >r pad dup 80 r@ read-line 0= and and r> close-file drop ;
: cpu-number ( c-addr u -- n c-addr' u' ) 0 0 2swap >number rot drop ;
: cpu-skip ( c-addr u -- c-addr' u' ) dup 0> 1 and /string ;
: cpu-dash? ( c-addr u -- flag ) 1 min s" -" compare 0= ;
: cpu-range ( first c-addr u -- n c-addr' u' ) cpu-skip cpu-number 2swap swap - 1+ -rot ;
: cpu-item ( c-addr u -- n c-addr' u' )
  cpu-number 2dup cpu-dash? if cpu-range else rot drop 1 -rot then cpu-skip ;
: cpu-count ( c-addr u -- n ) 0 -rot begin dup 0> while cpu-item 2>r + 2r> repeat 2drop ;
cpu-read cpu-count 1 max constant task-cores
\ Workers the pool starts: every core unless changed with TO while the
\ pool is stopped; kept between 1 and task-cores.
task-cores value task-workers

begin-structure /pool
  field: pool-head        \ queue index of the oldest queued job
  field: pool-queued      \ jobs queued, not yet taken by a worker
  field: pool-live        \ workers running
  field: pool-stopping    \ true while pool-stop waits for the workers
  field: pool-broken      \ true after an overflow beyond a guard zone
  field: pool-stack-bytes \ bytes per stack of each worker (0.7.3)
  field: pool-threads     \ worker threads to join when stopping (1.0)
  field: pool-spawn-limit \ workers running beyond which the host refuses one
end-structure
create task-pool /pool allot  task-pool /pool erase  true task-pool pool-spawn-limit !
create task-queue task-queue-jobs cells allot

begin-structure /job
  field: job-xt           \ the word the job runs ( -- )
  field: job-context      \ the context it owns and runs in
  field: job-done         \ true once the word has returned or thrown
  field: job-ior          \ its result, as job-wait gives it
end-structure

\ The first nonzero ior of two, else 0.
: ior-first ( ior1 ior2 -- ior ) over if drop else nip then ;
\ Bytes of each stack of a 0.7.3 worker: the deeper of the two, its guard
\ zone and the scratch room.
: task-stack-bytes ( -- u )
  task-data-cells task-return-cells max task-guard-cells + cells task-scratch-bytes + ;
\ The host's limit on the workers running (see the header): -1, the
\ default, is the largest unsigned number, so no limit but the host's.
\ spawn-allowed? tells whether the host makes one more worker; read by
\ the driving task while it starts the pool, when no worker leaves.
: spawn-limit! ( n -- ) task-pool pool-spawn-limit ! ;
: spawn-allowed? ( -- flag ) task-pool dup pool-live @ swap pool-spawn-limit @ u< ;
\ What pthread_create gives when the host refuses a thread (EAGAIN).
11 constant host-refused

\ Running a job, in a worker or (serial host) in the submitting task.
\ job-call runs xt above the job's own address, a sentinel, and throws
\ task-unbalanced when xt changed the stack depth or the sentinel; so a
\ word with a wrong stack effect never goes unnoticed, even one that
\ consumes and replaces the cell below it.
: ?balanced ( flag -- ) 0= if task-unbalanced throw then ;
: job-call ( job xt -- ) over >r depth >r execute depth r> 1- = ?balanced r> = ?balanced ;
: job-body ( job -- ) dup job-context @ context-use dup job-xt @ job-call ;
\ Run the job's word as its owner, in its context, and give its ior; the
\ task's own context and token are restored afterwards, whatever the word
\ did to them.
: job-run ( job -- ior )
  lf-context @ lf-owner @ 2>r dup lf-owner ! ['] job-body catch dup if nip then
  2r> lf-owner ! lf-context ! ;
: job-done! ( ior job -- ) tuck job-ior ! true swap job-done ! ;

\ Hosts. Each defines task-host, task-yield, the pool lock and its two
\ conditions (work: a job was queued or the pool stops; change: a job
\ finished or a worker left), task-self ( -- task ), a worker's own
\ task, and stacks-ior ( task -- ior ), its stack check after a job. A
\ word named task-serial-only, defined before this file loads, forces the
\ serial host, so that tests reach it on every Forth.
[defined] task-serial-only 0= [defined] newtask4 and
[defined] pthread_cond_wait and [defined] save-task and [if]
task-threads constant task-host
mutex task-lock
cond task-work
cond task-change
: pool-lock ( -- ) task-lock lock ;
: pool-unlock ( -- ) task-lock unlock ;
: work-wait ( -- ) task-work task-lock pthread_cond_wait drop ;
: work-signal ( -- ) task-work pthread_cond_signal drop ;
: work-broadcast ( -- ) task-work pthread_cond_broadcast drop ;
: change-wait ( -- ) task-change task-lock pthread_cond_wait drop ;
: change-broadcast ( -- ) task-change pthread_cond_broadcast drop ;
: task-yield ( -- ) pause ;
: task-self ( -- task ) up@ ;
: stacks-ior ( task -- ior ) drop 0 ;
[else] [defined] task-serial-only 0= [defined] next-task and [defined] udp and [if]
require tasker.fs
task-cooperative constant task-host
: task-yield ( -- ) pause ;
\ A task's address is the start of its user area, where next-task is.
: task-self ( -- task ) next-task ;
: task-user ( addr task -- addr' ) + next-task - ;
\ tasker.fs's NewTask lays a task out, from low to high addresses, as its
\ HERE, its data, FP and locals stacks, its user area and its return
\ stack, each stack pool-stack-bytes; every stack grows down. The guard
\ zones lie at the far end of the data stack (above the scratch room) and
\ of the return stack (above the user area).
: task-stacks ( -- u ) task-pool pool-stack-bytes @ ;
: guard-data ( task -- zone ) task-stacks 3 * - task-scratch-bytes + ;
: guard-return ( task -- zone ) udp @ + ;
: task-shaped? ( task -- flag )
  sp0 over task-user @ over task-stacks 2* - =
  swap rp0 over task-user @ swap guard-return task-stacks + = and ;
\ Each canary cell holds its own address masked, so no run of equal
\ values that a stack might push matches it.
1431655765 constant canary-mask
: canary ( addr -- x ) canary-mask xor ;
: zone-span ( zone -- end start ) task-guard-cells cells over + swap ;
: zone-fill ( zone -- ) zone-span ?do i canary i ! 1 cells +loop ;
: zone-intact? ( zone -- flag ) true swap zone-span ?do i @ i canary = and 1 cells +loop ;
\ The far cell of a zone, next to memory outside the stack, intact.
: zone-held? ( zone -- flag ) dup @ swap canary = ;
: guards ( task -- data-zone return-zone ) dup guard-data swap guard-return ;
: guards-fill ( task -- ) guards zone-fill zone-fill ;
: guards-intact? ( task -- flag ) guards zone-intact? swap zone-intact? and ;
: guards-held? ( task -- flag ) guards zone-held? swap zone-held? and ;
\ 0 when both zones are intact; otherwise task-overflow with the zones
\ refilled, and a broken pool when the overflow went past a zone.
: guards-check ( task -- ior )
  dup guards-held? 0= if true task-pool pool-broken ! then
  dup guards-intact? if drop 0 else guards-fill task-overflow then ;
: stacks-ior ( task -- ior )
  guards-check task-pool pool-broken @ task-overflow and ior-first ;
[else]
task-serial constant task-host
: task-yield ( -- ) ;
: task-self ( -- task ) 0 ;
: stacks-ior ( task -- ior ) drop 0 ;
[then] [then]
task-host task-threads <> [if]
\ One task runs at a time: no lock is needed, and waiting is yielding.
: pool-lock ( -- ) ;
: pool-unlock ( -- ) ;
: work-wait ( -- ) task-yield ;
: work-signal ( -- ) ;
: work-broadcast ( -- ) ;
: change-wait ( -- ) task-yield ;
: change-broadcast ( -- ) ;
[then]

\ The queue: a ring of task-queue-jobs cells, used under the pool lock.
: queue-slot ( n -- addr ) task-queue-jobs mod cells task-queue + ;
: queue-empty? ( -- flag ) task-pool pool-queued @ 0= ;
: queue-full? ( -- flag ) task-pool pool-queued @ task-queue-jobs = ;
: queue-put ( job -- )
  task-pool dup pool-head @ swap pool-queued @ + queue-slot ! 1 task-pool pool-queued +! ;
: queue-take ( -- job )
  task-pool pool-head dup @ dup 1+ task-queue-jobs mod rot ! queue-slot @
  -1 task-pool pool-queued +! ;

\ Workers. job-next waits for a job, or gives 0 once the pool stops with
\ the queue empty. After job-finish sets the done flag, under the lock,
\ the worker never touches the job again: its owner may free it at once.
: pool-idle? ( -- flag ) queue-empty? task-pool pool-stopping @ 0= and ;
: job-next ( -- job|0 )
  pool-lock begin pool-idle? while work-wait repeat
  queue-empty? if 0 else queue-take then pool-unlock ;
: job-finish ( ior job -- ) pool-lock job-done! change-broadcast pool-unlock ;
\ Run a job and check the worker's stacks; an overflow takes precedence.
\ The task and the job stay on the return stack while the word runs, out
\ of the reach of a word with a wrong stack effect.
: job-checked ( task job -- ior ) 2>r r@ job-run 2r> drop stacks-ior swap ior-first ;
: job-serve ( task job -- ) dup >r job-checked r> job-finish ;
: worker-left ( -- ) pool-lock -1 task-pool pool-live +! change-broadcast pool-unlock ;
: worker-loop ( task -- ) >r begin job-next ?dup while r@ swap job-serve repeat r> drop ;
\ A worker's whole life, in its own task.
: worker-run ( -- ) 0 lf-context ! 0 lf-owner ! task-self worker-loop worker-left ;

\ Creating a worker: worker-launch ( task -- errno ) starts a new task on
\ worker-run and gives 0, or nonzero when it could not. workers-join
\ ( -- ) waits until every worker that left has ended.
task-host task-threads = [if]
\ Start task on the rest of the calling word and give pthread_create's
\ error number: the steps of Gforth 1.0's (activate) in unix/pthread.fs,
\ which drops that number. Compile-only. A task whose thread could not be
\ created is disposed of by task-unmade (below).
: (spawn) ( task -- errno )
  r> over save-task swap 's ! >r pthread-id r@ 's 0 thread_start r> pthread_create ;
\ Each worker owns its heap strings. Gforth 1.0's newtask4 copies the
\ creator's user area into the new task (unix/pthread.fs:257), and
\ thread-init resets only part of it (pthread.fs:246), so a worker would
\ start with the main task's two heap strings: stored-backtrace
\ (except.fs:33), which every THROW inside a CATCH stores the return
\ stack into (except.fs:139, backtrac.fs:45), and error-stack
\ (kernel/int.fs:735), which an EVALUATE or INCLUDED that a THROW unwinds
\ grows (kernel/input.fs:127). Once the main task had thrown, throws in
\ jobs resized and freed its string from other threads and corrupted the
\ heap. So a worker starts with neither (0 is the empty string) and frees
\ its own when it ends.
: strings-own ( -- ) 0 stored-backtrace ! 0 error-stack ! ;
: strings-free ( -- ) stored-backtrace $free error-stack $free ;
: worker-life ( -- ) strings-own worker-run strings-free ;
: worker-start ( task -- errno ) (spawn) up! thread-init worker-life ;
: worker-stacks ( -- u-data u-return u-fp u-locals )
  stacksize4 2>r task-return-cells cells max swap task-data-cells cells max swap 2r> ;
: task-make ( -- task ) worker-stacks newtask4 ;
\ Worker threads are joinable (a set pthread-joinwait keeps Gforth's
\ kill-task from detaching them); their ids are copied here, since a
\ task's user area is freed when its thread ends. workers-join joins them,
\ so no worker is still ending when the program exits (Gforth's cilk.fs
\ does the same).
create worker-ids task-cores pthreads allot
: worker-id ( k -- addr ) pthreads worker-ids + ;
: worker-joinable ( task -- ) up@ pthread-joinwait rot 's ! ;
: worker-id! ( task -- )
  pthread-id swap 's task-pool pool-threads @ worker-id 1 pthreads move
  1 task-pool pool-threads +! ;
\ The thread started (worker-start), or, beyond the spawn limit, refused
\ as the host refuses one (host-refused, no thread made).
: worker-try ( task -- errno )
  spawn-allowed? if worker-start else drop host-refused then ;
\ A task whose thread was not made: its two pipes closed, as Gforth's
\ kill-task closes a task's own (pthread.fs:221), so that refusals do not
\ use up file descriptors; its stacks stay allocated (Gforth 1.0 has no
\ word that frees a task that never ran).
: pipe-close ( addr task -- ) 's @ ?dup if close-file drop then ;
: task-unmade ( task -- ) epiper over pipe-close epipew swap pipe-close ;
: worker-launch ( task -- errno )
  dup worker-joinable dup worker-try ?dup if swap task-unmade exit then worker-id! 0 ;
: workers-join ( -- )
  task-pool pool-threads @ 0 ?do i worker-id 0 pthread_join drop loop
  0 task-pool pool-threads ! ;
[then]
task-host task-cooperative = [if]
\ THROW saves the return stack up to backtrace-rp0, which a new task
\ inherits pointing into its creator's stack: point it at the task's own
\ (as Gforth 1.0's thread-init does).
: worker-body ( -- ) rp@ cell+ backtrace-rp0 ! worker-run ;
\ The caller continues at once; the new task runs worker-body in its turn.
: worker-go ( task -- ) activate worker-body ;
\ A task of another layout, or one beyond the spawn limit, is freed
\ (tasker.fs's kill) and never runs.
: worker-fits? ( task -- flag ) task-shaped? spawn-allowed? and ;
: worker-launch ( task -- errno )
  dup worker-fits? 0= if kill host-refused exit then dup guards-fill worker-go 0 ;
: task-make ( -- task ) task-stacks newtask ;
: workers-join ( -- ) ;
[then]
task-host task-serial = [if]
: worker-launch ( task -- errno ) drop 1 ;
: task-make ( -- task ) 0 ;
: workers-join ( -- ) ;
[then]
: task-new ( -- task ior ) ['] task-make catch dup if 0 swap then ;
: worker-spawn ( -- ior )
  task-new if drop task-no-worker exit then worker-launch 0<> task-no-worker and ;

\ Whether a job's word may nest data-cells and return-cells deep: within
\ the workers' stacks less task-slack-cells, or on the serial host within
\ the host's stack sizes less task-slack-cells (the caller's own use also
\ comes off those; a host that does not report a size is not checked, as
\ mixed-beta.fs does not check it). A recursive pass needs about its
\ frames limit times its cells per frame (frame.fs) plus its entry words.
: covers? ( need have -- flag ) task-slack-cells - > 0= ;
: env-covers? ( need c-addr u -- flag ) environment? if covers? else drop true then ;
task-host task-serial = [if]
: job-stacks-cover? ( data-cells return-cells -- flag )
  s" RETURN-STACK-CELLS" env-covers? swap s" STACK-CELLS" env-covers? and ;
[else]
: job-stacks-cover? ( data-cells return-cells -- flag )
  task-return-cells covers? swap task-data-cells covers? and ;
[then]

\ Starting and stopping the pool. pool-start starts it, unless it runs,
\ and gives 0; or task-stacks-small, starting nothing, when the stack
\ settings do not cover the largest need a module stated (context-need,
\ context.fs); or task-no-worker when not one worker could be created.
\ When the host refuses a worker after others were made, the pool runs
\ with those (workers-running), until it is stopped; none is tried after
\ the first refusal. It seals the context layout first, so no need can
\ be stated later. pool-stop lets the workers finish every queued job,
\ then waits until all have left; it aborts inside a job.
task-host task-serial = [if]
: pool-size ( -- n ) 0 ;
[else]
: pool-size ( -- n ) task-workers 1 max task-cores min ;
[then]
: workers-running ( -- n ) task-pool pool-live @ ;
: pool-running? ( -- flag ) workers-running 0> ;
: worker-added ( -- ) pool-lock 1 task-pool pool-live +! pool-unlock ;
: worker-add ( -- ior ) worker-spawn dup 0= if worker-added then ;
: pool-fill ( n -- ior ) 0 ?do worker-add ?dup if unloop exit then loop 0 ;
: pool-drain ( -- ) begin task-pool pool-live @ while change-wait repeat ;
: pool-halt ( -- )
  pool-lock true task-pool pool-stopping ! work-broadcast pool-drain
  false task-pool pool-stopping ! pool-unlock ;
: pool-stop ( -- ) lf-owner @ abort" pool-stop: inside a job" pool-halt workers-join ;
: pool-stacks? ( -- flag ) context-needs job-stacks-cover? ;
\ A refusal after a worker was made leaves the pool running with fewer.
: pool-fresh ( -- ior )
  task-stack-bytes task-pool pool-stack-bytes !
  pool-size pool-fill pool-running? if drop 0 then ;
: pool-start ( -- ior )
  pool-running? if 0 exit then
  context-seal pool-stacks? if pool-fresh else task-stacks-small then ;

\ Submitting. job-refusal gives why a submission is refused before
\ anything is made, or 0, starting the pool if needed.
task-host task-serial = [if]
: job-launch ( job -- ior ) dup >r job-run r> job-done! 0 ;
[else]
: job-queue ( job -- ior )
  queue-full? if drop task-queue-full else queue-put work-signal 0 then ;
: job-launch ( job -- ior ) pool-lock job-queue pool-unlock ;
[then]
: job-refusal ( -- ior )
  lf-owner @ if task-refused exit then
  task-pool pool-broken @ if task-overflow exit then pool-start ;
: job-new ( context xt -- job ior )
  /job allocate0 ?dup if >r drop 2drop 0 r> exit then tuck job-xt ! tuck job-context ! 0 ;
: job-claim ( job -- flag ) dup job-context @ context-claim ;
: job-unclaim ( job -- job ) dup job-context @ context-release ;
: job-drop ( job ior -- 0 ior ) swap free drop 0 swap ;
\ The job stays on the return stack: on the serial host its word runs here.
: job-launched ( job -- job ior ) dup >r job-launch r> swap ;
: job-submit ( context xt -- job ior )
  job-refusal ?dup if nip nip 0 swap exit then
  job-new ?dup if exit then
  dup job-claim 0= if task-refused job-drop exit then
  job-launched dup if >r job-unclaim r> job-drop then ;

\ Waiting. job-wait refuses inside a job, leaving the job alone, and for
\ job 0, the handle of a refused submission, which it never reads.
: job-await ( job -- )
  pool-lock begin dup job-done @ 0= while change-wait repeat pool-unlock drop ;
: wait-refused? ( job -- flag ) 0= lf-owner @ 0<> or ;
: job-wait ( job -- ior )
  dup wait-refused? if drop task-refused exit then
  dup job-await job-unclaim dup job-ior @ swap free ior-first ;

\ Waiting for the first of several jobs (a scheduler that keeps one job
\ per worker): job-wait-any ( addr n -- k ) waits until one of the jobs
\ whose handles are the n cells from addr (0 for none) has returned or
\ thrown, and gives the lowest position of one that has, which the
\ caller then gives job-wait (it returns at once); -1 when every cell is
\ 0, and inside a job, where it waits for nothing. It frees nothing.
\ The flags are read under the pool lock, and the caller sleeps on the
\ same condition job-finish signals, so no finish is missed.
: jobs-done ( addr n -- k|-1 )
  0 ?do dup i cells + @ ?dup if job-done @ if drop i unloop exit then then loop
  drop -1 ;
: jobs-any? ( addr n -- flag ) cells bounds false -rot ?do i @ 0<> or 1 cells +loop ;
: jobs-await ( addr n -- k )
  pool-lock begin 2dup jobs-done dup 0< while drop change-wait repeat nip nip
  pool-unlock ;
: job-wait-any ( addr n -- k )
  lf-owner @ if 2drop -1 exit then 2dup jobs-any? if jobs-await else 2drop -1 then ;

\ The pool's size for the next start: n workers, kept between 1 and
\ task-cores; a running pool is stopped first (its queued jobs finish).
\ Outside jobs only, as pool-stop.
: pool-workers! ( n -- )
  pool-running? if pool-stop then 1 max task-cores min to task-workers ;

\ On Gforth 1.0 the program's end first stops the pool (outside a job),
\ so that no worker thread is still running while the process exits.
task-host task-threads = [if]
:noname ( -- ) lf-owner @ 0= if pool-stop then defers bye ; is bye
[then]

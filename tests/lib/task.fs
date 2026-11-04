\ Tests of the job pool (src/lib/task.fs) with checker contexts: jobs run
\ by the pool's workers, each in its own context, and contexts interleaved
\ in one task, must give exactly the results of the same jobs run one
\ after another, with any number of workers. Each job builds and walks
\ random DAGs and ends with a recursive pass about dag-depth frames deep,
\ inside its worker (tests/lib/task-job.fs). Then every refusal: words
\ with a wrong stack effect, the main, current, shared and busy contexts,
\ jobs inside jobs, a full queue and workers that cannot be created. On
\ Gforth 1.0 the workers are threads; on 0.7.3 they are cooperative and
\ yield every few visits; task-serial.fs runs this file on the serial
\ host. Stack overflows are in task-overflow.fs.
include ../support/tester.fs
include ../support/checks.fs
require ../../src/lib/task.fs
include ./task-job.fs

\ Results recorded inside a job (nested jobs, a worker's strings).
4 cells context-record: notes

\ Stack needs (context.fs): the largest stated data and return need is
\ kept, each on its own; pool-start refuses settings below it (below).
T{ context-needs -> 0 0 }T
600 300 context-need  100 700 context-need  50 50 context-need
T{ context-needs -> 600 700 }T

6 constant jobs
3 constant job-rounds
16 constant job-every
create serial-sums jobs cells allot
create serial-visits jobs cells allot
create job-contexts jobs cells allot
create job-handles jobs cells allot
: slot ( k table -- addr ) swap cells + ;
: aborts? ( addr xt -- flag ) catch dup if nip then 0<> ;  \ for ( addr -- ) words
: aborts0? ( xt -- flag ) catch 0<> ;  \ for words without inputs
: pooled? ( -- flag ) task-host task-serial <> ;

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
\ The recursive pass used over 900 cells of each stack inside the worker.
: deep? ( k -- flag )
  job-contexts slot @ context-use
  dag-state dag-deep @ 900 > dag-state dag-data @ 900 > and ;
: deep-count ( -- n ) 0 jobs 0 ?do i deep? - loop context-main context-use ;

\ A context per job, then every job submitted, then all waited for.
: prepare ( k -- context )
  fresh tuck over job-contexts slot ! job-every dag-job context-main context-use ;
: submit-job ( k -- ior )
  dup prepare ['] dag-run job-submit >r swap job-handles slot ! r> ;
: submit-all ( -- failures ) 0 jobs 0 ?do i submit-job 0<> - loop ;
: wait-all ( -- failures ) 0 jobs 0 ?do i job-handles slot @ job-wait 0<> - loop ;
: free-all ( -- failures ) 0 jobs 0 ?do i job-contexts slot @ context-free 0<> - loop ;
: batch ( -- failures )
  submit-all wait-all + wrong-count + deep-count jobs - + free-all + ;

T{ ' submit-all rs-checked ' wait-all rs-checked -> 0 0 }T
T{ wrong-count deep-count -> 0 jobs }T
T{ lf-context @ context-main = -> true }T
T{ free-all -> 0 }T
\ A second batch, which reuses freed memory, gives the same results.
T{ batch -> 0 }T

\ Any number of workers gives the serial results: the pool restarts with
\ 1, 2 and every core; each count is kept between 1 and task-cores.
: with-workers ( n -- ) pool-stop to task-workers pool-start throw ;
: live ( -- n ) task-pool pool-live @ ;
T{ 1 with-workers live batch -> pooled? 1 and 0 }T
T{ 2 with-workers live batch -> pooled? 2 task-cores min and 0 }T
T{ 0 with-workers live -> pooled? 1 and }T
T{ task-cores 5 + with-workers live -> pooled? task-cores and }T
T{ task-cores with-workers live batch -> pooled? task-cores and 0 }T
T{ pool-stop live pool-start live -> 0 0 pooled? task-cores and }T

\ A word that throws ends its own job with that THROW code, while other
\ jobs run on unaffected.
: thrower ( -- ) 37 throw ;
: run-thrower ( -- ior )
  context-new throw dup ['] thrower job-submit throw job-wait swap context-free throw ;
T{ ' run-thrower rs-checked -> 37 }T
T{ submit-all run-thrower wait-all wrong-count free-all -> 0 37 0 0 0 }T

\ Throws in jobs once the main task has thrown. On Gforth 1.0 a THROW
\ inside a CATCH stores a backtrace, and a failed EVALUATE its error
\ frames, in heap strings of the throwing task's own. Workers started after
\ the main task threw must not start with its strings (task.fs,
\ worker-start), or throws in jobs resize and free them from other threads
\ and corrupt the heap. So, with the pool started after the main task
\ threw: no job starts with a main-task string (checked before any job
\ throws, so that it fails cleanly); then jobs throw at many depths, the
\ main task's strings stay unchanged, and it throws on. Other hosts keep
\ no such strings per task; there the jobs' throws are checked alone.
: threads? ( -- flag ) task-host task-threads = ;
threads? [if]
: strings@ ( -- backtrace errors ) stored-backtrace @ error-stack @ ;
: string-sum ( $addr -- x ) $@ 0 -rot bounds ?do 31 * i @ + 1 cells +loop ;
: strings-sum ( -- x ) stored-backtrace string-sum error-stack string-sum + ;
[else]
: strings@ ( -- 0 0 ) 0 0 ;
: strings-sum ( -- 0 ) 0 ;
[then]
: main-throws ( -- ior ior )
  ['] thrower catch  s" no-such-word-here" ['] evaluate catch nip nip ;
: strings-job ( -- ) strings@ notes 2! ;
: deep-throw ( n -- ) ?dup if 1- recurse then 38 throw ;
: throw-job ( -- ) 200 0 do i 32 mod ['] deep-throw catch 2drop loop 38 throw ;
create throw-contexts jobs cells allot
create throw-handles jobs cells allot
: throw-context ( k -- context ) throw-contexts slot @ ;
: throw-new ( -- ) jobs 0 ?do context-new throw i throw-contexts slot ! loop ;
: throw-submit ( xt k -- xt )
  tuck throw-context over job-submit throw rot throw-handles slot ! ;
: throw-all ( xt -- ) jobs 0 ?do i throw-submit loop drop ;
\ How many jobs gave ior.
: ior-count ( ior -- n ) 0 jobs 0 ?do over i throw-handles slot @ job-wait = - loop nip ;
create main-strings 2 cells allot
\ Whether a job's string x is the main task's, main; none (0) never is.
: shared? ( main x -- flag ) over = and 0<> ;
: either-shared? ( backtrace errors -- flag )
  main-strings 2@ rot shared? >r swap shared? r> or ;
: noted ( k -- backtrace errors )
  throw-context context-use notes 2@ context-main context-use ;
: throw-shared ( -- n ) 0 jobs 0 ?do i noted either-shared? - loop ;
: throw-free ( -- failures ) 0 jobs 0 ?do i throw-context context-free 0<> - loop ;
variable main-sum
T{ pool-stop main-throws pool-start -> 37 -13 0 }T
strings@ main-strings 2!  strings-sum main-sum !  throw-new
T{ main-strings 2@ 0<> swap 0<> and -> threads? }T
T{ ' strings-job throw-all 0 ior-count throw-shared -> jobs 0 }T
T{ ' throw-job throw-all 38 ior-count strings-sum main-sum @ = -> jobs true }T
T{ main-throws throw-free -> 37 -13 0 }T
T{ lf-context @ context-main = -> true }T
T{ depth -> 0 }T

\ A word with a wrong stack effect fails with task-unbalanced, even one
\ that consumes and replaces a cell, and the job record, the worker and
\ the memory around them are unharmed.
create victim 8 cells allot  victim 8 cells -1 fill
: leaves ( -- x ) victim ;
: eats ( x -- ) drop ;
: swaps ( x -- y ) drop victim ;
: victim-intact? ( -- flag ) true 8 0 do victim i cells + @ -1 = and loop ;
: effect-ior ( xt -- ior ) context-new throw tuck swap job-submit throw job-wait
  swap context-free throw ;
T{ ' leaves effect-ior ' eats effect-ior ' swaps effect-ior -> task-unbalanced dup dup }T
T{ victim-intact? -> true }T
T{ submit-all wait-all wrong-count free-all -> 0 0 0 0 }T

\ Refusals: an address that is not a context, the main context, the
\ caller's current context; nothing is claimed, so each can be freed.
create not-a-context 4 cells allot  not-a-context 4 cells erase
T{ not-a-context ' dag-run job-submit -> 0 task-refused }T
T{ 0 ' dag-run job-submit -> 0 task-refused }T
T{ context-main ' dag-run job-submit -> 0 task-refused }T
context-new throw constant c1
c1 context-use
T{ c1 ' dag-run job-submit -> 0 task-refused }T
context-main context-use
T{ c1 context-idle? -> true }T

\ Ownership: a submitted job owns its context until it is waited for:
\ a second job on it is refused, and it cannot be selected or freed;
\ afterwards it is idle again.
c1 context-use 0 0 dag-job context-main context-use
c1 ' dag-run job-submit throw constant j1
T{ c1 ' dag-run job-submit -> 0 task-refused }T
T{ c1 context-idle? c1 ' context-use aborts? -> false true }T
T{ c1 ' context-free aborts? -> true }T
T{ lf-context @ context-main = -> true }T
T{ j1 job-wait c1 context-idle? -> 0 true }T
T{ c1 context-use 0 serial@ dag-results d= context-main context-use -> true }T

\ Inside a job: submitting, waiting, making or freeing a context and
\ stopping the pool are all refused, and the main context is not the job's.
: note ( x k -- ) cells notes + ! ;
: nester ( -- )
  c1 ['] noop job-submit 0 note 1 note  j1 job-wait 2 note
  ['] context-new aborts0? 3 note ;
: nest-aborts ( -- )
  context-main ['] context-use aborts? 0 note
  c1 ['] context-free aborts? 1 note  ['] pool-stop aborts0? 2 note ;
context-new throw constant c2
: in-job ( xt -- ior ) c2 swap job-submit throw job-wait ;
: note@ ( k -- x ) cells notes + @ ;
: notes@ ( -- a b c d )
  c2 context-use 0 note@ 1 note@ 2 note@ 3 note@ context-main context-use ;
T{ ' nester in-job notes@ -> 0 task-refused 0 task-refused true }T
T{ ' nest-aborts in-job notes@ drop -> 0 true true true }T
T{ c1 context-free c2 context-free -> 0 0 }T

\ The comparison detects interference: with the random seed planted in one
\ shared variable instead of each context, interleaved jobs no longer give
\ the serial results.
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
variable shared-seed
: shared-seed-cell ( -- addr ) shared-seed ;
' shared-seed-cell is dag-seed-cell
T{ prepare-pair interleave pair-wrong -> 2 }T
free-pair
' dag-own-seed is dag-seed-cell
T{ prepare-pair interleave pair-wrong -> 0 }T
free-pair

\ Stack coverage: the workers' depths less the slack, nothing more.
: depths ( -- data return ) task-data-cells task-return-cells pooled? 0= if
  2drop s" STACK-CELLS" env-cells s" RETURN-STACK-CELLS" env-cells then ;
T{ depths task-slack-cells - swap task-slack-cells - swap job-stacks-cover? -> true }T
: at-limit ( -- data return ) depths task-slack-cells - swap task-slack-cells - swap ;
T{ at-limit 1+ job-stacks-cover? at-limit swap 1+ swap job-stacks-cover? -> false false }T
\ The layout is sealed: no need can be stated any more.
: need-refused? ( -- flag )
  s" 1 1 context-need" ['] evaluate catch dup if nip nip then 0<> ;
T{ need-refused? context-needs -> true 600 700 }T

T{ lf-context @ context-main = -> true }T
T{ depth -> 0 }T

pooled? [if]
\ A full queue: every worker held at a gate (a shared variable, only in
\ this test), then task-queue-jobs jobs queued; one more is refused, and
\ nothing is claimed. Released, all finish.
variable gate  0 gate !
: gated ( -- ) begin gate @ 0= while task-yield repeat ;
task-queue-jobs pool-size + constant held
create held-contexts held cells allot
create held-jobs held cells allot
: held-new ( -- ) held 0 ?do context-new throw i held-contexts slot ! loop ;
: held-submit ( k -- )
  dup held-contexts slot @ ['] gated job-submit throw swap held-jobs slot ! ;
: taken ( -- ) begin task-pool pool-queued @ while task-yield repeat ;
: hold-workers ( -- ) pool-size 0 ?do i held-submit loop taken ;
: fill-queue ( -- ) held pool-size ?do i held-submit loop ;
: release ( -- failures )
  true gate ! 0 held 0 ?do i held-jobs slot @ job-wait 0<> - loop ;
: held-free ( -- failures ) 0 held 0 ?do i held-contexts slot @ context-free 0<> - loop ;
held-new context-new throw constant c3
T{ hold-workers fill-queue task-pool pool-queued @ -> task-queue-jobs }T
T{ c3 ' noop job-submit c3 context-idle? -> 0 task-queue-full true }T
T{ release held-free -> 0 0 }T
T{ c3 ' noop job-submit throw job-wait -> 0 }T

\ Workers that cannot be created (stacks too large to allocate): the
\ failure is reported, nothing runs or is claimed, and the pool starts
\ again once the setting is back. (Gforth 1.0 also prints why to stderr.)
task-data-cells constant normal-cells
T{ pool-stop max-n 8 cells / to task-data-cells pool-start live -> task-no-worker 0 }T
T{ c3 ' noop job-submit c3 context-idle? -> 0 task-no-worker true }T
normal-cells to task-data-cells
T{ pool-start live c3 ' noop job-submit throw job-wait -> 0 pooled? task-cores and 0 }T
\ Stack settings below the stated need: the pool does not start, every
\ submission is refused and nothing is claimed, until the setting is back.
task-return-cells constant normal-return
T{ pool-stop 600 to task-data-cells pool-start live -> task-stacks-small 0 }T
T{ c3 ' noop job-submit c3 context-idle? -> 0 task-stacks-small true }T
normal-cells to task-data-cells  700 to task-return-cells
T{ pool-start live -> task-stacks-small 0 }T
normal-return to task-return-cells
T{ pool-start live c3 ' noop job-submit throw job-wait -> 0 pooled? task-cores and 0 }T
c3 context-free throw
T{ depth -> 0 }T
[then]

." task host " task-host . ." (0 serial, 1 cooperative, 2 threads), " pool-size .
." workers; recursive pass used "
fresh 0 0 dag-job dag-run dag-state dag-deep @ . ." return and "
dag-state dag-data @ . ." data-stack cells" cr
lf-context @ context-free throw
bye

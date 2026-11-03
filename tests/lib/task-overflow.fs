\ Stack overflows inside jobs (src/lib/task.fs) never report success. The
\ pool has one worker, so every job runs in the worker that overflowed
\ before. Gforth 1.0: the worker's guard pages give THROW -3 (data stack)
\ or -5 (return stack), and the worker serves later jobs normally. Gforth
\ 0.7.3: an overflow into a worker's guard zone gives task-overflow and the
\ worker goes on; one that goes past the zone (here two cells into the
\ worker's user area, overwriting lf-owner and lf-context) gives
\ task-overflow and breaks the pool, which then refuses every
\ submission. Serial host (task-overflow-serial.fs): the host's THROW in
\ the calling task, caught by the job.
include ../support/tester.fs
include ../support/checks.fs
require ../../src/lib/task.fs

1 cells context-record: marks

\ deep n nests n+1 calls, one return-stack cell each; pile n pushes n
\ data-stack cells and drops them again.
: deep ( n -- ) ?dup if 1- recurse then ;
: pushes ( n -- ) 0 ?do 0 loop ;
: drops ( n -- ) 0 ?do drop loop ;
: pile ( n -- ) dup >r pushes r> drops ;

\ How deep each job goes: on 0.7.3 measured from inside the job to its
\ worker's guard zones; elsewhere twice the stack sizes, past any limit.
task-host task-cooperative = [if]
: data-room ( -- cells ) sp@ task-self guard-data - 1 cells / task-guard-cells - ;
: return-room ( -- cells ) rp@ task-self guard-return - 1 cells / task-guard-cells - ;
: into-guard ( room -- n ) task-guard-cells 2/ + ;
: past-guard ( room -- n ) task-guard-cells + 2 + ;
task-overflow constant data-overflow
task-overflow constant return-overflow
[else]
: data-room ( -- cells ) task-data-cells s" STACK-CELLS" env-cells max 2* ;
: return-room ( -- cells ) task-return-cells s" RETURN-STACK-CELLS" env-cells max 2* ;
: into-guard ( room -- n ) ;
: past-guard ( room -- n ) ;
-3 constant data-overflow
-5 constant return-overflow
[then]

\ Each job leaves the stacks balanced if it returns, and marks its
\ context, except return-past: on 0.7.3 it overwrites lf-context.
: data-over ( -- ) data-room into-guard pile 1 marks ! ;
: return-over ( -- ) return-room into-guard deep 1 marks ! ;
: return-past ( -- ) return-room past-guard deep ;
: fine ( -- ) 1000 deep 1000 pile 1 marks ! ;

: with-workers ( n -- ) pool-stop to task-workers pool-start throw ;
1 with-workers
context-new throw constant c
: run ( xt -- ior ) c swap job-submit throw job-wait ;
: marked? ( -- flag ) c context-use marks @ 0<> 0 marks ! context-main context-use ;
: broken? ( -- flag ) task-pool pool-broken @ ;

\ On 0.7.3 an overflow within the guard zone is caught after the word
\ returned, so the word's own mark is set.
T{ ' fine run marked? -> 0 true }T
T{ ' data-over run marked? -> data-overflow task-host task-cooperative = }T
T{ broken? -> false }T
T{ ' fine run marked? -> 0 true }T
T{ ' return-over run marked? -> return-overflow task-host task-cooperative = }T
T{ broken? -> false }T
T{ ' fine run marked? broken? -> 0 true false }T
T{ ' return-past run -> return-overflow }T
T{ lf-context @ context-main = lf-owner @ -> true 0 }T
task-host task-cooperative = [if]
T{ task-pool pool-broken @ c ' fine job-submit -> true 0 task-overflow }T
[else]
T{ ' fine run marked? -> 0 true }T
[then]
c context-free throw
T{ depth -> 0 }T
." task host " task-host . ." overflows: data " data-overflow . ." return "
return-overflow . cr
bye

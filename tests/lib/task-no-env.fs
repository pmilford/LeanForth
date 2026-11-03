\ A serial host that does not report its stack sizes (ENVIRONMENT? may
\ answer false for STACK-CELLS and RETURN-STACK-CELLS, as Forth-2012
\ allows): such a host is not checked, by mixed-beta.fs and mixed-infer.fs
\ when they load and by the job pool, so the kernel loads after task.fs
\ and jobs run. Defining task-serial-only before src/lib/task.fs forces
\ the serial host on every Forth; here ENVIRONMENT? answers false for
\ every query.
include ../support/tester.fs
: environment? ( c-addr u -- false ) 2drop false ;
: task-serial-only ( -- ) ;
require ../../src/lib/task.fs
require ../../src/kernel/mixed-infer.fs
T{ task-host -> task-serial }T
T{ max-n 2/ max-n 2/ job-stacks-cover? -> true }T
T{ context-needs -> lf-minfer-data-cells lf-minfer-return-cells }T
T{ pool-start -> 0 }T
context-new throw constant c1
T{ c1 ' noop job-submit throw job-wait -> 0 }T
T{ c1 context-free -> 0 }T
T{ depth -> 0 }T
bye

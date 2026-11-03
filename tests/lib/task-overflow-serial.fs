\ The overflow tests on the serial host, where a job runs on the calling
\ task's stacks: defining task-serial-only before src/lib/task.fs loads
\ forces it, so CI tests that path on both Gforths.
: task-serial-only ( -- ) ;
include ./task-overflow.fs

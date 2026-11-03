\ The checked environment's interleaving tests on the serial host, which
\ every Forth without a supported tasker uses: defining task-serial-only
\ before src/lib/task.fs loads forces it, so CI tests the serial path on
\ both Gforths. Jobs then run to the end when submitted, one after another.
: task-serial-only ( -- ) ;
include ./environment-tasks.fs

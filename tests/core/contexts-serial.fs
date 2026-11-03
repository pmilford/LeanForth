\ The context tests on the serial host, which every Forth without a
\ supported tasker uses: defining task-serial-only before src/lib/task.fs
\ loads forces it, so CI tests the serial path on both Gforths.
: task-serial-only ( -- ) ;
include ./contexts.fs

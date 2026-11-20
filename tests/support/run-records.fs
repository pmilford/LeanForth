\ Run records and their replay without the export's manifest (plan task
\ 2.2.5; docs/programming/RUN_RECORDS.md): the driver of
\ src/import/run-record.fs and run-replay.fs. It reads an export into the
\ checker's input with src/import/checker-input.fs through rr-import, the
\ manifest not checked (cin-read; the record notes the manifest's outcome
\ and says the manifest was not enforced) and
\ checks it with rr-check (fuel for each check, a pool of ni-pool
\ dependencies), then writes the run record to a file (ni-record) or
\ compares it with one written earlier and prints the replay report
\ (ni-replay). Test-only; bin/leanforth's check --record and replay are
\ the same run with the manifest checked by default
\ (docs/user/COMMAND_LINE.md). Forth only, no Python on the path.
\ For make, from the repository root:
\   gforth tests/support/run-records.fs -e 's" FILE" 100000 s" RECORD" ni-record ni-exit'
\   gforth tests/support/run-records.fs -e 's" FILE" 100000 s" RECORD" ni-replay ni-exit'
\ with -e 's" COMMIT" FLAG ni-source' first to record the LeanForth
\ commit and whether the tree differed from it (make run-record does).
\ ni-exit leaves Gforth with status 0 for ok, 1 for anything else.
\ State: the checker input's and the two modules' shared records; one run
\ at a time.

require ../../src/import/checker-input.fs
require ../../src/import/run-record.fs
require ../../src/import/run-replay.fs

64 constant ni-pool   \ dependencies the environment holds, as the command line gives it

\ Read and check the export file c-addr u, each declaration with fuel,
\ and write its record into rr-text: ok, or the outcome of the first step
\ that failed (rr-start, rr-finish, rr-write). A file the transport cannot
\ read still gets a record, which says so and lists no declarations. The
\ run's environment stays current until rr-release.
: ni-run ( c-addr u fuel -- outcome )
  ni-pool rr-settings! rr-start dup ok? 0= if exit then drop
  false rr-import ok? if rr-check then rr-finish dup ok? if drop rr-write then ;
\ Write the record of the export file c-addr1 u1 to the file c-addr2 u2.
: ni-record ( c-addr1 u1 fuel c-addr2 u2 -- outcome )
  2>r ni-run dup ok? if drop 2r> rr-save else 2r> 2drop then rr-release ;
\ Check the export file c-addr1 u1 again and compare its record with the
\ record in the file c-addr2 u2; print the replay report. ok only when the
\ record is confirmed.
: ni-reported ( outcome -- outcome ) rp-report ok? 0= if drop outcome-invalid then ;
: ni-replay ( c-addr1 u1 fuel c-addr2 u2 -- outcome )
  2>r ni-run ok? if 2r> rp-replay else 2r> 2drop rp-rerun-refused then
  rr-release ni-reported ;
\ The LeanForth commit and whether the tree differed from it; aborts on a
\ commit that is not 40 lowercase hexadecimal digits.
: ni-source ( c-addr u flag -- ) rr-source! ok? 0= abort" run-records: bad commit" ;
\ Leave Gforth with status 0 for ok, else 1 (Gforth's (bye)).
: ni-exit ( outcome -- ) ok? if 0 else 1 then (bye) ;

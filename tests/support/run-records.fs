\ Run records and their replay through the test-only transport (plan task
\ 2.2.5; docs/programming/RUN_RECORDS.md): the driver of
\ src/import/run-record.fs and run-replay.fs. It reads an export with
\ tests/support/ndjson-input.fs and checks it as ni-check does (fuel for
\ each check, a pool of ni-pool dependencies), then writes the run record
\ to a file (ni-record) or compares it with one written earlier and
\ prints the replay report (ni-replay). Test-only, like the transport,
\ which phase 3's importer replaces; Forth only, no Python on the path.
\ For make, from the repository root:
\   gforth tests/support/run-records.fs -e 's" FILE" 100000 s" RECORD" ni-record ni-exit'
\   gforth tests/support/run-records.fs -e 's" FILE" 100000 s" RECORD" ni-replay ni-exit'
\ with -e 's" COMMIT" FLAG ni-source' first to record the LeanForth
\ commit and whether the tree differed from it (make run-record does).
\ ni-exit leaves Gforth with status 0 for ok, 1 for anything else.
\ State: the transport's and the two modules' shared records; one run at
\ a time.

require ./ndjson-input.fs
require ../../src/import/run-record.fs
require ../../src/import/run-replay.fs

64 constant ni-pool   \ dependencies the environment holds, as ni-check gives it

\ Read and check the export file c-addr u, each declaration with fuel,
\ and write its record into rr-text: ok, or the outcome of the first step
\ that failed (rr-start, rr-finish, rr-write). A file the transport cannot
\ read still gets a record, which says so and lists no declarations. The
\ run's environment stays current until rr-release.
: ni-run ( c-addr u fuel -- outcome )
  ni-pool rr-settings! 2dup rr-start dup ok? 0= if nip nip exit then drop
  2dup ni-read dup rr-read! ok? if rr-check then
  rr-finish dup ok? if drop rr-write then ;
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

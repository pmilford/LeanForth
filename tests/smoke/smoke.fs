\ Smoke test of the loader: everything in src/main.fs loads, the data stack
\ is empty afterwards, and one word from each loaded layer runs.
require ../../src/main.fs

: smoke-fail ( flag -- ) if -1 throw then ;
depth smoke-fail

\ Core: build a Sort 7 node and read back its tag and fields.
: smoke-term ( -- )
  lf-term-reset 7 lf-term-sort 0= smoke-fail lf-term-read 0= smoke-fail
  0<> smoke-fail 7 <> smoke-fail lf-tag-sort <> smoke-fail ;

\ Import: a staging batch opens, a second open is refused, abort closes it.
: smoke-import ( -- )
  lf-load-begin 0= smoke-fail lf-load-begin smoke-fail lf-load-abort ;

\ Import: the NDJSON reader opens a fixture; with no handlers set, it
\ refuses the first record as unsupported.
export: smoke-export
: smoke-reader ( -- )
  smoke-export export-init ok? 0= smoke-fail s" tests/reference/identity.ndjson" smoke-export export-read
  outcome-unsupported <> smoke-fail smoke-export export-free ;

\ Program: clamp a value above the range to the upper bound.
: smoke-program ( -- ) 15 0 10 lf-clamp 0= smoke-fail 10 <> smoke-fail ;

smoke-term smoke-import smoke-reader smoke-program depth smoke-fail
bye

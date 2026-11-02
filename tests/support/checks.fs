\ Shared checks for Forth test files; include after tester.fs. Test-only words.
\ Named cases report a THROW and continue, but any case that changes the data
\ stack depth stops the file. A return-stack marker checks a single call.

variable case-failures  0 case-failures !

\ Report one caught THROW and count it.
: case-failed ( error -- ) .error-string cr 1 case-failures +! ;

\ Run a named case; the caller's stack depth must be the same afterwards.
: run-case ( i*x xt addr len -- i*x )
  type cr depth 1- >r catch ?dup if case-failed then
  depth r> <> abort" test stack imbalance" ;

\ Print the failure count and fail the file if any case failed.
: cases-done ( -- )
  case-failures @ dup . ." case(s) failed" cr abort" test case failed" ;

24379 constant rs-marker

\ Execute xt above a return-stack marker; fail unless the marker survives.
: rs-checked ( i*x xt -- j*x )
  rs-marker >r execute r> rs-marker <> abort" return stack imbalance" ;

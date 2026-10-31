\ Adapt Gforth's bundled tester to fail the process on the first assertion.
\ Both Gforth 0.7.3 and 1.0.0 expose ERROR-XT; their error counters differ.
\ A failure prints the tester message and source line, then throws to the host.
require test/ttester.fs

\ Report the failing assertion and terminate this test file unsuccessfully.
: lf-test-fail ( address length -- )
  type source type cr -1 throw ;

' lf-test-fail error-xt !

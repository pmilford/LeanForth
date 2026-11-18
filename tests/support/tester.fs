\ Adapt Gforth's bundled tester to fail the process on the first assertion.
\ Both Gforth 0.7.3 and 1.0.0 expose ERROR-XT; their error counters differ.
\ A failure prints the tester message and source line, then throws to the host.
require test/ttester.fs

\ Report the failing assertion and terminate this test file unsuccessfully.
: lf-test-fail ( address length -- )
  type source type cr -1 throw ;

' lf-test-fail error-xt !

\ Whether this engine checks the data stack's depth, reporting an underflow
\ as THROW -4: Gforth's checking engine (1.0 and 0.7.3) does, gforth-fast
\ does not; told by the program's name. A test of the host's own underflow
\ report runs only where it holds (unit tests run on both engines).
: host-checks-depth? ( -- flag ) 0 arg s" gforth-fast" search nip nip 0= ;

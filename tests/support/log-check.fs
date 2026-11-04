\ The derivation log's structural check for tests: lc-valid? runs
\ src/present/log-check.fs's lf-log-flaw on the current context's log (the
\ check the outline printer applies before it prints from a log; its
\ header lists the parts) and keeps the first part that failed for
\ lc-why. Test-only.

require ../../src/present/log-check.fs

variable lc-failed   \ the first part that failed, 0 when none
: lc-why ( -- part ) lc-failed @ ;
\ Whether the log passes: true, or false with lc-why the first part that
\ failed (1 rule, 2 start, 3 nesting, 4 reference, 5 publish, 6 copy,
\ 7 truncation, 8 no log, 9 premise kinds).
: lc-valid? ( -- flag ) lf-log-flaw dup lc-failed ! 0= ;

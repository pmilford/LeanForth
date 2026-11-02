\ The deepest nesting a full level store allows: a chain of 63 successor
\ steps above zero, evaluated and compared within the default host stacks
\ of Gforth 0.7.3 and 1.0 (both passes recurse on the host stacks). A host
\ stack overflow would throw and fail this test.
include ../support/tester.fs
include ../support/checks.fs
include ../../src/core/levels.fs
include ../../src/core/level-scope.fs
include ../../src/kernel/level-value.fs
include ../../src/kernel/level-compare.fs

lf-level-reset lf-lscope-context-reset
: succ-chain ( n -- top ) 0 swap 0 ?do lf-level-succ 0= abort" chain" loop ;
63 succ-chain constant top
T{ top lf-level-count @ -> 63 64 }T
T{ top 1000 lf-level-value lf-lvalue-fuel @ -> 63 outcome-ok 1000 128 - }T
T{ top top 1000 lf-level-compare lf-lcmp-fuel @ -> outcome-ok 680 }T
\ The same nesting with too little fuel is exhaustion, never a crash.
T{ top 100 lf-level-value nip -> outcome-exhausted }T
T{ top top 100 lf-level-compare -> outcome-exhausted }T
bye

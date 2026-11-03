\ The deepest nesting a full level store allows: a chain of 63 successor
\ steps above zero, evaluated and compared within the default host stacks
\ of Gforth 0.7.3 and 1.0 (both passes recurse on the host stacks). A host
\ stack overflow would throw and fail this test.
include ../support/tester.fs
include ../support/checks.fs
require ../../src/lib/lib.fs
require ../../src/core/level-scope.fs
require ../../src/core/levels.fs
require ../../src/kernel/level-compare.fs
require ../../src/kernel/level-value.fs

lf-level-reset lf-lscope-context-reset
: succ-chain ( n -- top ) 0 swap 0 ?do lf-level-succ 0= abort" chain" loop ;
63 succ-chain constant top
T{ top lf-level-count @ -> 63 64 }T
T{ top 1000 lf-level-value lf-lvalue-fuel @ -> 63 outcome-ok 1000 128 - }T
T{ top top 1000 lf-level-compare lf-lcmp-fuel @ -> outcome-ok 680 }T
\ The same nesting with too little fuel is exhaustion, never a crash.
T{ top 100 lf-level-value nip -> outcome-exhausted }T
T{ top top 100 lf-level-compare -> outcome-exhausted }T
\ The depth limits lie one level below what a full store can reach, so they
\ are reached here white-box: a visit at the limit is full and spends no
\ fuel; with no fuel either, the fuel decides (exhausted).
10 lf-lvalue-fuel !
T{ 0 lf-lvalue-depth-limit lf-lvalue-walk lf-lvalue-fuel @ -> -1 outcome-full 10 }T
T{ 0 lf-lvalue-depth-limit 1- lf-lvalue-walk lf-lvalue-fuel @ -> 0 outcome-ok 9 }T
0 lf-lvalue-fuel !
T{ 0 lf-lvalue-depth-limit lf-lvalue-walk -> -1 outcome-exhausted }T
10 lf-lcmp-fuel !
T{ 0 0 lf-lcmp-depth-limit lf-lcmp-walk lf-lcmp-fuel @ -> outcome-full 10 }T
T{ 0 0 lf-lcmp-depth-limit 1- lf-lcmp-walk lf-lcmp-fuel @ -> outcome-ok 7 }T
0 lf-lcmp-fuel !
T{ 0 0 lf-lcmp-depth-limit lf-lcmp-walk -> outcome-exhausted }T
bye

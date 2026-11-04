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
\ Structurally equal: only the two scope checks of 64 visits are charged.
T{ top top 1000 lf-level-compare lf-lcmp-fuel @ -> outcome-ok 872 }T
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
\ Lean's normalize (level-normalize) recurses once per imax or max level:
\ an imax chain of 62 levels over u (each step's normal form is u again,
\ so nothing is allocated) and a max chain of 60 levels over v, whose 61
\ arguments are flattened, normalized, sorted and reduced to max u v (one
\ new node, in the one free record), compared with u.
require ../../src/core/names.fs
: must ( flag -- ) 0= abort" deep" ;
\ n nodes of tag over the previous one and right, from start.
: chain ( right start tag n -- top )
  0 ?do >r 2dup swap r@ lf-level-binary must nip r> loop drop nip ;
lf-name-reset lf-level-reset lf-lscope-context-reset
0 s" u" lf-name-str must constant u-id   0 s" v" lf-name-str must constant v-id
u-id lf-lscope-context-add must v-id lf-lscope-context-add must
u-id lf-level-param must constant u
T{ u u lf-level-tag-imax 62 chain lf-level-count @ -> 63 64 }T
T{ 63 u 100000 lf-level-compare -> outcome-ok }T
T{ u 63 100000 lf-level-inequivalent? -> false outcome-ok }T
lf-level-reset
u-id lf-level-param must drop v-id lf-level-param must constant v
T{ v u lf-level-tag-max 60 chain lf-level-count @ -> 62 63 }T
T{ 62 u 100000 lf-level-inequivalent? lf-level-count @ -> true outcome-ok 63 }T
T{ 62 62 100000 lf-level-compare -> outcome-ok }T
bye

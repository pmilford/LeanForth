\ The head of a reduced term (src/kernel/mixed-head.fs; ADR 0011's rule
\ names): every kind lf-mhead-kind gives, with and without arguments, and
\ the spine. Coverage classes of docs/development/TEST_COVERAGE_REVIEW.md:
\ 1, 3. Each head: a symbolic Sort, a Pi and a lambda (rigid), a bound
\    and a free variable (rigid, also applied), a constant and a
\    projection (flexible, also applied); a Sort or Pi applied, a lambda
\    applied (none), a let and a concrete Sort (none); the spine's head
\    and argument count; which kinds rules D1-D5 compare.
\ 2. An index the store does not hold: none.
\ tests/core/definite-rejection.fs uses the same kinds in its rules.
\ Test-only; nothing here accepts a theorem.
include ../support/tester.fs
require ../../src/load/kernel.fs
decimal

: must ( flag -- ) 0= abort" mixed-head test: refused" ;
lf-name-reset lf-level-reset lf-term-reset lf-cref-reset lf-lctx-reset
4096 lf-term-capacity! drop
lf-ssession-begin must
: sort-node ( -- node ) 0 lf-term-symbolic-sort must ;
: var ( i -- node ) lf-term-bvar must ;
: app ( f a -- node ) lf-term-app must ;
: binary ( a b tag -- node ) lf-term-binary must ;
: pi-node ( -- node ) sort-node 0 var lf-tag-pi binary ;
: lam-node ( -- node ) sort-node 0 var lf-tag-lam binary ;
: named ( c-addr u -- id ) 0 -rot lf-name-str must ;
: const-node ( -- node )
  s" k" named lf-name-generation @ 0 0 lf-cref-new must lf-cterm-new must drop ;
: fvar-node ( -- node ) sort-node -1 lf-lctx-add ok? must ;
: proj-node ( -- node ) 0 var s" P" named 1 lf-proj-of ok? must ;
: kind ( node -- kind ) lf-mhead-kind ;
: applied ( node -- kind ) 1 var app 2 var app kind ;

\ Rigid heads alone; a Sort or Pi applied is ill typed (applied), a lambda
\ applied is a beta redex (none).
T{ sort-node kind pi-node kind lam-node kind -> lf-head-sort lf-head-pi lf-head-lam }T
T{ sort-node applied pi-node applied lam-node applied
   -> lf-head-applied lf-head-applied lf-head-none }T
\ Variables, bound and free, alone and applied.
T{ 0 var kind 0 var applied -> lf-head-var lf-head-var }T
T{ fvar-node kind fvar-node applied -> lf-head-var lf-head-var }T
\ Flexible heads: a constant and a projection, alone and applied.
T{ const-node kind const-node applied -> lf-head-constant lf-head-constant }T
T{ proj-node kind proj-node applied -> lf-head-constant lf-head-constant }T
\ No rule: a concrete Sort; an index the store does not hold.
T{ 0 lf-term-sort must kind -> lf-head-none }T
T{ -1 kind lf-term-count @ kind -> lf-head-none lf-head-none }T
\ The spine: head and count; a projection ends it as a head of its own.
T{ const-node dup 1 var app 2 var app lf-mhead-spine -rot = -> 2 true }T
T{ proj-node dup 1 var app lf-mhead-spine -rot = -> 1 true }T
T{ sort-node dup lf-mhead-spine -rot = -> 0 true }T
\ The shapes rules D1-D5 compare: Sort, Pi, lambda and variable only.
: shapes ( -- flags ) 7 0 do i lf-mhead-shape? loop ;
T{ shapes -> false true true true true false false }T
bye

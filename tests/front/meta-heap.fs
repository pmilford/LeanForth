\ A full heap for the front end's Meta layer (review of fe1c, L4; test
\ class 5 of docs/development/TEST_COVERAGE_REVIEW.md). Each operation runs
\ with its first, second, ... heap allocation or resize refused
\ (tests/support/heap-watch.fs) until it needs no more: every refused run
\ must answer full with no result and keep no heap block; the run that is
\ not refused gives the right answer. Operations: instantiate1, abstract,
\ headBeta (src/front/instantiate.fs), level equality (level-simp.fs),
\ universe-parameter instantiation of a level and of a term
\ (level-params.fs). Nothing here checks a theorem.
require ../support/tester.fs
require ../support/heap-watch.fs
require ../../src/main.fs

lf-author-begin lf-mctx-reset lf-lctx-reset
100000 lf-term-capacity! drop  100000 lf-level-capacity! drop
: must ( x flag -- x ) 0= abort" meta-heap: no room" ;
: made ( x outcome -- x ) ok? 0= abort" meta-heap: not made" ;

\ refusing ( xt -- x outcome n ): xt ( -- x outcome ) run with its k-th
\ allocation refused, k = 1, 2, ...; n refused runs, then the whole run's
\ answer. A refused run must answer full, x the value none holds, and
\ hold no more heap blocks than before the first (instantiate.fs keeps
\ its memo table from one walk to the next, so a small walk first makes
\ it).
variable held  variable none  variable refused
: refused-run ( xt k -- x outcome ) heap-refusals ! execute ;
: reached? ( -- flag ) heap-refusals @ 0= ;
: kept? ( -- flag ) live-blocks @ held @ > ;
: refused-ok ( x outcome -- )
  outcome-full <> abort" meta-heap: not full" none @ <> abort" meta-heap: a result"
  kept? abort" meta-heap: a heap block kept" 1 refused +! ;
: refusals ( xt -- xt k x outcome )
  0 refused ! live-blocks @ held ! 1 begin 2dup refused-run reached? while refused-ok 1+ repeat ;
: refusing ( xt -- x outcome n ) refusals 2swap 2drop 0 heap-refusals ! refused @ ;

\ Terms: x : Prop, #1000 under 1000 binders, x under 1000 binders, and
\ (fun a => a) applied to 300 arguments.
0 lf-term-sort must constant prop
prop lf-lctx-local made constant x
: lams ( body n -- t ) 0 ?do prop swap lf-term-lam must loop ;
: apps ( f n -- t ) 0 ?do x lf-term-app must loop ;
: seconds ( t n -- t' ) 0 ?do lf-term-second@ loop ;
1000 lf-term-bvar must 1000 lams constant deep
x 1000 lams constant xdeep
create xs x ,
prop 0 lf-term-bvar must lf-term-lam must 300 apps constant spine
: inst-op ( -- t outcome ) deep x lf-meta-instantiate1 ;
: abst-op ( -- t outcome ) xdeep xs 1 lf-meta-abstract ;
: beta-op ( -- t outcome ) spine lf-meta-head-beta ;
-1 none !
T{ 0 lf-term-bvar must x lf-meta-instantiate1 -> x outcome-ok }T
T{ ' inst-op refusing 0> swap ok? rot 1000 seconds -> true true x }T
T{ ' abst-op refusing 0> swap ok? rot 1000 seconds lf-term-first@ -> true true 1000 }T
\ headBeta's argument slab gets its block on its first use.
T{ prop 0 lf-term-bvar must lf-term-lam must 1 apps lf-meta-head-beta -> x outcome-ok }T
T{ ' beta-op refusing 0> swap ok? rot lf-term-second@ -> true true x }T

\ Levels: two equal 1000-successor levels made apart (sharing is off in
\ the authoring context); u + 1000 with u := 1; a constant C.{u, u} under
\ 100 applications with u := 1.
101 lf-level-param must constant u
0 lf-level-succ must constant one
: lsuccs ( l n -- l' ) 0 ?do lf-level-succ must loop ;
u 1000 lsuccs constant tall1
u 1000 lsuccs constant tall2
create ps 101 ,  create ls one ,
: leq-op ( -- flag outcome ) tall1 tall2 lf-meta-level= ;
: lps-op ( -- level outcome ) tall1 ps ls 1 lf-meta-level-params ;
create cpairs 4 cells allot
: cpair! ( level i -- ) 2* cells cpairs + >r dup lf-level-identity drop swap r> 2! ;
: const2 ( l1 l2 -- term )
  1 cpair! 0 cpair! 0 s" C" lf-name-str drop lf-name-generation @ cpairs 2 lf-cref-new
  must lf-cterm-new must drop ;
u u const2 100 apps constant cdeep
: ilp-op ( -- term outcome ) cdeep ps ls 1 lf-meta-instantiate-level-params ;
: clevel ( term -- level ) lf-term-first@ lf-cref-slot lf-cref-pairs drop 0 lf-cref-pair@ drop ;
: firsts ( t n -- t' ) 0 ?do lf-term-first@ loop ;
: lfirsts ( l n -- l' ) 0 ?do lf-level-first@ loop ;
false none !
T{ ' leq-op refusing 0> -> true outcome-ok true }T
-1 none !
T{ ' lps-op refusing 0> swap ok? rot 1000 lfirsts -> true true one }T
T{ ' ilp-op refusing 0> swap ok? rot 100 firsts clevel -> true true one }T

T{ depth -> 0 }T
cr .( meta-heap.fs: all tests passed) cr
bye

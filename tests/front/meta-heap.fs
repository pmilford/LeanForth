\ A full heap for the front end's Meta layer (review of fe1c, L4; test
\ class 5 of docs/development/TEST_COVERAGE_REVIEW.md). Each operation runs
\ with its first, second, ... heap allocation or resize refused
\ (tests/support/heap-watch.fs) until it needs no more: every refused run
\ must answer full with no result and keep no heap block; the run that is
\ not refused gives the right answer. Operations: instantiate1, abstract,
\ headBeta (src/front/instantiate.fs), level equality (level-simp.fs),
\ universe-parameter instantiation of a level and of a term
\ (level-params.fs), Level.normalize (level-normalize.fs). Nothing here
\ checks a theorem.
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
0 s" u" lf-name-str must constant u-id
0 s" v" lf-name-str must constant v-id
u-id lf-level-param must constant u
v-id lf-level-param must constant v
0 lf-level-succ must constant one
: lsuccs ( l n -- l' ) 0 ?do lf-level-succ must loop ;
u 1000 lsuccs constant tall1
u 1000 lsuccs constant tall2
create ps u-id ,  create ls one ,
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
\ Level.normalize (level-normalize.fs): max (v+500) (max u 1) under 500
\ successors is max (u+500) (v+1000); a small one first gives its slabs
\ their blocks.
: lmax ( a b -- l ) lf-level-max must ;
v 500 lsuccs u one lmax lmax 500 lsuccs constant nmax
T{ v u lmax lf-meta-level-normalize nip -> outcome-ok }T
: norm-op ( -- level outcome ) nmax lf-meta-level-normalize ;
T{ ' norm-op refusing 0> swap ok? rot dup lf-level-first@ 500 lfirsts swap
   lf-level-second@ 1000 lfirsts -> true true u v }T
\ Level.beq and Expr.eqv whose pair stack cannot grow (review reuse-1a
\ H1): a refused push, of the first pair or in a step (slab.fs's
\ slab-2all?), answers false and full, never a definite "different".
\ max v (max v .. (max v u)) and x applied to x 100 times, each made
\ twice apart, leave one pair waiting per level; Sorts of the two levels
\ compare the levels inside Expr.eqv. First the stacks' limits lowered
\ to 0 and 8 pairs, then every allocation refused in turn.
: vmaxes ( n -- l ) u swap 0 ?do v swap lmax loop ;
100 vmaxes constant vm1  100 vmaxes constant vm2
x 100 apps constant xa1  x 100 apps constant xa2
vm1 lf-term-symbolic-sort must constant vs1  vm2 lf-term-symbolic-sort must constant vs2
: leq-deep ( -- flag outcome ) vm1 vm2 lf-meta-level= ;
: eqv-deep ( -- flag outcome ) xa1 xa2 lf-meta-eqv ;
: eqv-sorts ( -- flag outcome ) vs1 vs2 lf-meta-eqv ;
T{ leq-deep eqv-deep eqv-sorts -> true outcome-ok true outcome-ok true outcome-ok }T
ls-pairs slab-limit constant ls-limit   eq-pairs slab-limit constant eq-limit
: slab-made ( outcome -- ) ok? 0= abort" meta-heap: no slab" ;
: pairs-room! ( n slab -- ) dup slab-free 2 cells -rot slab-init slab-made ;
: ls-room ( n -- ) ls-pairs pairs-room! ;
: eq-room ( n -- ) eq-pairs pairs-room! ;
T{ 0 ls-room leq-deep 8 ls-room leq-deep eqv-sorts
   -> false outcome-full false outcome-full false outcome-full }T
T{ 0 eq-room eqv-deep 8 eq-room eqv-deep -> false outcome-full false outcome-full }T
\ Fresh slabs: a small run gives each its first block, then each
\ allocation refused in turn (the pair stacks' RESIZEs) answers false
\ and full.
: ls-fresh ( -- flag outcome ) ls-limit ls-room tall1 tall2 lf-meta-level= ;
: x-x ( -- t ) x x lf-term-app must ;
: eq-fresh ( -- flag outcome ) eq-limit eq-room x-x x-x lf-meta-eqv ;
false none !
T{ ls-fresh ' leq-deep refusing 0> -> true outcome-ok true outcome-ok true }T
T{ eq-fresh ' eqv-deep refusing 0> -> true outcome-ok true outcome-ok true }T
T{ ls-fresh ' eqv-sorts refusing 0> -> true outcome-ok true outcome-ok true }T
\ Level unification (level-defeq.fs): 0 =?= max ?1 .. ?20, true through
\ normalization, a conjunction of 20 pairs (19 waiting on ld-pairs),
\ occurs checks and 20 assignments noted on the trail under a mark;
\ max u ?d =?= max u v, stuck (unsupported). A refused run answers full
\ and false and rolls its assignments back, among them the runs whose
\ pair stack or trail the heap does not let grow. A small one first gives
\ the trail and the pair stack their first blocks. (Each run normalizes
\ the shrinking chain again: about n^3 / 6 new levels, plan FE1c.)
lf-mctx-reset 1000000 lf-level-capacity! drop
: lnew ( -- level ) lf-level-mvar-new made ;
lnew constant md  lnew constant mw  lnew constant mx
T{ 0 mw mx lmax lf-meta-level-defeq -> true outcome-ok }T
: free? ( level -- flag ) lf-level-mvar-value dup if nip then 0= ;
variable newest
: wide ( n -- l ) lnew swap 1 ?do lnew dup newest ! lmax loop ;
\ Level.normalize of a max of 40 metavariables: lib/sort.fs merges more
\ than 32 arguments through a scratch the heap may refuse; sorted oldest
\ first, the newest last.
40 wide constant w40  newest @ constant w40-newest
: wide-norm-op ( -- level outcome ) w40 lf-meta-level-normalize ;
-1 none !
T{ ' wide-norm-op refusing 0> swap ok? rot lf-level-second@ w40-newest = -> true true true }T
20 wide constant w20
: conj-op ( -- flag outcome ) 0 w20 lf-meta-level-defeq ;
: stuck-op ( -- flag outcome ) u md lmax u v lmax lf-meta-level-defeq ;
false none !
T{ ' conj-op refusing 0> newest @ lf-level-mvar-value -> true outcome-ok true 0 true }T
T{ ' stuck-op refusing 0> md free? -> false outcome-unsupported true true }T
\ Marks the heap cannot grow: with marks open up to the slab's capacity,
\ level unification's own mark and then lf-mctx-mark are refused, full,
\ and nothing is assigned or opened; the marks then close in turn.
lnew constant me
: marks-to-room ( -- )
  begin lf-mctx-marks mv-marks slab-capacity < while lf-mctx-mark drop drop repeat ;
: close-marks ( -- ) begin lf-mctx-marks while lf-mctx-latest lf-mctx-rollback drop repeat ;
marks-to-room lf-mctx-marks constant open-marks
T{ 1 heap-refusals ! me 0 lf-meta-level-defeq me free? lf-mctx-marks
   -> false outcome-full true open-marks }T
T{ 1 heap-refusals ! lf-mctx-mark lf-mctx-marks -> 0 outcome-full open-marks }T
\ A depth scope refused for room goes no deeper (review s1-meta-a L1).
T{ 1 heap-refusals ! false lf-mctx-depth{ lf-mctx-depth lf-mctx-level-depth lf-mctx-marks
   -> 0 outcome-full 0 0 open-marks }T
T{ 0 heap-refusals ! close-marks lf-mctx-marks -> 0 }T
\ The undo trail's other slabs (S1 §3): a snapshot whose slab cannot
\ grow, a switch whose redo stack cannot, a delayed assignment whose three
\ records the trail has no room for: each full, and nothing changes (the
\ state, the trail's length, the open scopes).
lnew constant ms1  lnew constant ms2
variable hm  variable hs0  variable hs1  variable hn
: snap! ( addr -- ) lf-mctx-snapshot made swap ! ;
: snaps-to-room ( -- )
  begin mv-snaps slab-count mv-snaps slab-capacity < while lf-mctx-snapshot 2drop repeat ;
: trail-to-room ( -- )
  begin mv-trail slab-capacity mv-trail slab-count - 3 < 0= while
    lnew one lf-level-mvar-assign drop repeat ;
T{ lf-mctx-mark made hm ! hs0 snap! ms1 one lf-level-mvar-assign hs1 snap! -> outcome-ok }T
T{ snaps-to-room 1 heap-refusals ! lf-mctx-snapshot heap-refusals @ 0 heap-refusals !
   -> 0 outcome-full 0 }T
T{ hs0 @ lf-mctx-switch ms2 one lf-level-mvar-assign -> outcome-ok outcome-ok }T
T{ 1 heap-refusals ! hs1 @ lf-mctx-switch heap-refusals @ 0 heap-refusals ! ms1 free? ms2 free?
   -> outcome-full 0 true false }T
T{ hs1 @ lf-mctx-switch ms1 free? ms2 free? -> outcome-ok false true }T
: tm ( -- mvar ) prop mv-natural lf-mvar-new made ;
tm constant td1  tm constant tp1
T{ trail-to-room mv-trail slab-count hn ! 1 heap-refusals ! td1 tp1 0 lf-mvar-delay
   heap-refusals @ 0 heap-refusals ! td1 lf-mvar-delayed mv-trail slab-count hn @ =
   -> outcome-full 0 false true }T
T{ td1 tp1 0 lf-mvar-delay td1 lf-mvar-delayed nip nip nip -> outcome-ok true }T
T{ hm @ lf-mctx-rollback td1 lf-mvar-delayed ms1 free? lf-mctx-marks mv-trail slab-count
   -> outcome-ok false true 0 0 }T
\ instantiateMVars (mvars.fs). First, while the argument slab has no
\ block yet: ?d delayed over x forty times, ?p := x, ?d x .. x with 40
\ arguments, the 1st, 2nd, ... allocation refused until the slab has its
\ block; each run answers full with no result (review of fe1c-lnorm, M2:
\ the delayed step read past the slab and crashed; heap-watch.fs does not
\ see the slab's own block, so the slab's refusal is reached by lowering
\ its limit, below). Then every allocation refused in turn, and ?f x ..
\ x, 100 arguments, ?f := fun a => a.
lf-mctx-reset
: tnew ( -- mvar ) prop mv-natural lf-mvar-new made ;
tnew constant tp  tnew constant td
T{ tp x lf-mvar-assign -> outcome-ok }T
: delay-fvars ( n -- ) 0 ?do x lf-delay-fvar drop loop ;
40 delay-fvars
T{ td tp 40 lf-mvar-delay -> outcome-ok }T
td 40 apps constant td-spine
: delay-op ( -- term outcome ) td-spine lf-instantiate-mvars ;
: cold-run ( k -- )
  heap-refusals ! delay-op 0 heap-refusals !
  outcome-full <> abort" meta-heap: not full" -1 <> abort" meta-heap: a result" ;
: cold-runs ( -- n ) 0 begin 1+ dup cold-run mv-args slab-capacity until ;
T{ mv-args slab-capacity cold-runs 1 > mv-args slab-capacity 0> -> 0 true true }T
\ The argument slab itself full (heap-watch.fs does not refuse its
\ growth): its limit lowered to 8 arguments, the 40-argument delayed
\ term answers full with no result; the limit restored, x (re-check of
\ fe1c-lnorm, N1).
mv-args slab-limit constant args-limit
: args-room! ( n -- outcome ) mv-args slab-free 1 cells swap mv-args slab-init ;
T{ 8 args-room! delay-op args-limit args-room! -> outcome-ok -1 outcome-full outcome-ok }T
\ A whole run first makes the blocks the walks keep (instantiate.fs's memo).
T{ delay-op -> x outcome-ok }T
-1 none !
T{ ' delay-op refusing 0> swap ok? rot -> true true x }T
tnew constant tf
T{ tf prop 0 lf-term-bvar must lf-term-lam must lf-mvar-assign -> outcome-ok }T
tf 100 apps constant tf-spine
: mvinst-op ( -- term outcome ) tf-spine lf-instantiate-mvars ;
T{ ' mvinst-op refusing 0> swap ok? rot 99 firsts -> true true x }T
\ The same past dag-walk.fs's cut-over, its states in a memo of the nodes
\ met (performance scan, 2026-11-18): each refusal full, no block kept.
: grown ( n -- ) 0 ?do i 7 + lf-term-bvar must drop loop ;
dw-array-most grown
T{ lf-term-count @ dw-array-most > -> true }T
T{ ' mvinst-op refusing 0> swap ok? rot 99 firsts -> true true x }T

T{ depth -> 0 }T
cr .( meta-heap.fs: all tests passed) cr
bye

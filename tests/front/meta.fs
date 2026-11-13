\ Unit tests of the front end's Meta layer (plan FE1c; ADR 0021 D6): level
\ unification (src/front/level-defeq.fs, Lean's isLevelDefEqAux), every
\ answer and outcome, metavariable depth, assignments left and not left,
\ deep levels and full stores. Every T{ }T checks the data stack's depth.
\ tests/front/check_meta.py compares the same cases with pinned Lean.
\ Nothing here checks or accepts a theorem.
require ../support/tester.fs
require ../../src/main.fs
require ../../src/front/level-defeq.fs
require ../../src/front/instantiate.fs

lf-author-begin lf-mctx-reset
: lnew ( -- level ) lf-level-mvar-new ok? 0= abort" level mvar" ;
: lsucc ( level -- level' ) lf-level-succ 0= abort" succ" ;
: lsuccs ( level n -- level' ) 0 ?do lsucc loop ;
: lparam ( id -- level ) lf-level-param 0= abort" param" ;
: lmax ( a b -- level ) lf-level-max 0= abort" max" ;
: lval ( mvar -- value ) lf-level-mvar-value 0= abort" unassigned" ;
: lfree? ( mvar -- flag ) lf-level-mvar-value dup if nip then 0= ;
0 constant zero
zero lsucc constant one
one lsucc constant two
101 lparam constant u
102 lparam constant v

\ ---- Pass and fail, without metavariables (Lean: getLevelOffset ==, then
\ solve in both orders).
T{ u u lf-level-defeq -> true outcome-ok }T
T{ zero zero lf-level-defeq one one lf-level-defeq -> true outcome-ok true outcome-ok }T
T{ zero one lf-level-defeq one zero lf-level-defeq -> false outcome-ok false outcome-ok }T
T{ u v lf-level-defeq u zero lf-level-defeq zero u lf-level-defeq
   -> false outcome-ok false outcome-ok false outcome-ok }T
T{ u lsucc u lf-level-defeq u u 2 lsuccs lf-level-defeq
   -> false outcome-ok false outcome-ok }T
T{ u 3 lsuccs u 3 lsuccs lf-level-defeq -> true outcome-ok }T
\ Equal records made without sharing (the authoring context's setting).
T{ 101 lparam dup u = swap u lf-level-defeq -> false true outcome-ok }T

\ ---- Metavariables: assigned the other side.
lnew constant a
T{ a one lf-level-defeq a lval -> true outcome-ok one }T
\ ?a is now 1: the instantiated levels are compared.
T{ a one lf-level-defeq a two lf-level-defeq a lsucc two lf-level-defeq
   -> true outcome-ok false outcome-ok true outcome-ok }T
lnew constant bm
T{ two bm lsucc lf-level-defeq bm lval -> true outcome-ok one }T
\ ?c + 1 =?= ?d: solve (?c + 1) ?d is undef (Lean's rule for (_, ?v)
\ comes before decLevel?), then solve ?d (?c + 1) assigns ?d.
lnew constant c  lnew constant d
T{ c lsucc d lf-level-defeq -> true outcome-ok }T
T{ d lval ld-pred c lfree? -> c true }T
\ ?e =?= u + 2; ?f =?= ?f + 1 is false (the same base, Lean's first rule).
lnew constant e  lnew constant f
u 2 lsuccs constant u2
T{ e u2 lf-level-defeq e lval -> true outcome-ok u2 }T
T{ f f lsucc lf-level-defeq f lfree? -> false outcome-ok true }T
T{ f f lf-level-defeq -> true outcome-ok }T
\ u + 1 =?= ?g + 2 peels to u =?= ?g + 1: false, ?g left free.
lnew constant lg
T{ u lsucc lg 2 lsuccs lf-level-defeq lg lfree? -> false outcome-ok true }T
\ 0 =?= ?h: solve 0 ?h is undef, solve ?h 0 assigns.
lnew constant h
T{ zero h lf-level-defeq h lval -> true outcome-ok zero }T
\ succ u against a parameter is false; zero against a successor.
lnew constant li
T{ li lsucc v lf-level-defeq li lfree? -> false outcome-ok true }T
T{ zero li lsucc lf-level-defeq -> false outcome-ok }T

\ ---- Depth (Lean's isReadOnly and isMVarWithGreaterDepth). A level
\ metavariable made outside is read-only inside a deeper context.
lf-mctx-reset lnew constant lout
lf-mctx-deeper lnew constant inner
T{ lout one lf-level-defeq lout lfree? -> false outcome-ok true }T
\ Two metavariables: the deeper one is assigned the other.
T{ lout inner lf-level-defeq inner lval lout lfree? -> true outcome-ok lout true }T
\ Postponed by Lean (an assignable metavariable, both solves undef):
\ unsupported, nothing assigned.
lnew constant p
T{ p lsucc lout lf-level-defeq p lfree? -> false outcome-unsupported true }T
\ Neither side assignable: false.
lf-mctx-shallower lnew lf-mctx-deeper constant q
T{ lout lsucc q lf-level-defeq q lfree? -> false outcome-ok true }T
\ At depth 0 ?q is free: ?q := ?lout + 1.
lf-mctx-shallower
T{ lout lsucc q lf-level-defeq q lval ld-pred lout lfree? -> true outcome-ok lout true }T
\ Back at depth 0, ?o =?= ?d with ?d made at depth 1: Lean assigns the
\ deeper one, ?d := ?o (isMVarWithGreaterDepth), not ?o := ?d.
lnew constant o  lf-mctx-deeper lnew constant dp  lf-mctx-shallower
T{ o dp lf-level-defeq dp lval o lfree? -> true outcome-ok o true }T

\ ---- Not ported: max and imax (Lean normalizes them first).
lf-mctx-reset lnew constant m
T{ u v lmax u v lmax lf-level-defeq -> true outcome-ok }T
T{ u v lmax v u lmax lf-level-defeq -> false outcome-unsupported }T
T{ m u v lmax lf-level-defeq m lfree? -> false outcome-unsupported true }T
T{ u zero lf-level-imax drop one lf-level-defeq -> false outcome-unsupported }T
\ A metavariable assigned a max is instantiated, then unsupported.
lnew constant ln
T{ ln u v lmax lf-level-mvar-assign ln u lf-level-defeq
   -> outcome-ok false outcome-unsupported }T

\ ---- Malformed: a level not in the store, a stale metavariable.
T{ 99999 u lf-level-defeq u -1 lf-level-defeq
   -> false outcome-invalid false outcome-invalid }T
lnew constant old
T{ lf-mctx-reset old one lf-level-defeq -> false outcome-invalid }T
T{ one old lsucc lf-level-defeq -> false outcome-invalid }T

\ ---- Resources: 10,000 successors are peeled and counted in loops.
lf-mctx-reset 100000 lf-level-capacity! drop
u 10000 lsuccs constant tall
T{ tall u 10000 lsuccs lf-level-defeq tall u 9999 lsuccs lf-level-defeq
   -> true outcome-ok false outcome-ok }T
lnew constant w
T{ w 10000 lsuccs tall lf-level-defeq w lval -> true outcome-ok u }T
\ ?x + 10000 with ?x := 1 is instantiated (a new level) and compared.
lnew constant lx
T{ lx one lf-level-mvar-assign lx 10000 lsuccs zero 10001 lsuccs lf-level-defeq
   -> outcome-ok true outcome-ok }T

\ ---- Instantiation of bound variables (src/front/instantiate.fs, Lean's
\ instantiate1 and headBeta).
lf-mctx-reset lf-lctx-reset
: app ( f a -- t ) lf-term-app 0= abort" app" ;
: lam ( type body -- t ) lf-term-lam 0= abort" lam" ;
: tpi ( type body -- t ) lf-term-pi 0= abort" pi" ;
: bv ( i -- t ) lf-term-bvar 0= abort" bvar" ;
: inst ( body value -- term ) lf-meta-instantiate1 ok? 0= abort" inst" ;
: fvar ( type -- fvar ) lf-lctx-local ok? 0= abort" fvar" ;
: parts ( t -- first second ) dup lf-term-first@ swap lf-term-second@ ;
: tag ( t -- tag ) lf-term-tag@ ;
0 lf-term-sort drop constant prop
prop fvar constant x
prop fvar constant y
\ #0 becomes the value, #1 one less; under a binder #1 is the value.
T{ 0 bv x inst 1 bv x inst dup tag swap lf-term-first@ -> x lf-tag-bvar 0 }T
T{ prop 1 bv lam x inst dup tag swap parts -> lf-tag-lam prop x }T
T{ prop 1 bv tpi x inst parts -> prop x }T
\ #0 under a binder is bound there: the term is kept, the same node.
prop 0 bv lam constant id-fun
T{ id-fun x inst id-fun = prop x inst prop = -> true true }T
\ Both uses of a shared child become the value (made once).
0 bv dup app constant dup0
T{ dup0 x inst parts -> x x }T
\ A rebuilt binder keeps its name and kind.
prop 1 bv lam constant named
T{ named 0 s" z" lf-name-str drop lf-binder-implicit lf-pres-binder! -> outcome-ok }T
T{ named x inst lf-pres-binder@ drop nip -> lf-binder-implicit }T
\ Loose indices above the value: #2 under one binder becomes #1.
T{ prop 2 bv lam x inst lf-term-second@ dup tag swap lf-term-first@ -> lf-tag-bvar 1 }T
\ A value with a loose bound variable: unsupported (Lean lifts it); a
\ value holding a metavariable is closed (its range by a walk).
T{ 0 bv 0 bv lf-meta-instantiate1 -> -1 outcome-unsupported }T
T{ 0 bv x 0 bv app lf-meta-instantiate1 -> -1 outcome-unsupported }T
prop mv-natural lf-mvar-new drop constant hole
T{ hole x app lf-meta-loose x 1 bv app lf-meta-loose -> 0 outcome-ok 2 outcome-ok }T
T{ 0 bv hole x app inst parts -> hole x }T
T{ prop hole 1 bv app lam lf-meta-loose -> 1 outcome-ok }T
\ Malformed: a term or value that is not in the store.
T{ 99999 x lf-meta-instantiate1 x -1 lf-meta-instantiate1 -> -1 outcome-invalid -1 outcome-invalid }T
T{ 99999 lf-meta-loose 99999 lf-meta-head-beta -> -1 outcome-invalid -1 outcome-invalid }T

\ Head beta: (fun a => a) x is x; (fun a b => b a) x y is y x; extra
\ arguments are applied; a head that is no lambda keeps the term.
T{ id-fun x app lf-meta-head-beta -> x outcome-ok }T
prop prop 0 bv 1 bv app lam lam constant flip
T{ flip x app y app lf-meta-head-beta swap parts -> outcome-ok y x }T
T{ id-fun x app y app lf-meta-head-beta swap parts -> outcome-ok x y }T
T{ x y app dup lf-meta-head-beta drop = prop lf-meta-head-beta -> true prop outcome-ok }T
\ Fewer arguments than lambdas: a lambda is left.
T{ flip x app lf-meta-head-beta swap dup tag swap lf-term-second@ parts
   swap lf-term-first@ swap -> outcome-ok lf-tag-lam 0 x }T
\ One step only, as Lean: (fun a => a) (fun b => b) x is (fun b => b) x.
T{ id-fun id-fun app x app lf-meta-head-beta swap parts -> outcome-ok id-fun x }T

\ ---- Abstraction (Lean's Expr.abstract): x y become #1 #0 in order; under
\ a binder one more; the last of two equal entries wins; a metavariable
\ is abstracted too; a term without them is kept, the same node.
100000 lf-term-capacity! drop
create xs 4 cells allot
: xs1 ( a -- addr 1 ) xs ! xs 1 ;
: xs2 ( a b -- addr 2 ) xs cell+ ! xs ! xs 2 ;
: abst ( term addr n -- term' ) lf-meta-abstract ok? 0= abort" abst" ;
: bvar# ( t -- i ) dup tag lf-tag-bvar <> abort" no bvar" lf-term-first@ ;
x y app constant fxy0
T{ fxy0 x xs1 abst parts swap bvar# -> y 0 }T
T{ fxy0 x y xs2 abst parts bvar# swap bvar# -> 0 1 }T
T{ fxy0 y x xs2 abst parts bvar# swap bvar# -> 1 0 }T
T{ fxy0 x x xs2 abst parts swap bvar# -> y 0 }T
T{ prop x 0 bv app lam x xs1 abst lf-term-second@ parts bvar# swap bvar# -> 0 1 }T
T{ hole x app hole xs1 abst parts swap bvar# -> x 0 }T
T{ prop 3 bv lam dup x xs1 abst = fxy0 dup 0 0 abst = -> true true }T
\ Abstract then instantiate1 gives the term back (Lean's replaceFVar).
T{ fxy0 x xs1 abst y inst parts -> y y }T
\ Malformed: a negative count, a term not in the store.
T{ fxy0 xs -1 lf-meta-abstract 99999 x xs1 lf-meta-abstract
   -> -1 outcome-invalid -1 outcome-invalid }T

\ ---- Resources: 10,000 binders deep, and 10,000 applications deep, on the
\ heap stacks; a DAG of 2^40 paths in time of its size.
100000 lf-term-capacity! drop
: lams ( body n -- t ) 0 ?do prop swap lam loop ;
: apps ( t n -- t' ) 0 ?do prop app loop ;
10000 bv 10000 lams constant deep-lams
: seconds ( t n -- t' ) 0 ?do lf-term-second@ loop ;
T{ deep-lams x inst 10000 seconds -> x }T
0 bv 10000 apps constant deep-apps
: firsts ( t n -- t' ) 0 ?do lf-term-first@ loop ;
T{ deep-apps x inst 10000 firsts -> x }T
: doubling ( t n -- t' ) 0 ?do dup app loop ;
0 bv 40 doubling constant wide
T{ wide x inst 40 firsts -> x }T
x 10000 lams constant xdeep
T{ xdeep x xs1 abst 10000 seconds bvar# -> 10000 }T
\ Full: no room for one more term.
lf-term-capacity constant term-room
flip x app y app constant fxy
T{ lf-term-count @ lf-term-capacity! -> outcome-ok }T
T{ dup0 y lf-meta-instantiate1 fxy lf-meta-head-beta -> -1 outcome-full -1 outcome-full }T
T{ fxy0 x xs1 lf-meta-abstract -> -1 outcome-full }T
T{ term-room lf-term-capacity! dup0 y lf-meta-instantiate1 nip -> outcome-ok outcome-ok }T

T{ depth -> 0 }T
cr .( meta.fs: all tests passed) cr
bye

\ Unit tests of the front end's Meta layer (plan FE1c; ADR 0021 D6): level
\ unification (src/front/level-defeq.fs, Lean's isLevelDefEqAux), every
\ answer and outcome, metavariable depth, assignments left and not left
\ (also when the mark's close is refused), deep levels and full stores. Every T{ }T checks the data stack's depth.
\ tests/front/check_meta.py compares the same cases with pinned Lean.
\ Nothing here checks or accepts a theorem.
require ../support/tester.fs
require ../../src/main.fs
require ../../src/front/level-defeq.fs
require ../../src/front/instantiate.fs
require ../../src/front/level-params.fs
require ./depth.fs

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
0 s" u" lf-name-str drop constant u-id  0 s" v" lf-name-str drop constant v-id
u-id lparam constant u
v-id lparam constant v

\ ---- Pass and fail, without metavariables (Lean: getLevelOffset ==, then
\ solve in both orders).
T{ u u lf-meta-level-defeq -> true outcome-ok }T
T{ zero zero lf-meta-level-defeq one one lf-meta-level-defeq
   -> true outcome-ok true outcome-ok }T
T{ zero one lf-meta-level-defeq one zero lf-meta-level-defeq
   -> false outcome-ok false outcome-ok }T
T{ u v lf-meta-level-defeq u zero lf-meta-level-defeq zero u lf-meta-level-defeq
   -> false outcome-ok false outcome-ok false outcome-ok }T
T{ u lsucc u lf-meta-level-defeq u u 2 lsuccs lf-meta-level-defeq
   -> false outcome-ok false outcome-ok }T
T{ u 3 lsuccs u 3 lsuccs lf-meta-level-defeq -> true outcome-ok }T
\ succ u against zero: solve gives undef (decLevel? 0 has none), then
\ solve 0 (succ u) false.
T{ u lsucc zero lf-meta-level-defeq -> false outcome-ok }T
\ Equal records made without sharing (the authoring context's setting).
T{ u-id lparam dup u = swap u lf-meta-level-defeq -> false true outcome-ok }T

\ ---- Metavariables: assigned the other side.
lnew constant a
T{ a one lf-meta-level-defeq a lval -> true outcome-ok one }T
\ ?a is now 1: the instantiated levels are compared.
T{ a one lf-meta-level-defeq a two lf-meta-level-defeq a lsucc two lf-meta-level-defeq
   -> true outcome-ok false outcome-ok true outcome-ok }T
lnew constant bm
T{ two bm lsucc lf-meta-level-defeq bm lval -> true outcome-ok one }T
\ ?c + 1 =?= ?d: solve (?c + 1) ?d is undef (Lean's rule for (_, ?v)
\ comes before decLevel?), then solve ?d (?c + 1) assigns ?d.
lnew constant c  lnew constant d
T{ c lsucc d lf-meta-level-defeq -> true outcome-ok }T
T{ d lval ld-pred c lfree? -> c true }T
\ ?e =?= u + 2; ?f =?= ?f + 1 is false (the same base, Lean's first rule).
lnew constant e  lnew constant f
u 2 lsuccs constant u2
T{ e u2 lf-meta-level-defeq e lval -> true outcome-ok u2 }T
T{ f f lsucc lf-meta-level-defeq f lfree? -> false outcome-ok true }T
T{ f f lf-meta-level-defeq -> true outcome-ok }T
\ u + 1 =?= ?g + 2 peels to u =?= ?g + 1: false, ?g left free.
lnew constant lg
T{ u lsucc lg 2 lsuccs lf-meta-level-defeq lg lfree? -> false outcome-ok true }T
\ 0 =?= ?h: solve 0 ?h is undef, solve ?h 0 assigns.
lnew constant h
T{ zero h lf-meta-level-defeq h lval -> true outcome-ok zero }T
\ succ u against a parameter is false; zero against a successor.
lnew constant li
T{ li lsucc v lf-meta-level-defeq li lfree? -> false outcome-ok true }T
T{ zero li lsucc lf-meta-level-defeq -> false outcome-ok }T

\ ---- Depth (Lean's isReadOnly and isMVarWithGreaterDepth). A level
\ metavariable made outside is read-only inside a deeper context.
lf-mctx-reset lnew constant lout
deeper lnew constant inner
T{ lout one lf-meta-level-defeq lout lfree? -> false outcome-ok true }T
\ Two metavariables: the deeper one is assigned the other.
T{ lout inner lf-meta-level-defeq inner lval lout lfree? -> true outcome-ok lout true }T
\ Postponed by Lean (an assignable metavariable, both solves undef):
\ unsupported, nothing assigned.
lnew constant p
T{ p lsucc lout lf-meta-level-defeq p lfree? -> false outcome-unsupported true }T
\ Neither side assignable: false.
shallower lnew deeper constant q
T{ lout lsucc q lf-meta-level-defeq q lfree? -> false outcome-ok true }T
\ At depth 0 ?q is free: ?q := ?lout + 1.
shallower
T{ lout lsucc q lf-meta-level-defeq q lval ld-pred lout lfree?
   -> true outcome-ok lout true }T
\ Back at depth 0, ?o =?= ?d with ?d made at depth 1: Lean assigns the
\ deeper one, ?d := ?o (isMVarWithGreaterDepth), not ?o := ?d.
lnew constant lo  deeper lnew constant ldp  shallower
T{ lo ldp lf-meta-level-defeq ldp lval lo lfree? -> true outcome-ok lo true }T

\ ---- max and imax: both sides normalized first (Level.normalize), so
\ max v u is max u v; ?m is assigned the normal form; imax u 0 is 0.
\ (These four were unsupported before Level.normalize was ported.)
lf-mctx-reset 100000 lf-level-capacity! drop lnew constant m
: parts2 ( l -- a b ) dup lf-level-first@ swap lf-level-second@ ;
T{ u v lmax u v lmax lf-meta-level-defeq -> true outcome-ok }T
T{ u v lmax v u lmax lf-meta-level-defeq -> true outcome-ok }T
T{ m v u lmax lf-meta-level-defeq m lval parts2 -> true outcome-ok u v }T
T{ u zero lf-level-imax drop one lf-meta-level-defeq -> false outcome-ok }T
\ A metavariable assigned a max is instantiated: max u v =?= u is false.
lnew constant ln
T{ ln u v lmax lf-level-mvar-assign ln u lf-meta-level-defeq
   -> outcome-ok false outcome-ok }T
\ 0 =?= max ?a ?b: both parts, ?a := 0 and ?b := 0. 0 =?= max ?c (?f+1)
\ (sorted ?c first): ?c := 0, then 0 =?= ?f+1 is false and ?c's
\ assignment is rolled back (checkpointDefEq); 0 =?= max ?c u compares u
\ first (a parameter sorts before a metavariable): false at once.
\ 0 =?= imax u ?d: ?d := 0.
lnew constant ma  lnew constant mb  lnew constant mc  lnew constant md  lnew constant mf
T{ zero ma mb lmax lf-meta-level-defeq ma lval mb lval -> true outcome-ok zero zero }T
T{ zero mc mf lsucc lmax lf-meta-level-defeq mc lfree? mf lfree? -> false outcome-ok true true }T
T{ zero mc u lmax lf-meta-level-defeq mc lfree? -> false outcome-ok true }T
T{ zero u md lf-level-imax drop lf-meta-level-defeq md lval -> true outcome-ok zero }T
\ Not ported: ?m =?= max ?m u (Lean's solveSelfMax) and succ ?m against a
\ max (decLevel?): unsupported, nothing assigned. A stuck pair with an
\ assignable metavariable inside a max: unsupported (Lean postpones);
\ with none (?r read-only): false.
lnew constant me
T{ me me u lmax lf-meta-level-defeq me lfree? -> false outcome-unsupported true }T
\ ?e =?= imax u ?e: ?e occurs in a level that is no max: undef both ways,
\ then postponed (unsupported).
T{ me u me lf-level-imax drop lf-meta-level-defeq me lfree? -> false outcome-unsupported true }T
T{ me lsucc u lsucc v lsucc lmax lf-meta-level-defeq me lfree?
   -> false outcome-unsupported true }T
T{ u me lmax u v lmax lf-meta-level-defeq -> false outcome-unsupported }T
deeper
T{ u me lmax u v lmax lf-meta-level-defeq -> false outcome-ok }T
shallower
\ A stale metavariable inside a max: invalid.
lnew constant mold
lf-mctx-reset
T{ u mold lmax u lf-meta-level-defeq -> false outcome-invalid }T
\ No answer leaves its mark open (review of fe1c-lnorm-2, T2): true,
\ false, unsupported, invalid.
lnew constant mk
T{ mk one lf-meta-level-defeq lf-mctx-marks u v lf-meta-level-defeq lf-mctx-marks
   -> true outcome-ok 0 false outcome-ok 0 }T
T{ u lnew lmax u v lmax lf-meta-level-defeq lf-mctx-marks 99999 u lf-meta-level-defeq lf-mctx-marks
   -> false outcome-unsupported 0 false outcome-invalid 0 }T
\ The close refused (ld-close, white-box; coverage COVFU): through
\ lf-meta-level-defeq its mark is always the latest open one, so no input
\ reaches this. A refused commit or rollback (no mark open, or an outer
\ mark while an inner is open) is the answer: false with the refusal's
\ outcome, invalid, whatever the rounds gave; nothing changes. The latest
\ mark then closes as usual: commit keeps, rollback undoes.
: open-mark ( -- mark ) lf-mctx-mark ok? 0= abort" mark" ;
T{ true outcome-ok 0 ld-close false outcome-unsupported 0 ld-close lf-mctx-marks
   -> false outcome-invalid false outcome-invalid 0 }T
lnew constant lkept
open-mark constant outer-mark  open-mark constant inner-mark
T{ lkept one lf-level-mvar-assign true outcome-ok outer-mark ld-close
   lf-mctx-marks lkept lval -> outcome-ok false outcome-invalid 2 one }T
T{ true outcome-ok inner-mark ld-close false outcome-ok outer-mark ld-close
   lf-mctx-marks lkept lfree? -> true outcome-ok false outcome-ok 0 true }T

\ ---- Malformed: a level not in the store, a stale metavariable.
T{ 99999 u lf-meta-level-defeq u -1 lf-meta-level-defeq
   -> false outcome-invalid false outcome-invalid }T
lnew constant old
T{ lf-mctx-reset old one lf-meta-level-defeq -> false outcome-invalid }T
T{ one old lsucc lf-meta-level-defeq -> false outcome-invalid }T

\ ---- Resources: 10,000 successors are peeled and counted in loops.
lf-mctx-reset 100000 lf-level-capacity! drop
u 10000 lsuccs constant tall
T{ tall u 10000 lsuccs lf-meta-level-defeq tall u 9999 lsuccs lf-meta-level-defeq
   -> true outcome-ok false outcome-ok }T
lnew constant w
T{ w 10000 lsuccs tall lf-meta-level-defeq w lval -> true outcome-ok u }T
\ ?x + 10000 with ?x := 1 is instantiated (a new level) and compared.
lnew constant lx
T{ lx one lf-level-mvar-assign lx 10000 lsuccs zero 10001 lsuccs lf-meta-level-defeq
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

\ ---- Universe parameters (src/front/level-params.fs, Lean's
\ Level.instantiateParams and Expr.instantiateLevelParams).
lf-mctx-reset
create ps 2 cells allot  u-id ps !  v-id ps cell+ !
create ls 2 cells allot
: ls! ( a b -- ) ls cell+ ! ls ! ;
: lps ( level n -- level' outcome ) >r ps ls r> lf-meta-level-params ;
one two ls!
\ u + 1 becomes 1 + 1; v with only u named stays; no parameter stays.
T{ u lsucc 1 lps swap ld-pred -> outcome-ok one }T
T{ v 1 lps two 2 lps -> v outcome-ok two outcome-ok }T
T{ v 2 lps -> two outcome-ok }T
\ The first equal name wins (getParamSubst): u u -> 1 2.
T{ u-id ps cell+ ! u 2 lps v-id ps cell+ ! -> one outcome-ok }T
\ max over parameters: rebuilt with mkLevelMax' (max 1 2 is 2); a max
\ without one is kept as it is.
: same-under ( a b c -- flag c ) >r = r> ;
T{ u v lmax 2 lps one zero lmax dup 2 lps same-under -> two outcome-ok true outcome-ok }T
\ A max whose parts stay is simplified in place (simpLevelMax'): the
\ same node when no rule applies; so is a successor whose part stays.
T{ u v lmax dup 0 lps drop = u lsucc dup 0 lps drop = -> true true }T
\ max u 1 with u := 1: 1 (1 has no parameter and is kept; equal sides).
T{ u one lmax 1 lps -> one outcome-ok }T
\ imax u v: with v := 0, 0 (mkLevelIMax' v zero); with only u := 1, imax 1 v.
create ls0 2 cells allot  one ls0 !  zero ls0 cell+ !
T{ u v lf-level-imax drop ps ls0 2 lf-meta-level-params -> zero outcome-ok }T
T{ u v lf-level-imax drop 1 lps swap dup ls-tag swap lf-level-first@
   -> outcome-ok lf-level-tag-imax one }T
\ max u v with only u named: max 1 v, a new max (no rule applies).
T{ u v lmax 1 lps swap dup ls-tag swap lf-level-second@ -> outcome-ok lf-level-tag-max v }T
\ Malformed: a negative count, a level not in the store.
T{ u ps ls -1 lf-meta-level-params 99999 1 lps -> -1 outcome-invalid -1 outcome-invalid }T
\ Terms: Sort u and C.{u, v} take the levels; a binder keeps its name.
: sort-of ( level -- term ) dup lf-level-identity drop lf-hterm-sort 0= abort" sort" drop ;
create cpairs 4 cells allot
: cpair! ( level i -- ) 2* cells cpairs + >r dup lf-level-identity drop swap r> 2! ;
: const2 ( l1 l2 -- term )
  1 cpair! 0 cpair! 0 s" C" lf-name-str drop lf-name-generation @ cpairs 2 lf-cref-new
  0= abort" cref" lf-cterm-new 0= abort" cterm" drop ;
: clevel ( term i -- level ) >r lf-term-first@ lf-cref-slot lf-cref-pairs drop r> lf-cref-pair@ drop ;
: ilp ( term n -- term' outcome ) >r ps ls r> lf-meta-instantiate-level-params ;
lnew constant la
one la ls!
T{ u sort-of 2 ilp swap lf-term-first@ -> outcome-ok one }T
u v const2 constant cuv
T{ cuv 2 ilp drop dup 0 clevel swap 1 clevel -> one la }T
T{ cuv 1 ilp drop dup 0 clevel swap 1 clevel -> one v }T
u sort-of dup lam constant su-lam
T{ su-lam 0 s" w" lf-name-str drop lf-binder-implicit lf-pres-binder! -> outcome-ok }T
T{ su-lam 2 ilp drop parts lf-term-first@ swap lf-term-first@ -> one one }T
T{ su-lam 2 ilp drop lf-pres-binder@ drop nip -> lf-binder-implicit }T
\ Nothing to change: the same node; a count of 0 changes nothing.
T{ prop x app dup 2 ilp drop = cuv dup 0 ilp drop = -> true true }T
T{ u sort-of dup 0 ilp drop = -> true }T
\ No names: Sort (max u u) is kept as it is (Lean's empty-list test), but
\ the Level version simplifies it (Lean has no such test there).
T{ u u lmax sort-of dup 0 ilp drop = u u lmax 0 lps -> true u outcome-ok }T
\ A Sort over max u v (with u := 1, v := ?la): Sort (max 1 ?la).
T{ u v lmax sort-of 2 ilp drop lf-term-first@ dup ls-tag swap lf-level-second@
   -> lf-level-tag-max la }T

\ The shared rebuild of a Sort or constant (src/front/level-map.fs): an
\ image that keeps every level keeps the node; one taking u to 1
\ rebuilds it.
: keep-level ( level -- level ) ;
: u-to-one ( level -- level' ) dup u = if drop one then ;
T{ u sort-of dup ' keep-level lf-meta-sort-remap drop = -> true }T
T{ u sort-of ' u-to-one lf-meta-sort-remap swap lf-term-first@ -> outcome-ok one }T
T{ cuv dup ' keep-level lf-meta-const-remap drop = -> true }T
T{ cuv ' u-to-one lf-meta-const-remap swap dup 0 clevel swap 1 clevel -> outcome-ok one v }T

\ ---- Level equality and Lean's cheap simplifications (src/front/
\ level-simp.fs: Level.beq, isNeverZero, mkLevelMax', mkLevelIMax').
: l= ( a b -- flag ) lf-meta-level= ok? 0= abort" l=" ;
: nz? ( l -- flag ) lf-meta-never-zero? ok? 0= abort" nz" ;
: lmx ( a b -- l ) lf-meta-max ok? 0= abort" lmx" ;
: limx ( a b -- l ) lf-meta-imax ok? 0= abort" limx" ;
: limax ( a b -- l ) lf-level-imax 0= abort" imax" ;
\ Equality by structure: equal levels made twice, and unequal ones.
T{ u lsucc v lmax u lsucc v lmax l= u lsucc v lmax v lsucc u lmax l= -> true false }T
T{ u 3 lsuccs u 3 lsuccs l= u 3 lsuccs u 2 lsuccs l= u v l= -> true false false }T
T{ u v limax u v lmax l= one one l= -> false true }T
\ isNeverZero: a successor, or one through max or imax's second side.
T{ one nz? u nz? zero nz? u one lmax nz? -> true false false true }T
T{ one u limax nz? u one limax nz? -> false true }T
\ mkLevelMax': u u is u; a zero side gives the other; an explicit level
\ below the other's offset is subsumed (max 1 2 is 2, max (u+2) 1 is
\ u+2); an argument of a max is subsumed; the same base keeps the larger
\ offset; else a new max.
T{ u u lmx zero u lmx u zero lmx -> u u u }T
T{ one two lmx u 2 lsuccs dup one lmx = -> two true }T
\ At an equal offset the explicit side is subsumed too: max (u+1) 1 and
\ max 1 (u+1) are u+1.
T{ u lsucc dup one lmx = u lsucc dup one swap lmx = -> true true }T
T{ u v lmax dup u lmx = u v lmax dup v swap lmx = -> true true }T
T{ u lsucc dup u lmx = u dup lsucc lmx ld-pred -> true u }T
T{ u v lmx dup ls-tag swap lf-level-first@ -> lf-level-tag-max u }T
\ mkLevelIMax': v never zero gives the max; v zero gives v; u zero gives
\ v; u u is u; else a new imax.
T{ u one limx dup ls-tag swap lf-level-second@ -> lf-level-tag-max one }T
T{ u zero limx zero u limx u u limx -> zero u u }T
T{ u v limx ls-tag -> lf-level-tag-imax }T
\ The simp forms give d where a new node would be made.
T{ u zero 7 lm-simp-imax -> zero outcome-ok }T
T{ u v 7 lm-simp-max u v 7 lm-simp-imax one two 7 lm-simp-max
   -> 7 outcome-ok 7 outcome-ok two outcome-ok }T
\ Deep: equality and isNeverZero over 10,000 successors in loops.
T{ u 10000 lsuccs u 10000 lsuccs l= zero 10000 lsuccs v lmax nz? -> true true }T
T{ cuv ps ls -1 lf-meta-instantiate-level-params 99999 2 ilp
   -> -1 outcome-invalid -1 outcome-invalid }T
\ Deep: 10,000 applications over Sort u; full: no room for a term.
u sort-of 10000 apps constant su-deep
T{ su-deep 2 ilp drop 10000 firsts lf-term-first@ -> one }T
lf-term-capacity constant room2
T{ lf-term-count @ lf-term-capacity! su-lam 2 ilp -> outcome-ok -1 outcome-full }T
T{ room2 lf-term-capacity! -> outcome-ok }T

200000 lf-level-capacity! drop
\ ---- Level.normalize (src/front/level-normalize.fs); check_meta.py
\ compares 44 cases with pinned Lean.
: nf ( l -- l' ) lf-meta-level-normalize ok? 0= abort" nf" ;
\ Kept, the same node: a level over zero, a parameter or a metavariable.
T{ u 3 lsuccs dup nf = zero dup nf = -> true true }T
\ Sorted by name, a duplicate and a subsumed explicit level dropped, the
\ offset pushed into a max but kept over an imax that is never zero.
T{ v u lmax nf u v lmax l= u u lmax nf u l= u lsucc one lmax nf u lsucc l= -> true true true }T
T{ u v lmax lsucc nf u lsucc v lsucc lmax l= -> true }T
T{ u v lsucc limax 2 lsuccs nf u v lsucc lmax 2 lsuccs l= -> true }T
\ imax: zero for a zero right side, the right side for a left side 1.
T{ u zero limax nf one v limax nf -> zero v }T
\ mkIMaxAux's other rules: imax 0 u is u; imax u u is u; else an imax.
T{ zero u limax nf u u limax nf u v limax nf ls-tag -> u u lf-level-tag-imax }T
\ normLt on two imax bases: by their first sides, then by their second
\ when the first are equal; equal bases by offset.
lnew constant mz
T{ u mz limax u v limax lmax nf u v limax u mz limax lmax l= -> true }T
T{ v u limax u v limax lmax nf u v limax v u limax lmax l= -> true }T
T{ u v limax lsucc u v limax lmax nf u v limax lsucc l= -> true }T
\ Zero against zero inside a max: max 0 0 is 0.
T{ zero zero lmax nf -> zero }T
\ Lean's Name.cmp: by prefixes first (w before u.v), a number before a
\ string (u.1 before z), then by bytes.
: nm ( prefix c-addr u -- id ) lf-name-str 0= abort" name" ;
0 s" w" nm constant w-id  u-id s" v" nm constant uv-id  0 s" z" nm constant z-id
T{ u-id v-id lf-meta-name-cmp v-id u-id lf-meta-name-cmp u-id u-id lf-meta-name-cmp
   -> -1 1 0 }T
T{ w-id uv-id lf-meta-name-cmp uv-id w-id lf-meta-name-cmp -> -1 1 }T
T{ u-id 2 lf-name-num drop u-id 1 lf-name-num drop lf-meta-name-cmp -> 1 }T
T{ u-id 1 lf-name-num drop u-id 2 lf-name-num drop lf-meta-name-cmp -> -1 }T
\ Equal last parts: the prefixes decide (a.1 before b.1).
T{ 0 s" a" nm 1 lf-name-num drop 0 s" b" nm 1 lf-name-num drop lf-meta-name-cmp -> -1 }T
T{ u-id 1 lf-name-num drop z-id lf-meta-name-cmp 0 s" ab" nm 0 s" abc" nm lf-meta-name-cmp
   -> -1 -1 }T
\ Malformed: a level not in the store; a parameter whose name is no name.
T{ 99999 lf-meta-level-normalize 999999 lparam v lmax lf-meta-level-normalize
   -> -1 outcome-invalid -1 outcome-invalid }T
\ Deep and wide: 10,000 successors over a max; a max of 200 metavariables
\ made newest first, sorted oldest first (idempotent, the newest last).
\ Each inner max of the chain gets its own normal form: about n^2 / 2 new
\ levels.
T{ v u lmax 10000 lsuccs nf lf-level-second@ ld-offset -> v 10000 }T
variable newest
: wide-max ( n -- l ) lnew swap 1 ?do lnew dup newest ! swap lmax loop ;
lf-mctx-reset 200 wide-max nf constant w200
T{ w200 dup nf l= w200 lf-level-second@ newest @ = -> true true }T
\ Full: no room for the normal form.
lf-level-capacity constant level-room
v u lmax constant vu
T{ lf-level-count @ lf-level-capacity! vu lf-meta-level-normalize -> outcome-ok -1 outcome-full }T
T{ level-room lf-level-capacity! vu lf-meta-level-normalize nip -> outcome-ok outcome-ok }T

T{ depth -> 0 }T
cr .( meta.fs: all tests passed) cr
bye

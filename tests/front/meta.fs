\ Unit tests of the front end's Meta layer (plan FE1c; ADR 0021 D6): level
\ unification (src/front/level-defeq.fs, Lean's isLevelDefEqAux), every
\ answer and outcome, metavariable depth, assignments left and not left,
\ deep levels and full stores. Every T{ }T checks the data stack's depth.
\ tests/front/check_meta.py compares the same cases with pinned Lean.
\ Nothing here checks or accepts a theorem.
require ../support/tester.fs
require ../../src/main.fs
require ../../src/front/level-defeq.fs

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
lnew constant x
T{ x one lf-level-mvar-assign x 10000 lsuccs zero 10001 lsuccs lf-level-defeq
   -> outcome-ok true outcome-ok }T

T{ depth -> 0 }T
cr .( meta.fs: all tests passed) cr
bye

\ Unit tests of the goal layer's exfalso (plan row TB1; src/front/
\ meta-tactic/goal.fs's lf-goal-exfalso, Lean's MVarId.exfalso), over the
\ S2 slice in an authoring run, by the classes of docs/development/
\ TEST_COVERAGE_REVIEW.md: 1. outcomes: a goal of a proposition (Sort 0),
\ of a type (Sort 1) and of a type in Sort u (a universe parameter): the
\ new goal is synthetic opaque, of type False, in the goal's context, with
\ the goal's tag; the goal is assigned @False.elim.{u} target goal', u the
\ target's level; 2. malformed input: an assigned goal (a fault, invalid);
\ 3. stack effects (each T{ }T checks the depth); 7. regression pins: the
\ term's head, level and arguments.
\ Nothing here accepts a theorem: only the kernel's check does.
require ../../../support/tester.fs
require ../../../../src/main.fs
decimal

4000000 lf-term-capacity! drop  100000 lf-cref-capacity! drop
T{ s" tests/front/s2-slice.ndjson" true lfc-library-open -> outcome-ok }T
T{ s" tests/front/s2-slice.elab.ndjson" lfc-elab-file! lfc-elab-read lfc-rooms
   -> outcome-ok outcome-ok }T
lf-author-begin
: made ( x outcome -- x ) ok? 0= abort" exfalso test: not made" ;
: nat ( -- t ) s" Nat" lf-mk-const0 ;
: binder ( type c-addr u -- fvar )
  lfa-intern swap lf-lctx-local made tuck swap 0 lf-local-new made
  lf-mctx-view swap lf-view-push made lf-mctx-view! ;
: goal ( type -- goal ) 0 lf-mctx-view lf-goal-new made ;
: code1 ( x xt -- code ) catch dup if nip then ;
nat s" a" binder constant fa
nat s" b" binder constant fb
\ A goal of type, tagged left; exfalso of it.
: tagged ( type -- goal ) goal dup s" left" lfa-intern lf-mvar-tag! made ;
: exf ( type -- goal goal' ) tagged dup lf-goal-exfalso ;
\ The new goal: False, synthetic opaque, the goal's tag and context.
: false? ( t -- flag ) s" False" lf-mk-const0 lf-meta-eqv made ;
: like? ( goal goal' -- flag )
  2dup lf-goal-tag swap lf-goal-tag = >r lf-goal-view swap lf-goal-view = r> and ;
: new-ok? ( goal goal' -- flag )
  dup lf-goal-type false? over lf-goal-kind mv-opaque = and >r like? r> and ;
\ The goal's value: False.elim.{u} target goal'.
: assigned ( goal -- e ) lf-instantiate! ;
: elim-level ( goal -- u ) assigned lf-meta-head 0 lf-const-level@ ;
: elim-args ( goal -- target goal' ) assigned lf-meta-args2 ;
: elim? ( goal -- flag ) assigned lf-meta-head s" False.elim" lf-meta-const-named? ;
: zero? ( u -- flag ) lf-level-tag@ lf-level-tag-zero = ;
: one? ( u -- flag ) dup lf-level-tag@ lf-level-tag-succ = swap lf-level-first@ zero? and ;

\ Sort 0: a = b.
fa fb lf-mk-eq constant eq-ab
eq-ab exf constant g0' constant g0
T{ g0 g0' new-ok? g0 elim? g0 elim-level zero? -> true true true }T
T{ g0 elim-args g0' = swap eq-ab = -> true true }T
\ Sort 1: Nat.
nat exf constant g1' constant g1
T{ g1 g1' new-ok? g1 elim? g1 elim-level one? -> true true true }T
\ Sort u: α : Sort u, the goal α.
s" u" lfa-intern lf-level-param drop constant u
u lf-term-symbolic-sort lf-made! s" α" binder constant fα
fα exf constant gu' constant gu
T{ gu gu' new-ok? gu elim? gu elim-level u = gu elim-args drop fα = -> true true true true }T
\ An assigned goal is a fault (checkNotAssigned): invalid.
T{ eq-ab goal dup fa lf-mvar-assign made ' lf-goal-exfalso code1 -> -4201 }T
.( exfalso test.fs: all tests passed) cr
bye

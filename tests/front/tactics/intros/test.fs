\ Unit tests of the goal layer's intros and introN (plan row TB1; src/front/
\ meta-tactic/goal.fs's lf-intros-size, lf-goal-intros and lf-goal-intro-n
\ with names 0 and kinds 0), over the S2 slice in an authoring run, by the
\ classes of docs/development/TEST_COVERAGE_REVIEW.md: 1. outcomes:
\ getIntrosSize of pis and lets as they are (none through a definition: ¬ p
\ counts 0; none through a metavariable either, the caller instantiates
\ first), intros of three binders (implicit, strict implicit, explicit:
\ each local of its node's kind, named as its binder, inaccessible), of a
\ binder with no name (a), of none (the goal itself, unassigned), the
\ introN refusals: no binder (94 with the goal), a definition that might
\ unfold (93), a let, an instance binder, a binder of no known kind (99);
\ introN's binder through instantiation and through whnfCore (a
\ beta-redex); 2. malformed input: an assigned goal (a fault, invalid);
\ 3. stack effects (each T{ }T checks the depth); 5. resources and 6.
\ state: intros' cells and introN's frames given back after each refusal,
\ the current context put back; 7. regression pins: kinds, names, flags.
\ Nothing here accepts a theorem: only the kernel's check does.
require ../../../support/tester.fs
require ../../../../src/main.fs
decimal

4000000 lf-term-capacity! drop  100000 lf-cref-capacity! drop
T{ s" tests/front/s2-slice.ndjson" true lfc-library-open -> outcome-ok }T
T{ s" tests/front/s2-slice.elab.ndjson" lfc-elab-file! lfc-elab-read lfc-rooms
   -> outcome-ok outcome-ok }T
lf-author-begin
: made ( x outcome -- x ) ok? 0= abort" intros test: not made" ;
: nat ( -- t ) s" Nat" lf-mk-const0 ;
: prop ( -- t ) 0 lf-term-symbolic-sort lf-made! ;
lf-mctx-view constant view0
: goal ( type -- goal ) 0 view0 lf-goal-new made ;
: code1 ( x xt -- code ) catch dup if nip then ;
: name= ( id c-addr u -- flag ) lfa-intern = ;
\ A pi named c-addr u of kind over dom and body (bound variables as given).
: pi-named ( dom body c-addr u kind -- t )
  >r lfa-intern >r lf-term-pi lf-made! dup r> r> lf-pres-binder! made ;
: bvar ( i -- t ) lf-term-bvar lf-made! ;
: eq-nat ( a b -- t ) lf-mk-eq ;
\ ∀ {x : Nat} ⦃y : Nat⦄ (z : Nat), Nat: three binders of the three kinds.
: three ( -- t )
  nat nat nat nat s" z" lf-binder-default pi-named s" y" lf-binder-strict pi-named
  s" x" lf-binder-implicit pi-named ;
: frames0? ( -- flag ) mti-frames slab-count mti-cells slab-count or 0= lf-mctx-view view0 = and ;
: local-at ( goal k -- local ) swap lf-goal-view dup lf-view-count rot - 1- lf-view-local ;

\ ---- getIntrosSize: pis and lets as they are.
: let-nat ( -- t ) nat nat 0 bvar lf-term-lam lf-made! 0 lf-let-make lf-made! ;
T{ three lf-intros-size nat lf-intros-size let-nat lf-intros-size -> 3 0 1 }T
: not-p ( -- t ) s" Not" lf-mk-const0 s" True" lf-mk-const0 lf-mk-app ;
T{ not-p lf-intros-size nat nat lf-term-pi lf-made! let-nat lf-term-pi lf-made! lf-intros-size
   -> 0 2 }T
\ let x := 0; Nat → Nat: the let's body counted on (2).
: let-pi ( -- t ) s" Nat.zero" lf-mk-const0 nat nat nat lf-term-pi lf-made! lf-term-lam lf-made!
  0 lf-let-make lf-made! ;
T{ let-pi lf-intros-size -> 2 }T

\ ---- intros: three binders, each local of its node's kind, named as its
\ binder, inaccessible; the new goal Nat, the goal assigned.
three goal constant g3
g3 lf-goal-intros constant g3'
: kind@ ( k -- flags ) g3' swap local-at lf-local-flags ;
T{ g3' lf-goal-type nat lf-meta-eqv made g3 lf-goal-assigned? frames0? -> true true true }T
T{ 2 kind@ 1 kind@ 0 kind@
   -> lf-binder-implicit lf-local-inaccessible or lf-binder-strict lf-local-inaccessible or
      lf-local-inaccessible }T
T{ g3' 2 local-at lf-local-name s" x" name= g3' 0 local-at lf-local-name s" z" name= -> true true }T
\ No binder: the goal itself, not assigned.
T{ nat goal dup lf-goal-intros over = swap lf-goal-assigned? -> true false }T
\ A binder with no name (its record's name 0): a, inaccessible.
: anon-pi ( -- t ) nat nat lf-term-pi lf-made! dup 0 lf-binder-default lf-pres-binder! made ;
T{ anon-pi goal lf-goal-intros 0 local-at dup lf-local-name s" a" name= swap lf-local-flags
   -> true lf-local-inaccessible }T

\ ---- introN with names 0 and kinds 0 (by-intro's and intros' call):
\ refusals, the frames and cells given back.
create xs 3 cells allot
: intro-code ( goal n -- code ) 0 0 rot xs ['] lf-goal-intro-n catch dup if >r 2drop 2drop
  drop r> else nip then ;
: intros-code ( goal -- code ) ['] lf-goal-intros code1 ;
\ A let (telescope.fs's mkLambdaFVars has no let case): 99.
T{ let-nat goal intros-code lf-author-code frames0? -> lf-author-throw 99 true }T
lf-tac-forget
\ An instance binder (a local instance, plan FE3) and a binder of no known
\ kind (no binder record): 99.
T{ nat nat s" i" lf-binder-instance pi-named goal intros-code lf-author-code frames0?
   -> lf-author-throw 99 true }T
lf-tac-forget
T{ nat nat lf-term-pi lf-made! goal intros-code lf-author-code frames0? -> lf-author-throw 99 true }T
lf-tac-forget
\ No binder after the first (Nat → Nat asked for two): 94 with the goal.
T{ nat nat s" n" lf-binder-default pi-named goal 2 intro-code lf-author-code frames0?
   -> lf-author-throw 94 true }T
lf-tac-forget
\ ¬ True: no pi as it is, nor through whnfCore, and Not is a definition
\ whose delta might give one (LeanForth's introN does not unfold it): 93.
T{ not-p goal 1 intro-code frames0? -> -4205 true }T
\ A beta-redex whose whnfCore is a pi: introduced.
: beta-pi ( -- t ) prop 0 bvar 0 bvar s" h" lf-binder-default pi-named lf-term-lam lf-made!
  s" True" lf-mk-const0 lf-mk-app ;
T{ beta-pi goal 1 intro-code frames0? -> 0 true }T
\ An assigned goal is a fault (checkNotAssigned): invalid, nothing left.
T{ three goal dup nat lf-mvar-assign made intros-code frames0? -> -4201 true }T
.( intros test.fs: all tests passed) cr
bye

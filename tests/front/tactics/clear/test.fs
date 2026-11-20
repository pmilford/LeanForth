\ Unit tests of the goal layer's clear and of getFVarId (plan row TB1;
\ src/front/meta-tactic/goal.fs's lf-goal-clear!, goals.fs's
\ lf-local-depends-on?, lctx-views.fs's lf-view-fvar, tactic-core.fs's
\ lf-tac-get-fvar, tactic-msg.fs's lf-tac-quoted.), over the S2 slice and
\ its elaboration data in an authoring run, by the classes of
\ docs/development/TEST_COVERAGE_REVIEW.md: 1. outcomes: a hypothesis and a
\ variable nothing depends on cleared (the new goal's context without it,
\ the same type and tag, the old goal assigned); Lean's three refusals
\ with their texts and the goal: an unknown variable (440), a hypothesis
\ that depends on it, the oldest of two (441; also a let whose value
\ does), the goal's type (442); through by-clear's text, getFVarId's
\ refusal of a constant (389) and the clears above; 2. malformed input:
\ an assigned goal (a fault, invalid); 3. stack effects (each T{ }T checks
\ the depth); 6. state: a refusal leaves the goal unassigned and the
\ current context as it was; 7. regression pins: the texts.
\ Nothing here accepts a theorem: only the kernel's check does.
require ../../../support/tester.fs
require ../../../../src/main.fs
require ../../../support/tactic-text.fs
decimal

4000000 lf-term-capacity! drop  100000 lf-cref-capacity! drop
T{ s" tests/front/s2-slice.ndjson" true lfc-library-open -> outcome-ok }T
T{ s" tests/front/s2-slice.elab.ndjson" lfc-elab-file! lfc-elab-read lfc-rooms
   -> outcome-ok outcome-ok }T
lf-author-begin
: made ( x outcome -- x ) ok? 0= abort" clear test: not made" ;
: nat ( -- t ) s" Nat" lf-mk-const0 ;
: binder ( type c-addr u -- fvar )
  lfa-intern swap lf-lctx-local made tuck swap 0 lf-local-new made
  lf-mctx-view swap lf-view-push made lf-mctx-view! ;
: le ( a b -- t ) >r >r s" LE.le" 0 lf-mk-const1 nat lf-mk-app s" instLENat" lf-mk-const0
  lf-mk-app r> lf-mk-app r> lf-mk-app ;
: goal ( type -- goal ) 0 lf-mctx-view lf-goal-new made ;
: detail$ ( -- c-addr u ) 0 lfa-detail slab-at lfa-detail slab-count ;
: detail-has? ( c-addr u -- flag ) detail$ 2swap search nip nip ;
: clear-code ( goal fvar -- code ) ['] lf-goal-clear! catch dup if nip nip then ;
lf-mctx-view constant view0
nat s" a" binder constant fa
nat s" b" binder constant fb
fa fa le s" h1" binder constant fh1
fa fa le s" h2" binder constant fh2
lf-mctx-view constant view4

\ ---- lf-view-fvar: local k's free variable, oldest first.
T{ view4 0 lf-view-fvar view4 3 lf-view-fvar view4 lf-view-count -> fa fh2 4 }T
\ ---- lf-local-depends-on?: h1's type depends on a, not on b.
T{ fh1 fa lf-local-depends-on? fh1 fb lf-local-depends-on? -> true outcome-ok false outcome-ok }T

\ ---- Cleared: b (nothing depends on it), the context without b, the same
\ type and tag, the goal assigned; then h2.
: tagged ( type -- goal ) goal dup s" left" lfa-intern lf-mvar-tag! made ;
fa fa le tagged constant g1
g1 fb lf-goal-clear! constant g1'
T{ g1' lf-goal-view fb lf-view-has? g1' lf-goal-view lf-view-count g1' lf-goal-type g1 lf-goal-type =
   g1' lf-goal-tag g1 lf-goal-tag = g1 lf-goal-assigned? lf-mctx-view view4 =
   -> false 3 true true true true }T
T{ g1' fh2 lf-goal-clear! lf-goal-view lf-view-count -> 2 }T

\ ---- Lean's refusals, each with the goal; the goal left unassigned.
\ a: h1 depends on it, the oldest of h1 and h2 (441).
fa fa le goal constant g2
T{ g2 fa clear-code lf-author-code g2 lf-goal-assigned? lf-mctx-view view4 =
   -> lf-author-throw 441 false true }T
T{ s"  'h1' depends on 'a'" detail-has? s" ⊢ a ≤ a" detail-has? -> true true }T
lf-tac-forget
\ b: the goal's type depends on it (442).
T{ fb fb le goal fb clear-code lf-author-code -> lf-author-throw 442 }T
T{ s"  'b'" detail-has? -> true }T
lf-tac-forget
\ A variable of another context (unknown variable, 440; it prints as a
\ name outside the goal's context does, not as x).
view0 lf-mctx-view!  nat s" x" binder constant fx  view4 lf-mctx-view!
T{ nat goal fx clear-code lf-author-code -> lf-author-throw 440 }T
T{ detail$ drop 2 s"  '" compare s" ⊢ Nat" detail-has? -> 0 true }T
lf-tac-forget
\ A let whose value mentions b (localDeclDependsOn reads the value): 441.
: let-local ( -- fvar )
  s" c" lfa-intern nat fb lf-lctx-let made tuck swap 0 lf-local-new made
  lf-mctx-view swap lf-view-push made lf-mctx-view! ;
let-local constant fc
T{ fc fb lf-local-depends-on? nat goal fb clear-code lf-author-code
   -> true outcome-ok lf-author-throw 441 }T
T{ s"  'c' depends on 'b'" detail-has? -> true }T
lf-tac-forget
view4 lf-mctx-view!
\ An assigned goal is a fault (checkNotAssigned): invalid.
T{ nat goal dup fa lf-mvar-assign made fb clear-code -> -4201 }T

\ ---- by-clear's text: getFVarId (389 for a constant), then clear.
: ran ( c-addr u -- code )
  s" Nat explicit: a Nat explicit: b a a ≤ explicit: h a a ≤" 2swap tactic-ran ;
T{ s" ' b by-clear ' h by-exact" ran -> 0 }T
T{ s" ' Nat.le_refl by-clear" ran -> 389 }T
T{ s"  `Nat.le_refl`; expected single reference to variable" detail-has? -> true }T
lf-tac-forget
T{ s" ' a by-clear" ran -> 441 }T
lf-tac-forget
\ An application is no variable either (389); elabTermForApply's other
\ caller, by-apply, on an identifier and on an application (postponing
\ allowed), which give no metavariable.
T{ s" ' Nat.succ ' a $ by-clear" ran -> 389 }T
lf-tac-forget
T{ s" ' Nat.le_refl by-apply" ran s" ' Nat.le_refl ' a $ by-apply" ran -> 0 0 }T
.( clear test.fs: all tests passed) cr
bye

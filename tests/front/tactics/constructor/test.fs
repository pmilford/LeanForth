\ Unit tests of the goal layer's constructor (slice a2-iii;
\ src/front/meta-tactic/constructor.fs) over the S2 slice and its
\ elaboration data in an authoring run, by the classes of
\ docs/development/TEST_COVERAGE_REVIEW.md: 1. outcomes: the first
\ constructor that applies and its goals (And: left and right; True:
\ none), no inductive type (382), no constructor applies (383), both
\ thrown with no step running; observing?'s verdict on each kind of
\ failure: a Lean error (an authoring error whose outcome is invalid, a
\ library rejection) is "does not apply", anything else is thrown on;
\ 2. malformed input: an assigned goal (a fault, invalid); 3. stack
\ effects (each T{ }T checks the depth); 6. state: a failed probe leaves
\ no assignment and no error recorded; 7. regression pins: Lean's choice
\ (Or.inl when both apply) and the goals' tags.
\ Nothing here accepts a theorem: only the kernel's check does.
require ../../../support/tester.fs
require ../../../../src/load/checker.fs
require ../../../../src/load/front.fs
require ../../../../src/cli/check-lf.fs
decimal

4000000 lf-term-capacity! drop  100000 lf-cref-capacity! drop
T{ s" tests/front/s2-slice.ndjson" true lfc-library-open -> outcome-ok }T
T{ s" tests/front/s2-slice.elab.ndjson" lfc-elab-file! lfc-elab-read lfc-rooms
   -> outcome-ok outcome-ok }T
lf-author-begin
: made ( x outcome -- x ) ok? 0= abort" constructor test: not made" ;
: nat ( -- t ) s" Nat" lf-mk-const0 ;
: binder ( type c-addr u -- fvar )
  lfa-intern swap lf-lctx-local made tuck swap 0 lf-local-new made
  lf-mctx-view swap lf-view-push made lf-mctx-view! ;
: goal ( type -- goal ) 0 lf-mctx-view lf-goal-new made ;
: code1 ( x xt -- code ) catch dup if nip then ;
: le ( a b -- t ) >r >r s" LE.le" 0 lf-mk-const1 nat lf-mk-app s" instLENat" lf-mk-const0
  lf-mk-app r> lf-mk-app r> lf-mk-app ;
: and2 ( p q -- t ) >r >r s" And" lf-mk-const0 r> lf-mk-app r> lf-mk-app ;
: or2 ( p q -- t ) >r >r s" Or" lf-mk-const0 r> lf-mk-app r> lf-mk-app ;
: tag@ ( goal -- c-addr u ) lf-mvar-tag drop lf-name-text ;
nat s" a" binder constant fa
nat s" b" binder constant fb

\ ---- observing?'s verdict (tactic-msg.fs's lf-tac-lean-error?): a Lean error or not.
T{ -4204 lf-tac-lean-error? -4201 lf-tac-lean-error? -4205 lf-tac-lean-error? 77 lf-tac-lean-error?
   -> true false false false }T
T{ s" " 0 lfa-e-assumption lfa-record lf-author-throw lf-tac-lean-error? -> true }T
lf-tac-forget
T{ s" " 0 lfa-e-tac-meta lfa-record lf-author-throw lf-tac-lean-error? -> false }T
lf-tac-forget
T{ -4205 ' mco-caught code1 77 ' mco-caught code1 -4204 mco-caught -> -4205 77 false }T

\ ---- And: And.intro, its two goals left and right.
: and-goals ( -- goals ) fa fb le fb fa le and2 goal lf-goal-constructor ;
T{ and-goals dup run-count swap dup 0 run@ tag@ s" left" compare swap 1 run@ tag@ s" right"
   compare -> 2 0 0 }T
\ True: True.intro, no goal; the goal is assigned.
T{ s" True" lf-mk-const0 goal dup lf-goal-constructor swap lf-instantiate! s" True.intro"
   lf-mk-const0 lf-meta-eqv -> 0 true outcome-ok }T
\ a ≤ a ∨ a ≤ b: both apply; Or.inl is chosen (Lean's order), one goal.
T{ fa fa le fa fb le or2 goal dup lf-goal-constructor run-count swap lf-instantiate!
   lf-meta-head s" Or.inl" lf-mk-const0 lf-meta-eqv -> 1 true outcome-ok }T
\ False: no constructor (383); Nat → Nat, no inductive type (382); no
\ error left recorded by the probes, nothing assigned.
T{ s" False" lf-mk-const0 goal dup ' lf-goal-constructor code1 lf-author-code
   rot lf-goal-assigned? -> lf-author-throw 383 false }T
lf-tac-forget
: arrow ( -- t ) nat nat lf-term-pi lf-made! ;
T{ arrow goal ' lf-goal-constructor code1 lf-author-code -> lf-author-throw 382 }T
lf-tac-forget
\ An assigned goal is a fault (checkNotAssigned): invalid, before the
\ search (False has no constructor: without the check, error 383).
: solved ( -- goal ) s" False" lf-mk-const0 goal dup fa lf-mvar-assign made ;
T{ solved ' lf-goal-constructor code1 -> -4201 }T
\ a + 1 ≤ a: both of Nat.le's constructors are tried and fail (Lean's
\ "no applicable constructor found"), each probe's error forgotten.
: succ ( a -- t ) s" Nat.succ" lf-mk-const0 swap lf-mk-app ;
T{ fa succ fa le goal ' lf-goal-constructor code1 lf-author-code
   -> lf-author-throw 383 }T
lf-tac-forget
\ Expr.constLevels! and one level (core/constant-term-boundary.fs), for a
\ constructor at its type's levels.
nat lf-level! constant lvl1
T{ s" congrArg" 0 0 2 lf-mk-const lf-const-levels -> 0 0 2 }T
: c1 ( -- c ) s" congrArg" lvl1 0 2 lf-mk-const ;
T{ c1 lf-const-levels c1 0 lf-const-level@ c1 1 lf-const-level@ -> lvl1 0 2 lvl1 0 }T
T{ s" Nat" lf-mk-const0 lf-const-levels -> 0 }T
.( constructor test.fs: all tests passed) cr
bye

\ Unit tests of by-right's record (plan row TB1; src/front/tactics/
\ right.fs's tri-nth over src/front/meta-tactic/constructor.fs's
\ lf-goal-nth-constructor, whose own tests are tests/front/tactics/left/
\ test.fs), over the S2 slice in an authoring run: 1. outcomes: constructor
\ 1 of Or (Or.inr and its goal b ≤ a) and of Nat.le through whnf
\ (Nat.le.step, one goal Nat.le a a), right's two codes (387 no inductive
\ type, 388 not two constructors); 3. stack effects; 7. regression pins:
\ the record's fields.
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
: made ( x outcome -- x ) ok? 0= abort" right test: not made" ;
: nat ( -- t ) s" Nat" lf-mk-const0 ;
: binder ( type c-addr u -- fvar )
  lfa-intern swap lf-lctx-local made tuck swap 0 lf-local-new made
  lf-mctx-view swap lf-view-push made lf-mctx-view! ;
: goal ( type -- goal ) 0 lf-mctx-view lf-goal-new made ;
: le ( a b -- t ) >r >r s" LE.le" 0 lf-mk-const1 nat lf-mk-app s" instLENat" lf-mk-const0
  lf-mk-app r> lf-mk-app r> lf-mk-app ;
: or2 ( p q -- t ) >r >r s" Or" lf-mk-const0 r> lf-mk-app r> lf-mk-app ;
: head-is? ( goal c-addr u -- flag ) rot lf-instantiate! lf-meta-head -rot lf-mk-const0
  lf-meta-eqv made ;
: nth-code ( goal nth -- code ) ['] lf-goal-nth-constructor catch dup if nip nip then ;
nat s" a" binder constant fa
nat s" b" binder constant fb

T{ tri-nth nth-idx @ tri-nth nth-expected @ tri-nth nth-target @ tri-nth nth-count @
   -> 1 2 387 388 }T
\ Or.inr, its goal b ≤ a.
T{ fa fb le fb fa le or2 goal dup tri-nth lf-goal-nth-constructor dup run-count swap 0 run@
   lf-goal-type lf-instantiate! fb fa le lf-meta-eqv made rot s" Or.inr" head-is? -> 1 true true }T
\ a ≤ a + 1 through whnf: Nat.le.step, one goal.
: succ ( a -- t ) s" Nat.succ" lf-mk-const0 swap lf-mk-app ;
T{ fa fa succ le goal dup tri-nth lf-goal-nth-constructor run-count swap s" Nat.le.step" head-is?
   -> 1 true }T
\ 387: a function type; 388: True has one constructor.
T{ nat nat lf-term-pi lf-made! goal tri-nth nth-code lf-author-code -> lf-author-throw 387 }T
lf-tac-forget
T{ s" True" lf-mk-const0 goal tri-nth nth-code lf-author-code -> lf-author-throw 388 }T
lf-tac-forget
\ ---- by-right's text (the plug-in's run words, tactics/right.fs): Or.inr,
\ then exact; ¬ a = b refused (387).
T{ s" Nat explicit: a Nat explicit: b b a ≤ explicit: h a b ≤ b a ≤ Or" s" by-right ' h by-exact"
   tactic-ran -> 0 }T
T{ s" Nat explicit: a Nat explicit: b a b = Not" s" by-right" tactic-ran -> 387 }T
lf-tac-forget
.( right test.fs: all tests passed) cr
bye

\ Unit tests of the goal layer's nthConstructor (plan row TB1;
\ src/front/meta-tactic/constructor.fs's lf-nth-constructor: and
\ lf-goal-nth-constructor) and of by-left's record (src/front/tactics/
\ left.fs's tle-nth), over the S2 slice in an authoring run, by the classes
\ of docs/development/TEST_COVERAGE_REVIEW.md: 1. outcomes: constructor 0
\ of a type with two (Or: Or.inl and its goal;
\ Nat.le through whnf: Nat.le.refl, no goal), the error of the record's
\ target code for a goal whose head is no inductive type (a function type)
\ and of its count code for 0, 1 and 3 constructors (False, And,
\ Lean.Name), apply's error with "the term" (380), all with the goal after
\ a blank line; 2. malformed input: an assigned goal (a fault, invalid,
\ before the type is read); the load refusing a record whose index is not
\ below the count expected (Lean's out-of-bounds branch, not ported);
\ 3. stack effects (each T{ }T checks the depth); 6. state: a refused goal
\ is left unassigned; 7. regression pins: the record's fields as given.
\ Nothing here accepts a theorem: only the kernel's check does.
require ../../../support/tester.fs
require ../../../../src/load/checker.fs
require ../../../../src/load/front.fs
require ../../../../src/cli/check-lf.fs
require ../../../support/tactic-text.fs
decimal

4000000 lf-term-capacity! drop  100000 lf-cref-capacity! drop
T{ s" tests/front/s2-slice.ndjson" true lfc-library-open -> outcome-ok }T
T{ s" tests/front/s2-slice.elab.ndjson" lfc-elab-file! lfc-elab-read lfc-rooms
   -> outcome-ok outcome-ok }T
lf-author-begin
: made ( x outcome -- x ) ok? 0= abort" left test: not made" ;
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
: detail$ ( -- c-addr u ) 0 lfa-detail slab-at lfa-detail slab-count ;
: detail-has? ( c-addr u -- flag ) detail$ 2swap search nip nip ;
: nth-code ( goal nth -- code ) ['] lf-goal-nth-constructor catch dup if nip nip then ;
nat s" a" binder constant fa
nat s" b" binder constant fb

\ ---- The record: Lean's idx and expected, the two codes.
T{ tle-nth nth-idx @ tle-nth nth-expected @ tle-nth nth-target @ tle-nth nth-count @
   -> 0 2 385 386 }T
\ Lean's out-of-bounds branch (idx not below expected) is not ported: the
\ load refuses such a record.
: bad-record ( -- code ) s" 2 2 385 386 lf-nth-constructor: bad-nth" ['] evaluate catch
  dup if nip nip then ;
T{ bad-record 0<> -> true }T

\ ---- Constructor 0 of Or: Or.inl, one goal (a ≤ b, its type ?a as
\ stored, instantiated); of a ≤ a through whnf: Nat.le.refl, no goal.
: or-goal ( -- goal ) fa fb le fb fa le or2 goal ;
T{ or-goal dup tle-nth lf-goal-nth-constructor dup run-count swap 0 run@ lf-goal-type
   lf-instantiate! fa fb le lf-meta-eqv made rot lf-instantiate! lf-meta-head s" Or.inl" lf-mk-const0
   lf-meta-eqv made -> 1 true true }T
T{ fa fa le goal dup tle-nth lf-goal-nth-constructor run-count swap lf-goal-assigned? -> 0 true }T
\ A record of index 1 (by-right's place): Or.inr.
1 2 385 386 lf-nth-constructor: second-nth
T{ or-goal dup second-nth lf-goal-nth-constructor drop lf-instantiate! lf-meta-head
   s" Or.inr" lf-mk-const0 lf-meta-eqv made -> true }T

\ ---- Errors: no inductive type (a function type), the target code; 0, 1
\ and 3 constructors, the count code; each with the goal after a blank
\ line, the goal left unassigned.
: arrow ( -- t ) nat nat lf-term-pi lf-made! ;
T{ arrow goal dup tle-nth nth-code lf-author-code rot lf-goal-assigned?
   -> lf-author-throw 385 false }T
T{ s" ⊢ Nat → Nat" detail-has? detail$ drop c@ 10 = -> true true }T
lf-tac-forget
T{ s" False" lf-mk-const0 goal tle-nth nth-code lf-author-code -> lf-author-throw 386 }T
lf-tac-forget
T{ fa fb le fb fa le and2 goal tle-nth nth-code lf-author-code -> lf-author-throw 386 }T
T{ s" ⊢ a ≤ b ∧ b ≤ a" detail-has? -> true }T
lf-tac-forget
T{ s" Lean.Name" lf-mk-const0 goal tle-nth nth-code lf-author-code -> lf-author-throw 386 }T
lf-tac-forget
\ apply's own error passes through: Nat.le.refl does not fit a ≤ b (380),
\ "the term" (nthConstructor gives apply no term?).
T{ fa fb le goal tle-nth nth-code lf-author-code -> lf-author-throw 380 }T
T{ s"  conclusion of the term" detail-has? -> true }T
lf-tac-forget

\ ---- An assigned goal is a fault (checkNotAssigned): invalid, before
\ the type is read (a function type: without the check, error 385).
: solved ( -- goal ) arrow goal dup fa lf-mvar-assign made ;
T{ solved tle-nth nth-code -> -4201 }T
\ ---- by-left's text (the plug-in's run words, tactics/left.fs): Or.inl,
\ then exact; And refused (386).
T{ s" Nat explicit: a Nat explicit: b a b ≤ explicit: h a b ≤ b a ≤ Or" s" by-left ' h by-exact"
   tactic-ran -> 0 }T
T{ s" Nat explicit: a Nat explicit: b a b ≤ b a ≤ And" s" by-left" tactic-ran -> 386 }T
lf-tac-forget
.( left test.fs: all tests passed) cr
bye

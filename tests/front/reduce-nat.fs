\ Unit tests of the front end's reduceNat? (plan S3a, commit C2;
\ src/front/reduce-nat.fs and src/front/whnf.fs's reduceNat? frames) over
\ the Init slice and the variables of tests/front/whnf-cases.fs, by the
\ classes of docs/development/TEST_COVERAGE_REVIEW.md:
\ 1. outcomes: reduceNat?'s match (Nat.succ, the fourteen operations, and
\    what is none: Nat.le, other argument counts, Nat.pred, a head that is
\    no constant), withNatValue's test (closed, a free variable, an
\    assigned or unassigned metavariable, a metavariable below a beta
\    redex) and its value (a literal, Nat.zero, none), each fold (Bool for
\    Nat.beq and Nat.ble, Nat.succ), and whnf's folded-to through the
\    arguments' whnf (numerals, Nat.zero, an assigned metavariable, a nested
\    fold, decide (10 < 20)), with the original term unfolded when an
\    argument has no value (a free variable first or second, a let
\    variable whose value is a literal, a metavariable assigned one);
\    unsupported for an exponent above 256 (257, two limbs);
\ 2. malformed input: the fold given an operand that is no literal leaf,
\    first, second or both, and Nat.succ of one: invalid, before the
\    threshold is read (core/nat-ops.fs's lf-nat-lits-by; plan 9.4.8l
\    AW); the match reads any term;
\ 3. stack effects: each T{ }T checks the depth;
\ 5. resources: whnf's fuel and the Meta budget run out (exhausted);
\    each fold swept with every heap allocation and every term refused in
\    turn (tests/support/meta-sweeps.fs): its answer or full, never
\    another (a refused literal 0, instantiation, frame or result);
\ 7. regression pins: the indices of the match (Nat.gcd 4, shiftRight 13,
\    Nat.succ lf-meta-nat-succ).
\ tests/front/check_whnf.py compares whnf's results with pinned Lean's.
\ Nothing here accepts a theorem: only the kernel's check does.
include ../support/tester.fs
include ../support/heap-watch.fs
include ../support/meta-sweeps.fs
require ./whnf-cases.fs
decimal

: nat2 ( a b c-addr u -- t ) 0 -rot cn -rot >r app r> app ;
\ Nat.gcd and Nat.shiftRight, which the slice lacks: their names interned
\ here (core/nat-ops.fs's lf-nat-in); reduceNat? reads only the name.
: nat2x ( a b c-addr u -- t ) s" Nat" lf-nat-in made -rot >r app r> app ;
: ofnat ( u -- t ) nat-lit >r l0 1 s" OfNat.ofNat" cn nat app r@ app 0 s" instOfNatNat" cn r> app app ;
: eqv ( a b -- flag ) lf-meta-eqv drop ;
: truth ( e -- c-addr u ) lf-const-name lf-name-text ;
: true? ( e -- flag ) truth s" true" compare 0= ;
: w= ( t expected -- flag outcome ) >r lf-meta-whnf-d r> swap >r eqv r> ;
nat mv-natural lf-mvar-new made constant ?c   0 ?c 2 nat-lit lf-mvar-assign made drop
nat mv-natural lf-mvar-new made constant ?a   0 ?a fx lf-mvar-assign made drop
nat 2 nat-lit lf-lctx-let made in-view constant fg2
nat mv-natural lf-mvar-new made constant ?g   0 ?g fg2 lf-mvar-assign made drop
: beta2 ( -- t ) nat 2 nat-lit lam ?n app ;   \ (fun y => 2) ?n

\ ---- 1. The match.
T{ succ fk app lf-meta-nat-op? -> fk 0 lf-meta-nat-succ true }T
T{ fa fb s" Nat.add" nat2 lf-meta-nat-op? -> fa fb 0 true }T
T{ fa fb s" gcd" nat2x lf-meta-nat-op? fa fb s" shiftRight" nat2x lf-meta-nat-op?
   -> fa fb 4 true fa fb 13 true }T
T{ fa fb s" Nat.le" nat2 lf-meta-nat-op? 0 s" Nat.add" cn fa app lf-meta-nat-op? -> false false }T
T{ fa fb s" Nat.add" nat2 fk app lf-meta-nat-op? succ fa app fb app lf-meta-nat-op? -> false false }T
T{ 0 s" Nat.pred" cn fa app lf-meta-nat-op? fs fa app lf-meta-nat-op? 3 nat-lit lf-meta-nat-op?
   -> false false false }T

\ ---- 1. withNatValue's test, then its value.
T{ 3 nat-lit lf-meta-open? fk lf-meta-open? ?n lf-meta-open? 3 ofnat lf-meta-open?
   -> false true true false }T
\ (A literal leaf compared by value: lf-meta-eqv; the answer's flag and
\ outcome alone.)
: lit= ( lit flag outcome u -- same? flag outcome ) >r rot r> nat-lit eqv -rot ;
: flag-of ( x flag outcome -- flag outcome ) rot drop ;
T{ 3 nat-lit lf-meta-nat-guard 3 lit= -> true true outcome-ok }T
T{ fk lf-meta-nat-guard flag-of ?n lf-meta-nat-guard flag-of -> false outcome-ok false outcome-ok }T
T{ ?c lf-meta-nat-guard 2 lit= ?a lf-meta-nat-guard flag-of -> true true outcome-ok false outcome-ok }T
T{ beta2 lf-meta-nat-guard flag-of ?g lf-meta-nat-guard flag-of -> false outcome-ok false outcome-ok }T
T{ 5 nat-lit lf-meta-nat-value? 5 lit= zero lf-meta-nat-value? 0 lit=
   -> true true outcome-ok true true outcome-ok }T
T{ succ fk app lf-meta-nat-value? flag-of 3 ofnat lf-meta-nat-value? flag-of
   -> false outcome-ok false outcome-ok }T
\ lf-meta-nat-value? is the front end's test before the fold (review
\ s3a-decide M1: the fold refuses an operand that is no literal, plan
\ 9.4.8l AW, but is given literals only, as Lean's withNatValue gives): a
\ free variable, a sort and a constant other than Nat.zero have no value
\ either.
T{ fk lf-meta-nat-value? flag-of 0 sort lf-meta-nat-value? flag-of succ lf-meta-nat-value? flag-of
   -> false outcome-ok false outcome-ok false outcome-ok }T

\ ---- 1. The folded-to.
: folded-to ( a b i -- u outcome ) >r swap nat-lit swap nat-lit r> lf-meta-nat-fold swap lf-lit-cell swap ;
T{ 3 5 0 folded-to 3 5 1 folded-to 6 7 2 folded-to 2 10 3 folded-to -> 8 outcome-ok 0 outcome-ok 42 outcome-ok
   1024 outcome-ok }T
T{ 1071 462 4 folded-to 100 7 5 folded-to 17 5 6 folded-to 12 10 9 folded-to -> 21 outcome-ok 2 outcome-ok
   3 outcome-ok 8 outcome-ok }T
T{ 12 10 10 folded-to 12 10 11 folded-to 3 4 12 folded-to 48 4 13 folded-to 41 0 lf-meta-nat-succ folded-to
   -> 14 outcome-ok 6 outcome-ok 48 outcome-ok 3 outcome-ok 42 outcome-ok }T
T{ 4 nat-lit 4 nat-lit 7 lf-meta-nat-fold swap true? 5 nat-lit 3 nat-lit 8 lf-meta-nat-fold swap true?
   -> outcome-ok true outcome-ok false }T
\ The threshold (exponentiation.threshold, 256): 2 ^ 256 folds (257 bits,
\ five limbs); 2 ^ 257 and an exponent of two limbs answer unsupported.
: two64 ( -- t ) 2 nat-lit 64 nat-lit 3 lf-meta-nat-fold drop ;
T{ 2 nat-lit 256 nat-lit 3 lf-meta-nat-fold swap lf-lit-vector nip -> outcome-ok 5 }T
T{ 2 nat-lit 257 nat-lit 3 lf-meta-nat-fold 2 nat-lit two64 3 lf-meta-nat-fold
   -> -1 outcome-unsupported -1 outcome-unsupported }T

\ ---- 2. An operand that is no literal leaf (review s3a-decide M1, plan
\ 9.4.8l AW): the constant Nat and the application Nat.succ fk, first,
\ second or both, for each operation, and Nat.succ of one: invalid and -1,
\ the cells under the call kept (111). The test comes before the
\ threshold is read, so Nat.pow by Nat.succ fk, whose fields read as a
\ literal of two limbs or more, is invalid, not unsupported.
: sfk ( -- t ) succ fk app ;
T{ sfk lf-term-second@ 1 > -> true }T
: fold-refused? ( v1 v2 i -- flag ) lf-meta-nat-fold outcome-invalid = swap -1 = and ;
: each-fold-refused? ( v1 v2 -- flag ) true 14 0 do >r 2dup i fold-refused? r> and loop nip nip ;
T{ 111 3 nat-lit sfk 3 lf-meta-nat-fold 111 sfk nat 12 lf-meta-nat-fold
   -> 111 -1 outcome-invalid 111 -1 outcome-invalid }T
T{ 111 nat 3 nat-lit 0 lf-meta-nat-fold -> 111 -1 outcome-invalid }T
T{ nat 3 nat-lit each-fold-refused? 3 nat-lit sfk each-fold-refused? sfk nat each-fold-refused?
   -> true true true }T
T{ 111 nat 0 lf-meta-nat-succ lf-meta-nat-fold 111 sfk 0 lf-meta-nat-succ lf-meta-nat-fold
   -> 111 -1 outcome-invalid 111 -1 outcome-invalid }T
\ The first operand no literal and an exponent above 256 (review B1 of
\ AW): invalid, not unsupported, as the test comes before the threshold.
T{ nat 257 nat-lit 3 fold-refused? sfk two64 3 fold-refused? -> true true }T

\ ---- 1. whnf (default transparency): the arguments' whnf, then the fold.
T{ 2 ofnat 3 ofnat s" Nat.add" nat2 5 nat-lit w= succ 3 ofnat app 4 nat-lit w=
   -> true outcome-ok true outcome-ok }T
T{ zero 2 ofnat s" Nat.add" nat2 2 nat-lit w= ?c 3 ofnat s" Nat.add" nat2 5 nat-lit w=
   -> true outcome-ok true outcome-ok }T
: one-one ( -- t ) 1 ofnat 1 ofnat s" Nat.add" nat2 ;
T{ one-one 3 ofnat s" Nat.add" nat2 5 nat-lit w= 1071 ofnat 462 ofnat s" gcd" nat2x 21 nat-lit w=
   -> true outcome-ok true outcome-ok }T
T{ 4 ofnat 4 ofnat s" Nat.beq" nat2 lf-meta-whnf-d swap true? -> outcome-ok true }T
\ decide (10 < 20): Decidable.decide's instance Nat.decLt 10 20 unfolds to
\ Nat.ble 11 20, which folds (Bool.true).
: lt-10-20 ( -- t ) l0 1 s" LT.lt" cn nat app 0 s" instLTNat" cn app 10 ofnat app 20 ofnat app ;
: declt ( -- t ) 10 ofnat 20 ofnat s" Nat.decLt" nat2 ;
T{ 0 s" Decidable.decide" cn lt-10-20 app declt app lf-meta-whnf-d swap true? -> outcome-ok true }T
\ No value for an argument: the original term unfolded (whnfImp's none).
\ k + 2 by the smart path to Nat.succ (k + 1); 2 + k stays (stuck on k); a
\ let variable g2 := 2 and ?g := g2 hold a free variable (none at once,
\ Lean's withNatValue) and (fun y => 2) ?n a metavariable: unfolded, never
\ the fold 5. As a second argument g2 is reached by the smart path's
\ match (its value 2 is Nat.succ 1), after which Nat.succ (3 + 1) folds:
\ 3 + g2 is 5, as Lean's whnf gives it.
T{ fk 2 ofnat s" Nat.add" nat2 lf-meta-whnf-d swap lf-meta-head succ eqv -> outcome-ok true }T
T{ 2 ofnat fk s" Nat.add" nat2 dup lf-meta-whnf-d -rot eqv -> outcome-ok true }T
: unfolded? ( t -- flag outcome ) lf-meta-whnf-d swap lf-lit-leaf? 0= swap ;
T{ fg2 3 ofnat s" Nat.add" nat2 unfolded? ?g 3 ofnat s" Nat.add" nat2 unfolded?
   beta2 3 ofnat s" Nat.add" nat2 unfolded? -> true outcome-ok true outcome-ok true outcome-ok }T
T{ 3 ofnat fg2 s" Nat.add" nat2 5 nat-lit w= -> true outcome-ok }T
\ A closed argument whose whnf is no literal (Classical.choice, an axiom:
\ withNatValue's none after whnf) leaves the term to unfoldDefinition? too:
\ choice + 3 is Nat.succ (choice + 2).
: choice-0 ( -- t )
  lv1 1 s" Classical.choice" cn nat app lv1 1 s" Nonempty.intro" cn nat app 0 ofnat app app ;
T{ choice-0 3 ofnat s" Nat.add" nat2 lf-meta-whnf-d swap lf-meta-head succ eqv -> outcome-ok true }T
T{ 3 ofnat choice-0 s" Nat.add" nat2 dup lf-meta-whnf-d -rot eqv -> outcome-ok true }T
\ Not ported yet: an exponent above 256 (plan S3b).
T{ 2 ofnat 257 ofnat s" Nat.pow" nat2 lf-meta-whnf-d -> -1 outcome-unsupported }T

\ ---- 5. Resources: whnf's fuel (each step one), the Meta budget (an
\ unfolding after an argument without a value).
T{ 3 lf-whnf-fuel! one-one 3 ofnat s" Nat.add" nat2 lf-meta-whnf-d 0 lf-whnf-fuel!
   -> -1 outcome-exhausted }T
T{ 0 lf-meta-budget! fk 2 ofnat s" Nat.add" nat2 lf-meta-whnf-d lf-meta-default-budget lf-meta-budget!
   -> -1 outcome-exhausted }T
\ Each fold with each heap allocation and each term refused in turn:
\ whnf's slabs given back first, so that a frame's first claim allocates.
: nat-slabs-anew ( -- )
  wc-frames sweep-slab-anew wc-args sweep-slab-anew wc-margs sweep-slab-anew
  uf-args sweep-slab-anew uf-levels sweep-slab-anew ;
' nat-slabs-anew sweep-slabs-xt !
: w-d ( e -- x outcome ) lf-meta-whnf-d ;
: s-nested ( -- e xt ) one-one 3 ofnat s" Nat.add" nat2 ['] w-d ;
: s-zero1 ( -- e xt ) zero 2 ofnat s" Nat.add" nat2 ['] w-d ;
: s-zero2 ( -- e xt ) 2 ofnat zero s" Nat.add" nat2 ['] w-d ;
: s-mvar ( -- e xt ) 3 ofnat ?c s" Nat.add" nat2 ['] w-d ;
: s-succ ( -- e xt ) succ 3 ofnat app ['] w-d ;
T{ s-nested heap-sweep swept? s-nested room-sweep swept? -> true true }T
T{ s-zero1 room-sweep swept? s-zero2 room-sweep swept? s-succ room-sweep swept? -> true true true }T
T{ s-mvar heap-sweep swept? s-mvar room-sweep swept? -> true true }T
.( reduce-nat test: all tests passed) cr
bye

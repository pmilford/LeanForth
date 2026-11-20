\ Unit tests of by-decide and by-native-decide (plan row S3, slice S3a;
\ src/front/tactics/decide.fs) over decide's slice of Init in an
\ authoring run, by the classes of docs/development/TEST_COVERAGE_REVIEW.md:
\ 1. outcomes: preprocessPropToDecide's tests called directly (a closed
\    type passes, instantiated; a free variable 251 with Lean's hint; a
\    metavariable 252, which no text reaches before FE2's holes, and 252
\    first when both are there; a let variable, or a let or have
\    expression with a free variable, unsupported, zetaReduce not ported;
\    a let expression without one passes); doElab's (Bool.true's
\    proof, its nodes as Lean's: of_decide_eq_true P I (id (decide P I =
\    true) (Eq.refl true)); Bool.false 250 with the proposition; anything
\    else 253 with the decide term; whnf's unsupported passed on, never 250
\    or 253; no instance 122); the plug-in's run words through LeanForth
\    text (tests/support/tactic-text.fs: accepted, 251, 122, 90 after a
\    first decide, 254 by-native-decide); instance keys that unfold
\    (plan S3a-ops C1): IntList's instance verified, `*`, GT.gt and Ne
\    goals accepted through text;
\ 3. stack effects: each T{ }T checks the depth;
\ 6. state: a refused goal is left unassigned.
\ Nothing here accepts a theorem: only the kernel's check does.
require ../../../support/tester.fs
require ../../../../src/load/checker.fs
require ../../../../src/load/front.fs
require ../../../../src/cli/check-lf.fs
require ../../../support/tactic-text.fs
decimal

4000000 lf-term-capacity! drop  100000 lf-cref-capacity! drop
T{ s" tests/front/decide-slice.ndjson" true lfc-library-open -> outcome-ok }T
T{ s" tests/front/decide-slice.elab.ndjson" lfc-elab-file! lfc-elab-read lfc-rooms
   -> outcome-ok outcome-ok }T
lf-author-begin
: made ( x outcome -- x ) ok? 0= abort" decide test: not made" ;
: nat ( -- t ) s" Nat" lf-mk-const0 ;
: binder ( type c-addr u -- fvar )
  lfa-intern swap lf-lctx-local made tuck swap 0 lf-local-new made
  lf-mctx-view swap lf-view-push made lf-mctx-view! ;
: code1 ( x xt -- code ) catch dup if nip then ;
: num ( u -- t ) lf-meta-nat-lit made ;
: eq-nat ( a b -- t ) lf-mk-eq ;
: detail$ ( -- c-addr u ) 0 lfa-detail slab-at lfa-detail slab-count ;
: detail-has? ( c-addr u -- flag ) detail$ 2swap search nip nip ;
: eqv ( a b -- flag ) lf-meta-eqv made ;
: bool-true ( -- t ) s" Bool.true" lf-mk-const0 ;
: decide-of ( p -- e ) lf-mk-decide ;

\ ---- preprocessPropToDecide.
: two=two ( -- t ) 2 num 2 num eq-nat ;
T{ two=two dup tdc-pre eqv -> true }T
nat s" n" binder constant fn
T{ fn 1 num eq-nat ' tdc-pre code1 lf-author-code -> lf-author-throw 251 }T
T{ s"   n = 1" detail-has? s\" \n\nHint: Use the `+revert` option to automatically clean up and revert free variables"
   detail-has? -> true true }T
lf-tac-forget
nat mv-natural lf-mvar-new made constant ?m
T{ ?m 1 num eq-nat ' tdc-pre code1 lf-author-code -> lf-author-throw 252 }T
T{ s" Expected type must not contain metavariables" 252 lf-author-message compare -> 0 }T
lf-tac-forget
\ A let variable g := 2 in the goal: zetaReduce is plan S3b's, so the
\ step answers unsupported (thrown, -4205), never 251.
nat 2 num lf-lctx-let made constant fg
T{ fg 2 num eq-nat ' tdc-pre code1 -> -4205 }T
\ Lean's order (L2 of the review of S3a): a metavariable (252) is reported
\ before a free variable (251) when P holds both.
T{ ?m fn eq-nat ' tdc-pre code1 lf-author-code -> lf-author-throw 252 }T
lf-tac-forget
\ A universe level metavariable makes the order visible (re-check of the
\ S3a fixes, R1): Sort ?u applied to n holds a metavariable (hasMVar counts
\ a level's) and a free variable both, and Lean reports 252.
: sort-?u ( -- t ) lf-level-mvar-new made lf-term-symbolic-sort 0= abort" decide test: no sort" ;
T{ sort-?u fn lf-term-app drop ' tdc-pre code1 lf-author-code -> lf-author-throw 252 }T
lf-tac-forget
\ A let or have expression in P with a free variable (review s3a-decide B2):
\ zetaReduce would remove or substitute it, so the step answers
\ unsupported, never 251, at the root and inside; without a free variable
\ P is left as it is, for whnf.
: let-over ( v body nondep -- t )
  >r nat swap lf-term-lam 0= abort" decide test: no lambda"
  r> lf-let-make 0= abort" decide test: no let" ;
T{ fn two=two 0 let-over ' tdc-pre code1 fn two=two 1 let-over ' tdc-pre code1 -> -4205 -4205 }T
T{ 2 num fn 2 num 0 let-over eq-nat ' tdc-pre code1 -> -4205 }T
T{ 2 num two=two 0 let-over dup tdc-pre eqv -> true }T
\ ---- doElab: Bool.true's proof, node for node.
\ Pinned Lean's term (pp.all) for True, written out node by node.
: true-p ( -- t ) s" True" lf-mk-const0 ;
: inst-true ( -- t ) s" instDecidableTrue" lf-mk-const0 ;
: bool ( -- t ) s" Bool" lf-mk-const0 ;
: dec-true ( -- t ) s" Decidable.decide" lf-mk-const0 true-p lf-mk-app inst-true lf-mk-app ;
: eq-hint ( -- t ) s" Eq" nat lf-level! lf-mk-const1 bool lf-mk-app dec-true lf-mk-app
  bool-true lf-mk-app s" id" 0 lf-mk-const1 swap lf-mk-app ;
: refl-true ( -- t ) s" Eq.refl" nat lf-level! lf-mk-const1 bool lf-mk-app bool-true lf-mk-app ;
: lean-true-proof ( -- e )
  s" of_decide_eq_true" lf-mk-const0 true-p lf-mk-app inst-true lf-mk-app
  eq-hint refl-true lf-mk-app lf-mk-app ;
T{ true-p tdc-decide lean-true-proof eqv -> true }T
T{ true-p decide-of lf-term-second@ inst-true eqv -> true }T
\ Bool.false: 250 with the proposition; a term stuck at Classical.choice:
\ 253 with the decide term; whnf's unsupported (an exponent above 256)
\ passed on (-4205), never 250 or 253; no instance: 122.
T{ 2 num 5 num eq-nat ' tdc-decide code1 lf-author-code -> lf-author-throw 250 }T
T{ s\"   2 = 5\nis false" detail-has? -> true }T
lf-tac-forget
: choice0 ( -- t ) s" Classical.choice" nat lf-level! lf-mk-const1 nat lf-mk-app
  s" Nonempty.intro" nat lf-level! lf-mk-const1 nat lf-mk-app 0 num lf-mk-app lf-mk-app ;
T{ choice0 0 num eq-nat ' tdc-decide code1 lf-author-code -> lf-author-throw 253 }T
T{ s\" \nto `true` or `false`." detail-has? -> true }T
lf-tac-forget
: pow300 ( -- t ) s" Nat.pow" lf-mk-const0 2 num lf-mk-app 300 num lf-mk-app ;
T{ pow300 1 num eq-nat ' tdc-decide code1 -> -4205 }T
: nonempty-nat ( -- t ) s" Nonempty" nat lf-level! lf-mk-const1 nat lf-mk-app ;
T{ nonempty-nat ' tdc-decide code1 lf-meta-failed nip -> -4204 122 }T

\ ---- The run words through text: accepted; 251; 122; 90; 254.
T{ s" 1071 462 Nat.gcd 21 =" s" by-decide" tactic-ran -> 0 }T
T{ s" Nat explicit: k k k Nat.add k =" s" by-decide" tactic-ran -> 251 }T
lf-tac-forget
T{ s" Nat Nonempty" s" by-decide" tactic-ran -> 122 }T
T{ s"   Decidable" detail-has? -> true }T
lf-tac-forget
T{ s" True" s" by-decide by-decide" tactic-ran -> 90 }T
lf-tac-forget
T{ s" True" s" by-native-decide" tactic-ran lf-author-code lf-author-outcome -> 254 outcome-unsupported }T
lf-tac-forget

\ ---- Instance keys that unfold (plan S3a-ops C1, DiscrTree's reduceDT):
\ the abbreviation IntList is unfolded in the keys of
\ Lean.Omega.IntList.instHMulInt, the first candidate Lean tries for a
\ numeral `*`, so its check passes and `6 7 *` elaborates; the reducible
\ GT.gt is unfolded in the goal Decidable (20 > 10), keyed as 10 < 20,
\ where Nat.decLt is found; Ne gives Not (Eq ..), instDecidableNot.
: inst-of ( c-addr u -- i )
  lf-mk-const0 lf-dt-const-decl 0= abort" decide test: no declaration"
  elab-instance-of 0= abort" decide test: no instance" ;
T{ s" Lean.Omega.IntList.instHMulInt" inst-of lf-inst-check -> outcome-ok }T
T{ s" 6 7 * 42 =" s" by-decide" tactic-ran -> 0 }T
T{ s" 20 10 GT.gt" s" by-decide" tactic-ran s" 3 4 Ne" s" by-decide" tactic-ran -> 0 0 }T
\ isBadKey's pi head (Main.lean:218-225, review ops-c1 B3): DecidableEq
\ Nat, an abbreviation of (a b : Nat) → Decidable (a = b)
\ (Prelude.lean:1206), unfolds at a root to a pi, whose key is arrow and
\ its domain Nat, as pinned Lean's mkPath gives [∀, Nat].
: dec-eq-nat ( -- t ) s" DecidableEq" nat lf-level! lf-mk-const1 nat lf-mk-app ;
: dec-eq-keys ( -- n tag0 tag1 )
  dec-eq-nat lf-dt-path made swap dup elab-key-tag swap 1+ elab-key-tag ;
T{ dec-eq-keys -> 2 elab-key-arrow elab-key-const }T
.( decide test.fs: all tests passed) cr
bye

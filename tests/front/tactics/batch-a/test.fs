\ Unit tests of tactic batch 1 (plan row TB2) over decide's slice of Init
\ in an authoring run, by the classes of docs/development/
\ TEST_COVERAGE_REVIEW.md: the library words (app-builder.fs's
\ mkExpectedTypeHint, mkFalseElim, mkAbsurd, matchNot?, matchNe?,
\ matchHEq?; meta-tactic/goal.fs's replaceTargetDefEq and lf-goal-fresh;
\ assumption.fs's findLocalDeclWithType?; revert.fs; assert.fs; delta.fs;
\ contradiction.fs; tactic-core.fs's first) called on goals built here,
\ and each tactic word through LeanForth text (tests/support/
\ tactic-text.fs):
\ 1. outcomes: each word's result, each refusal with its code (443-449,
\    389, 381, 96, 90), each case not ported (99, 93 through the runner;
\    unsupported or invalid thrown by the library words);
\ 2. malformed input: an assigned goal (invalid), a local asked that the
\    goal's context does not hold (invalid), an unknown name (invalid),
\    first of no alternative (invalid);
\ 3. stack effects: each T{ }T checks the depth;
\ 6. state: a refused goal is left unassigned; the tactics' terms are
\    checked node for node with pinned Lean by check.py.
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
: made ( x outcome -- x ) ok? 0= abort" batch-a test: not made" ;
lf-meta-throw-base outcome-invalid - constant thrown-invalid
lf-meta-throw-base outcome-unsupported - constant thrown-unsupported
: nat ( -- t ) s" Nat" lf-mk-const0 ;
: prop ( -- t ) 0 lf-term-symbolic-sort lf-made! ;
: fresh ( -- ) lf-view-empty lf-mctx-view! ;
: local+ ( type c-addr u flags -- fvar )
  >r lfa-intern swap lf-lctx-local made tuck swap r> lf-local-new made
  lf-mctx-view swap lf-view-push made lf-mctx-view! ;
: binder ( type c-addr u -- fvar ) 0 local+ ;
: goal ( type -- goal ) 0 lf-mctx-view lf-goal-new made ;
: tagged ( type -- goal ) goal dup s" t" lfa-intern lf-mvar-tag! made ;
: code1 ( x xt -- code ) catch dup if nip then ;
: code2 ( x y xt -- code ) catch dup if nip nip then ;
: code4 ( w x y z xt -- code ) catch dup if >r 2drop 2drop r> then ;
\ An authoring error's code (the error forgotten); any other THROW code as it is.
: authored ( code -- n ) dup lf-author-throw = if drop lf-author-code lf-tac-forget then ;
\ An application's function and argument.
: app-parts ( t -- f a ) dup lf-term-first@ swap lf-term-second@ ;
: eqv? ( a b -- flag ) lf-meta-eqv made ;
: le ( x y -- t ) s" LE.le" 2swap 2 lf-mk-app-m ;
: ge ( x y -- t ) s" GE.ge" 2swap 2 lf-mk-app-m ;
: ne ( x y -- t ) s" Ne" 2swap 2 lf-mk-app-m ;
: not-of ( p -- t ) s" Not" lf-mk-const0 swap lf-mk-app ;
: false-t ( -- t ) s" False" lf-mk-const0 ;
: const? ( t c-addr u -- flag ) rot lf-meta-head -rot lf-meta-const-named? ;
: zero? ( u -- flag ) lf-level-tag@ lf-level-tag-zero = ;
: one? ( u -- flag ) dup lf-level-tag@ lf-level-tag-succ = swap lf-level-first@ zero? and ;
: level0 ( t -- u ) lf-meta-head 0 lf-const-level@ ;
: view# ( goal -- n ) lf-goal-view lf-view-count ;
: open? ( mvar -- flag ) lf-goal-assigned? 0= ;
: nlit ( u -- t ) lf-meta-nat-lit made ;
: mvar ( type -- m ) mv-natural lf-mvar-new made ;

fresh
nat s" a" binder constant fa
nat s" b" binder constant fb
fa fb le constant ab-le
fb fa le constant ba-le
fa fb ge constant ab-ge
ab-le s" h" binder constant fh
ab-le not-of s" hn" binder constant fhn
false-t s" hf" binder constant fhf

\ ---- app-builder.fs: mkExpectedTypeHint, mkFalseElim, mkAbsurd.
T{ fh ab-le lf-mk-expected-type-hint dup s" id" const? over level0 zero? rot lf-meta-args2
   fh = swap ab-le = -> true true true true }T
T{ fa nat lf-mk-expected-type-hint level0 one? -> true }T
T{ ab-le fhf lf-mk-false-elim dup s" False.elim" const? over level0 zero? rot lf-meta-args2
   fhf = swap ab-le = -> true true true true }T
T{ nat fhf lf-mk-false-elim level0 one? -> true }T
: absurd-arg ( t i -- a ) 4 lf-meta-nth-arg ;
fa fb lf-mk-eq fh fhn lf-mk-absurd constant e-absurd
T{ e-absurd s" absurd" const? e-absurd level0 zero? -> true true }T
T{ e-absurd 0 absurd-arg ab-le = e-absurd 2 absurd-arg fh = e-absurd 3 absurd-arg fhn =
   -> true true true }T

\ ---- matchNot?, matchNe?, matchHEq?: on the term, then after whnf.
T{ ab-le not-of lf-match-not? swap ab-le = -> true true }T
T{ ab-le false-t lf-term-pi lf-made! lf-match-not? swap ab-le = -> true true }T
T{ ab-le nat lf-term-pi lf-made! lf-match-not? -> false }T
T{ ab-le lf-match-not? -> false }T
T{ fa fb ne lf-match-not? swap fa fb lf-mk-eq eqv? -> true true }T
: ne-parts? ( α a b -- f1 f2 f3 ) fb = swap fa = rot nat eqv? ;
T{ fa fb ne lf-match-ne? -> fa fb ne lf-match-ne? }T
T{ fa fb ne lf-match-ne? drop ne-parts? -> true true true }T
T{ fa fb lf-mk-eq not-of lf-match-ne? nip nip nip -> true }T
T{ ab-le not-of lf-match-ne? -> false }T
T{ ab-le lf-match-ne? -> false }T
: heq-parts? ( α a β b -- f1 f2 f3 f4 )
  fb = >r nat eqv? >r fa = >r nat eqv? r> r> r> ;
T{ s" HEq" fa fb 2 lf-mk-app-m lf-match-heq? -> s" HEq" fa fb 2 lf-mk-app-m lf-match-heq? }T
T{ s" HEq" fa fb 2 lf-mk-app-m lf-match-heq? drop heq-parts? -> true true true true }T
T{ ab-le lf-match-heq? -> false }T
\ HEq found only after whnf: (fun x : Nat => HEq x b) a.
: heq-redex ( -- t )
  s" HEq" fa fb 2 lf-mk-app-m lf-meta-head nat lf-mk-app 0 lf-term-bvar lf-made! lf-mk-app
  nat lf-mk-app fb lf-mk-app nat swap lf-term-lam lf-made! fa lf-mk-app ;
T{ heq-redex lf-match-heq? drop heq-parts? -> true true true true }T

\ ---- replaceTargetDefEq and lf-goal-fresh.
ab-ge tagged constant g1
T{ g1 ab-ge lf-goal-replace-target-defeq g1 = g1 open? -> true true }T
g1 ba-le lf-goal-replace-target-defeq constant g1'
T{ g1' lf-goal-type ba-le = g1' lf-goal-tag g1 lf-goal-tag = g1' lf-goal-view g1 lf-goal-view =
   g1' lf-goal-kind mv-opaque = -> true true true true }T
T{ g1 lf-instantiate! dup s" id" const? swap lf-meta-args2 g1' = swap ab-ge = -> true true true }T
: revert-none ( goal -- flag n ) dup 0 lf-goal-revert -rot = swap ;
: after-none ( goal fvar -- flag n ) over swap lf-goal-revert-after -rot = swap ;
prop mvar constant m-p
m-p goal constant g2
T{ m-p ab-le lf-mvar-assign -> outcome-ok }T
T{ g2 ab-le lf-goal-replace-target-defeq g2 = g2 open? -> true true }T
T{ g1 ba-le ' lf-goal-replace-target-defeq code2 -> thrown-invalid }T
T{ ab-le g1' lf-goal-fresh dup lf-goal-type ab-le = swap lf-goal-tag g1' lf-goal-tag =
   -> true true }T

\ ---- findLocalDeclWithType?: the newest local that fits.
ab-le s" h2" binder constant fh2
T{ ab-le lf-local-index-with-type? swap lf-mctx-fvar fh2 = -> true true }T
T{ ba-le lf-local-index-with-type? -> false }T

\ ---- revert: a hypothesis; a variable and what depends on it; none.
fresh
nat s" a" binder constant ra
nat s" b" binder constant rb
ra rb le constant rab
rab s" h" binder constant rh
rab tagged constant g3
: one-run ( x -- run ) 0 swap run-push made ;
g3 rh one-run lf-goal-revert constant n3 constant g3'
T{ n3 g3' view# g3' lf-goal-type lf-term-pi? g3' lf-goal-tag g3 lf-goal-tag = -> 1 2 true true }T
T{ g3 lf-instantiate! app-parts rh = swap g3' = -> true true }T
rab tagged constant g4
g4 ra one-run lf-goal-revert constant n4 constant g4'
T{ n4 g4' view# g4' lf-goal-type lf-meta-forall-body# nip -> 2 1 2 }T
T{ rab tagged revert-none -> true 0 }T
T{ g3 rh one-run ' lf-goal-revert code2 -> thrown-invalid }T
nat s" c" binder constant rc
: short-view ( -- view ) lf-mctx-view dup lf-view-count 1- run-take made ;
T{ rab 0 short-view lf-goal-new made rc one-run ' lf-goal-revert code2 -> thrown-invalid }T
T{ rab tagged rc after-none -> true 0 }T
rab tagged constant g5
T{ g5 rh lf-goal-revert-after nip -> 1 }T
fresh
nat s" a" binder drop
false-t s" aux" lf-local-impl-detail local+ constant rx
T{ false-t goal rx one-run ' lf-goal-revert code2 -> thrown-unsupported }T

\ ---- assert and replace.
fresh
nat s" a" binder constant sa
nat s" b" binder constant sb
sa sb le constant sab
sb sa le constant sba
sab s" h" binder constant s-h
sba tagged constant g6
g6 s" k" lfa-intern sab s-h lf-goal-assert constant g6'
T{ g6' lf-goal-type dup lf-term-pi? swap lf-binder-name s" k" lfa-intern = -> true true }T
T{ g6' lf-goal-tag g6 lf-goal-tag = g6 lf-instantiate! app-parts s-h = swap g6' =
   -> true true true }T
T{ g6 s" k" lfa-intern sab s-h ' lf-goal-assert code4 -> thrown-invalid }T
\ replace f with f c, f : (x : Nat) -> x ≤ b, c and h2 : c ≤ c after f:
\ the new f follows c (its type names c), h2 is introduced again, the old f
\ cleared.
: bvar0 ( -- t ) 0 lf-term-bvar lf-made! ;
: le-raw ( x y -- t )   \ @LE.le.{0} Nat instLENat x y, made by hand (x may be loose)
  >r >r s" LE.le" 0 lf-mk-const1 nat lf-mk-app s" instLENat" lf-mk-const0 lf-mk-app
  r> lf-mk-app r> lf-mk-app ;
nat bvar0 sb le-raw lf-term-pi lf-made! dup s" x" lfa-intern lf-binder-default lf-pres-binder!
  made constant pi-le
pi-le s" f" binder constant sf
nat s" c" binder constant sc
sc sc le s" h2" binder constant sh2
sa sb le tagged constant g7
g7 sf sf sc lf-mk-app dup lf-infer! lf-goal-replace constant g7'
: name@ ( goal k -- name ) swap lf-goal-view swap lf-view-local lf-local-name ;
: type@ ( goal k -- t ) swap lf-goal-view swap lf-view-fvar lf-fvar-type ;
T{ g7' view# g7' 3 name@ s" c" lfa-intern = g7' 4 name@ s" f" lfa-intern =
   g7' 5 name@ s" h2" lfa-intern = -> 6 true true true }T
T{ g7' 4 type@ sc sb le eqv? g7' lf-goal-view sf lf-view-has? -> true false }T
: hidden@ ( goal k -- flag ) swap lf-goal-view swap lf-view-local lf-local-inaccessible? ;
T{ g7' 4 hidden@ g7' 5 hidden@ -> false false }T
\ The goal names h: replace h by h, then the old h stays (tryClear refused).
s-h s-h lf-mk-eq tagged constant g8
T{ g8 s-h s-h sab lf-goal-replace view# -> 7 }T
T{ sab tagged s-h s-h m-p lf-goal-replace lf-goal-type sab = -> true }T
prop mvar constant m-open
T{ sab tagged s-h s-h m-open ' lf-goal-replace code4 -> thrown-unsupported }T
\ An inaccessible local reverted stays inaccessible when introduced again.
fresh nat s" a" binder constant ia
pi-le s" f" binder constant if1
nat s" c" lf-local-inaccessible local+ drop
ia sb le tagged constant g9
g9 if1 if1 ia lf-mk-app dup lf-infer! lf-goal-replace constant g9'
T{ g9' view# g9' 2 name@ s" c" lfa-intern = g9' 2 hidden@ g9' 1 hidden@ -> 3 true true false }T
\ A goal of a type: assert's pi Nat -> Nat (a node the export may hold).
T{ nat goal s" k" lfa-intern nat ia lf-goal-assert lf-goal-type lf-term-pi? -> true }T

\ ---- delta: GE.ge's applications, a partial one, the constant alone.
: ge-const ( -- c ) s" GE.ge" 0 lf-mk-const1 ;
T{ sa sb ge s" GE.ge" lfa-intern lf-delta-expand sb sa le eqv? -> true }T
T{ sa sb ge sb sa ge s" And" 2swap 2 lf-mk-app-m s" GE.ge" lfa-intern lf-delta-expand
   sb sa le sa sb le s" And" 2swap 2 lf-mk-app-m eqv? -> true }T
T{ ge-const nat lf-mk-app s" instLENat" lf-mk-const0 lf-mk-app sa lf-mk-app
   s" GE.ge" lfa-intern lf-delta-expand lf-term-lam? -> true }T
T{ ge-const s" GE.ge" lfa-intern lf-delta-expand lf-term-lam? -> true }T
T{ sab s" GE.ge" lfa-intern lf-delta-expand sab = -> true }T
T{ sa sb ge s" Nat" lfa-intern lf-delta-expand sa sb ge eqv? -> true }T
T{ s" GE.ge" lf-mk-const0 dup s" GE.ge" lfa-intern lf-delta-expand = -> true }T
T{ sab s" Nat.le_refl" lfa-intern ' lf-delta-expand code2 -> thrown-unsupported }T
T{ sab s" No.such.name" lfa-intern ' lf-delta-expand code2 -> thrown-invalid }T
\ betaRev of an argument with a loose bound variable under a binder of the
\ value, not ported: fun y => @Function.const Nat Nat y.
: const-loose ( -- t )
  s" Function.const" nat sa 2 lf-mk-app-m lf-term-first@ 0 lf-term-bvar lf-made! lf-mk-app
  nat swap lf-term-lam lf-made! ;
T{ const-loose s" Function.const" lfa-intern ' lf-delta-expand code2 -> thrown-unsupported }T
\ betaRev's zeta step, not ported: (let x := a; fun y => y) b.
: let-applied ( -- t )
  sa nat bvar0 lf-term-lam lf-made! nat swap lf-term-lam lf-made! false lf-let-make lf-made!
  sb lf-mk-app ;
T{ let-applied mdl-zeta nip -> outcome-unsupported }T
T{ sab mdl-zeta nip -> outcome-ok }T

\ ---- contradiction: each rule, a fresh context each time.
: rules ( type -- code ) goal ['] lf-goal-contradiction catch dup if nip then authored ;
: hyp ( type -- ) s" h" binder drop ;
fresh nat s" a" binder constant ca  nat s" b" binder constant cb
: c-ab ( -- t ) ca cb lf-mk-eq ;
T{ fresh false-t hyp c-ab rules -> 0 }T
T{ fresh ca cb le not-of hyp ca cb le s" h2" binder drop c-ab rules -> 0 }T
T{ fresh ca ca ne hyp c-ab rules -> 0 }T
T{ fresh ca cb ne hyp c-ab rules -> 449 }T
T{ fresh ca cb le hyp c-ab rules -> 99 }T
T{ fresh s" Bool.true" lf-mk-const0 s" Bool.false" lf-mk-const0 lf-mk-eq hyp c-ab rules -> 99 }T
T{ fresh 1 nlit 2 nlit lf-mk-eq hyp c-ab rules -> 0 }T
T{ fresh ca 0 nlit lf-mk-eq hyp c-ab rules -> 449 }T
T{ fresh s" HEq" s" Bool.true" lf-mk-const0 s" Bool.false" lf-mk-const0 2 lf-mk-app-m hyp
   c-ab rules -> 99 }T
T{ fresh s" HEq" ca cb 2 lf-mk-app-m hyp c-ab rules -> 449 }T
T{ fresh s" True" lf-mk-const0 hyp c-ab rules -> 449 }T
T{ fresh prop mvar hyp c-ab rules -> 449 }T
: not-bit ( -- t ) s" Nat.hasNotBit" lf-mk-const0 ca cb 2 lf-mk-app-n ;
T{ fresh not-bit hyp c-ab rules -> 99 }T
T{ fresh false-t s" aux" lf-local-impl-detail local+ drop c-ab rules -> 449 }T
fresh false-t s" hf" binder constant cf
T{ prop cf lf-mk-false-elim rules -> 99 }T
T{ c-ab goal dup lf-goal-contradiction lf-goal-assigned? -> true }T
\ An equation with a constant the library does not declare: no constructor
\ (isConstructorApp? and whnf, as Lean's getUnfoldableConstNoEx?, find none).
: eq-unknown ( -- t )
  ca ca lf-mk-eq lf-term-first@ s" No.such" lfa-intern 0 lf-mk-const-id lf-mk-app ;
T{ fresh eq-unknown hyp c-ab rules -> 449 }T
T{ s" Not" lfa-intern lf-menv-find made ' mcd-data code1 authored -> 99 }T

\ ---- first: no alternative is a fault; one runs bare.
T{ 0 ' lf-tac-first-of catch nip -> thrown-invalid }T
: one-alt ( -- ) 7 ;
T{ ' one-alt 1 lf-tac-first-of -> 7 }T
\ trivial's all_goals passes over an assigned goal.
T{ 0 g1 ttr-goal -> 0 outcome-ok }T

\ ---- The tactics' words through LeanForth text.
: vars ( -- c-addr u ) s" Nat explicit: a Nat explicit: b " ;
create stmt 512 allot  variable stmt#
: stmt+ ( c-addr u -- ) tuck stmt stmt# @ + swap move stmt# +! ;
: st ( c-addr u -- c-addr' u' ) 0 stmt# ! vars stmt+ stmt+ stmt stmt# @ ;
T{ s" b a ≤ explicit: h a b ≥" st s" b a ≤ by-change ' h by-exact" tactic-ran -> 0 }T
T{ s" b a ≤ explicit: h a b ≥" st s" a b ≤ by-change ' h by-exact" tactic-ran -> 443 }T
T{ s" b a ≤ explicit: h a b ≥" st s" b a ≤ by-show ' h by-exact" tactic-ran -> 0 }T
T{ s" b a ≤ explicit: h a b ≥" st s" a b ≤ by-show" tactic-ran -> 444 }T
T{ s" b a ≤ explicit: h a b ≥" st s" ' h by-exact b a ≤ by-show" tactic-ran -> 90 }T
T{ s" a b ≤ explicit: h1 b a ≤ explicit: h2 a b ≤ b a ≤ ∧" st
   s" ' And.intro by-apply b a ≤ by-show ' h2 by-exact ' h1 by-exact" tactic-ran -> 0 }T
T{ s" a b ≤ explicit: h1 b a ≤ explicit: h2 a b ≤ b a ≤ ∧" st
   s" ' And.intro by-apply a b = by-show" tactic-ran -> 445 }T
T{ s" b a ≤ explicit: h a b ≥" st s" a by-show" tactic-ran -> 96 }T
T{ prop mvar ' lf-open-mvar-free code1 -> thrown-unsupported }T
T{ nat dup lf-open-mvar-free = -> true }T
T{ s" a b ≤ explicit: h1 b a ≤ explicit: h2 a b ≤ b a ≤ ∧" st
   s" ' And.intro by-apply by-swap ' h2 by-exact ' h1 by-exact" tactic-ran -> 0 }T
T{ s" a b ≤ explicit: h a b ≤" st s" by-swap" tactic-ran -> 446 }T
T{ s" a b ≤ explicit: h b a ≤ explicit: h2 a b ≤" st s" ' h by-specialize by-assumption"
   tactic-ran -> 0 }T
T{ s" a b ≤ explicit: h a b ≤" st s" ' Nat.le_refl a $ by-specialize" tactic-ran -> 447 }T
: lam-body? ( -- flag )   \ getLambdaBody of fun x : Nat => x
  nat 0 lf-term-bvar lf-made! dup >r lf-term-lam lf-made! lf-meta-lambda-body r> = ;
T{ lam-body? -> true }T
\ The messages' printers end at the first part that does not print.
lf-tac-forget
T{ -1 nat 2 ' tch-pair. lf-tac-detail-n lf-tac-forget -1 nat 2 ' tch-many. lf-tac-detail-n -> }T
lf-tac-forget
T{ s" a b ≤ explicit: h a b ≤" st s" ' h by-revert by-intro: k ' k by-exact" tactic-ran -> 0 }T
T{ s" a b ≤ explicit: h a b ≤" st s" ' Nat.le_refl by-revert" tactic-ran -> 389 }T
T{ s" b a ≤ explicit: h a b ≥" st s" ' GE.ge by-delta ' h by-exact" tactic-ran -> 0 }T
T{ s" b a ≤ explicit: h a b ≥" st s" ' Ne by-delta" tactic-ran -> 448 }T
T{ s" b a ≤ explicit: h a b ≥" st s" ' h by-delta" tactic-ran -> 99 }T
T{ s" False explicit: h a b =" st s" by-contradiction" tactic-ran -> 0 }T
T{ s" a b = explicit: h b a =" st s" by-contradiction" tactic-ran -> 449 }T
T{ s" a b ≤ explicit: h False explicit: h2 a b =" st s" by-contradiction" tactic-ran -> 99 }T
T{ s" a a =" st s" by-trivial" tactic-ran -> 0 }T
T{ s" False explicit: h a b =" st s" by-trivial" tactic-ran -> 0 }T
T{ s" a b = explicit: h b a =" st s" by-trivial" tactic-ran -> 381 }T
T{ s" a a ≤ explicit: h a a ≤" st s" by-trivial" tactic-ran -> 99 }T
T{ s" True True ∧" st s" by-trivial" tactic-ran -> 0 }T
: deep ( n -- c-addr u )   \ True ∧ (True ∧ ... ): n + 1 Trues, n ∧
  0 stmt# ! dup 1+ 0 ?do s" True " stmt+ loop 0 ?do s" ∧ " stmt+ loop stmt stmt# @ ;
T{ 40 deep s" by-trivial" tactic-ran -> 99 }T
T{ s" a b ≤ ¬ explicit: h a b ≤ explicit: h2 a b =" st s" ' h by-absurd ' h2 by-exact"
   tactic-ran -> 0 }T
T{ s" a b ≤ explicit: h a b ≤ ¬ explicit: h2 a b =" st s" ' h by-absurd by-assumption"
   tactic-ran -> 0 }T
T{ s" a b ≤ explicit: h a b ≤ explicit: h2 a b =" st s" ' h by-absurd by-assumption"
   tactic-ran -> 381 }T
lf-tac-forget
.( batch-a test.fs: all tests passed) cr
bye

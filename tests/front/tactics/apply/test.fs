\ Unit tests of the goal layer's apply and its helpers (slice a2-iii;
\ src/front/meta-tactic/apply.fs, goal.fs, telescope.fs's bounded
\ telescope and lf-expected-num-args), over the S2 slice and its
\ elaboration data in an authoring run, for what the .lf files of
\ check.py cannot write yet (a goal with a binder, an instance binder), by
\ the classes of docs/development/TEST_COVERAGE_REVIEW.md: 1. outcomes:
\ a later argument count that fits, an instance found, an instance not
\ found (error 125), an unchanged and a changed head-beta type, the three
\ tag cases and hygienic tags; 2. malformed input: an assigned goal;
\ 3. stack effects (each T{ }T checks the depth); 6. state: a count
\ that does not fit leaves no assignment (lf-commit-when); 7. regression
\ pins: Lean's terms (tests/front/tactics/goal-layer.lean's ap_later,
\ which natural LeanForth cannot state yet: @Nat.le_succ_of_le a b).
\ Error 380 and the goal order are pinned end to end (check.py).
\ Nothing here accepts a theorem: only the kernel's check does.
require ../../../support/tester.fs
require ../../../../src/main.fs
decimal

4000000 lf-term-capacity! drop  100000 lf-cref-capacity! drop
T{ s" tests/front/s2-slice.ndjson" true lfc-library-open -> outcome-ok }T
T{ s" tests/front/s2-slice.elab.ndjson" lfc-elab-file! lfc-elab-read lfc-rooms
   -> outcome-ok outcome-ok }T
lf-author-begin
: made ( x outcome -- x ) ok? 0= abort" apply test: not made" ;
: nat ( -- t ) s" Nat" lf-mk-const0 ;
: binder ( type c-addr u -- fvar )
  lfa-intern swap lf-lctx-local made tuck swap 0 lf-local-new made
  lf-mctx-view swap lf-view-push made lf-mctx-view! ;
: code1 ( x xt -- code ) catch dup if nip then ;
: le ( a b -- t ) >r >r s" LE.le" 0 lf-mk-const1 nat lf-mk-app s" instLENat" lf-mk-const0
  lf-mk-app r> lf-mk-app r> lf-mk-app ;
: succ ( a -- t ) s" Nat.succ" lf-mk-const0 swap lf-mk-app ;
: goal ( type -- goal ) 0 lf-mctx-view lf-goal-new made ;
: goal-value ( goal -- e ) lf-instantiate! ;
: c-fresh ( c-addr u -- e ) lfa-intern lf-menv-find made lf-meta-const-fresh made ;
nat s" a" binder constant fa
nat s" b" binder constant fb

\ ---- lf-expected-num-args (getExpectedNumArgsAux) and the bounded telescope.
T{ nat lf-expected-num-args -> 0 false }T
T{ s" Nat.le_succ_of_le" c-fresh lf-infer! lf-expected-num-args -> 3 false }T
T{ nat mv-natural lf-mvar-new made lf-expected-num-args -> 0 true }T   \ ?P: a head metavariable
T{ lf-mctx-marks -> 0 }T   \ the counting telescope rolled back
: count+ ( n mvar kind -- n' ) 2drop 1+ ;
: bounded ( max -- n body ) >r 0 s" Nat.le_succ_of_le" c-fresh lf-infer! -1 r> ['] count+
  lf-forall-meta-bounded-telescope ;
T{ 0 bounded lf-term-pi? -> 0 true }T
T{ 2 bounded lf-term-pi? -> 2 true }T
T{ 3 bounded lf-term-pi? -> 3 false }T
T{ 9 bounded lf-term-pi? -> 3 false }T

\ ---- apply where a later count fits: a ≤ b → a ≤ b + 1 (as Nat.succ b)
\ by Nat.le_succ_of_le {n m} (h : n ≤ m) : n ≤ m.succ. Counts 2 to 3
\ (3 less the goal's 1): 2 fits, no goal left; the term is Lean's
\ @Nat.le_succ_of_le a b.
\ (The pi's binder recorded as the elaborator records a statement's: a
\ telescope refuses a binder of unknown kind, telescope.fs.)
: pi-recorded ( pi -- pi ) dup s" h" lfa-intern lf-binder-default lf-pres-binder! made ;
: later-goal ( -- goal ) fa fb le fa fb succ le lf-term-pi lf-made! pi-recorded goal ;
: later-lean ( -- e ) s" Nat.le_succ_of_le" lf-mk-const0 fa fb 2 lf-mk-app-n ;
T{ later-goal dup s" Nat.le_succ_of_le" c-fresh lf-goal-apply swap goal-value later-lean
   lf-meta-eqv -> 0 true outcome-ok }T
\ The same goal and Nat.le_succ: no count fits (error 380 needs a step
\ running, so here the throw), and nothing is left assigned.
T{ later-goal dup s" Nat.le_succ" c-fresh ' lf-goal-apply catch nip nip swap
   lf-goal-assigned? -> lf-author-throw false }T
lf-tac-forget

\ ---- synthAppInstances: @instHAdd {α} [Add α] on HAdd Nat Nat Nat; α by
\ isDefEq, the instance found (instAddNat), no goal left.
: hadd ( t -- t' ) >r s" HAdd" 0 0 0 3 lf-mk-const r@ lf-mk-app r@ lf-mk-app r> lf-mk-app ;
: inst-lean ( -- e ) s" instHAdd" 0 lf-mk-const1 nat lf-mk-app s" instAddNat" lf-mk-const0
  lf-mk-app ;
T{ nat hadd goal dup s" instHAdd" c-fresh lf-goal-apply swap goal-value inst-lean lf-meta-eqv
   -> 0 true outcome-ok }T
\ No instance: @instHAppendOfAppend {α} [Append α] on HAppend Nat Nat Nat
\ needs Append Nat, which has none (Lean's "failed to synthesize"): error
\ 125 (thrown: no step running). (Add Bool would try a candidate the
\ slice's data leaves out: unsupported, synth.fs's 119.)
: happend ( t -- t' ) >r s" HAppend" 0 0 0 3 lf-mk-const r@ lf-mk-app r@ lf-mk-app r> lf-mk-app ;
T{ nat happend goal s" instHAppendOfAppend" c-fresh ' lf-goal-apply catch nip nip
   lf-author-code -> lf-author-throw 125 }T
T{ s" Bool" lf-mk-const0 hadd goal s" instHAdd" c-fresh ' lf-goal-apply catch nip nip
   lf-synth-error -> -4205 119 }T
lf-tac-forget

\ ---- An assigned goal is a fault (checkNotAssigned), thrown invalid.
: solved ( -- goal ) nat goal dup s" Nat.zero" lf-mk-const0 lf-mvar-assign made ;
T{ solved s" Nat.zero" c-fresh ' lf-goal-apply catch nip nip -> -4201 }T

\ ---- headBetaType: a goal of type (fun x : Nat => x) a (the type need
\ not be a type here) gives a new goal of type a, a synthetic opaque one
\ as the old, which is assigned it; an unchanged type gives the goal itself.
: idf ( -- lam ) nat 0 lf-term-bvar lf-made! lf-term-lam lf-made! ;
: beta-pair ( -- old new ) idf fa lf-mk-app goal dup lf-goal-head-beta-type ;
: type@ ( goal -- t ) lf-mvar-type drop ;
: kind@ ( goal -- kind ) lf-mvar-kind drop ;
T{ nat goal dup lf-goal-head-beta-type = -> true }T
T{ beta-pair <> -> true }T
T{ beta-pair nip dup type@ fa = swap kind@ mv-opaque = -> true true }T
T{ beta-pair swap goal-value = -> true }T

\ ---- appendTag: parent ++ tag, its macro scopes erased; anonymous gives
\ the parent; a hygienic parent keeps its scopes after (Name.modifyBase:
\ Lean's appendTag `x._@.M._hyg.1 `left is x.left._@.M._hyg.1, and
\ appendTag `zero `a._@.Init._hyg.5 is zero.a).
: tagged ( c-addr u -- goal ) lfa-intern nat goal tuck swap lf-mvar-tag! made ;
: tag@ ( goal -- name ) lf-mvar-tag drop ;
: succ-tag ( -- name ) s" succ" lfa-intern ;
T{ s" left" tagged dup succ-tag lf-goal-tag-append tag@ s" succ.left" lfa-intern = -> true }T
T{ nat goal dup succ-tag lf-goal-tag-append tag@ succ-tag = -> true }T
T{ s" a.b" tagged dup succ-tag lf-goal-tag-append tag@ s" succ.a.b" lfa-intern = -> true }T
T{ s" a._@.Init._hyg.5" tagged dup s" zero" lfa-intern lf-goal-tag-append tag@
   s" zero.a" lfa-intern = -> true }T
T{ s" left" tagged dup s" x._@.M._hyg.1" lfa-intern lf-goal-tag-append tag@
   s" x.left._@.M._hyg.1" lfa-intern = -> true }T
\ The name store refusing the new tag (no room): thrown full (-4206),
\ the goal's tag unchanged.
: names-full ( -- ) lf-name-count @ lf-name-capacity! drop ;
: names-back ( cap -- ) lf-name-capacity! drop ;
: full-append ( goal parent -- code )
  lf-name-capacity >r names-full ['] lf-goal-tag-append catch nip nip r> names-back ;
T{ s" right" tagged dup s" fresh9" lfa-intern full-append swap tag@ s" right" lfa-intern =
   -> -4206 true }T
\ ---- A type whose conclusion is a metavariable (Lean's hasMVarHead):
\ the range is numArgs alone. Lean applies h : ?P to a ≤ b with no
\ argument, ?P := a ≤ b; LeanForth's isDefEq answers ?P =?= a ≤ b not
\ supported yet here (a gap, plan 9.4.8l L): unsupported, never accepted.
: prop ( -- t ) 0 lf-term-sort lf-made! ;
prop mv-natural lf-mvar-new made constant ?p
?p s" h" binder constant fh
T{ fa fb le goal dup fh ' lf-goal-apply catch nip nip swap lf-goal-assigned? -> -4205 false }T
\ ---- getMVarsNoDelayed is not ported: e that is still an unassigned
\ metavariable after apply (?x : Nat on a goal Nat) is not supported yet
\ (error 99, thrown: no step running), never a goal left out silently.
T{ nat goal nat mv-natural lf-mvar-new made ' lf-goal-apply catch nip nip lf-author-code
   -> lf-author-throw 99 }T
lf-tac-forget

\ ---- synthAppInstances and appendParentTag on hypotheses whose binders
\ are recorded as Lean's (review tactic-a2ii B1; the Lean twins were run
\ with pinned Lean 4.35.0, their answers quoted).
: rec ( pi c-addr u kind -- pi ) >r lfa-intern over swap r> lf-pres-binder! made ;
: pit ( dom body -- pi ) lf-term-pi lf-made! ;
: bv ( i -- t ) lf-term-bvar lf-made! ;
: type0 ( -- t ) nat lf-infer! ;
: true0 ( -- t ) s" True" lf-mk-const0 ;
: add ( t -- t' ) s" Add" 0 lf-mk-const1 swap lf-mk-app ;
: le-by ( inst a b -- t ) >r >r s" LE.le" 0 lf-mk-const1 nat lf-mk-app swap lf-mk-app
  r> lf-mk-app r> lf-mk-app ;
: hyp ( type -- fvar ) s" h" binder ;
\ Error 384: the instance argument fixed by isDefEq (⟨Nat.lt⟩) is not
\ defeq the instance found (instLENat). Lean, for
\   example (a b : Nat) (h : ∀ [i : LE Nat], @LE.le Nat i a b) :
\       @LE.le Nat ⟨Nat.lt⟩ a b := by apply h
\ answers "Tactic `apply` failed: failed to assign synthesized instance".
: le-lt ( -- t ) s" LE.mk" 0 lf-mk-const1 nat lf-mk-app s" Nat.lt" lf-mk-const0 lf-mk-app ;
: inst-hyp ( -- fvar )
  s" LE" 0 lf-mk-const1 nat lf-mk-app 0 bv fa fb le-by pit s" i" lf-binder-instance rec hyp ;
T{ le-lt fa fb le-by goal dup inst-hyp ' lf-goal-apply catch nip nip lf-author-code
   rot lf-goal-assigned? -> lf-author-throw 384 false }T
lf-tac-forget
\ The second round: [i : Add γ] is not found while γ is open; [j : HAdd
\ Nat Nat γ] is, and fixes γ (an out-parameter); i is found in the round
\ after. Lean, for
\   example (h : ∀ {γ : Type} [i : Add γ] [j : HAdd Nat Nat γ], True) :
\       True := by apply h
\ accepts @h Nat instAddNat (@instHAdd Nat instAddNat).
: hadd3 ( t -- t' ) >r s" HAdd" 0 0 0 3 lf-mk-const nat lf-mk-app nat lf-mk-app r> lf-mk-app ;
: rounds-hyp ( -- fvar )
  type0  0 bv add  1 bv hadd3 true0 pit s" j" lf-binder-instance rec
  pit s" i" lf-binder-instance rec  pit s" c" lf-binder-implicit rec hyp ;
: rounds-lean ( h -- e ) nat lf-mk-app s" instAddNat" lf-mk-const0 tuck lf-mk-app
  s" instHAdd" 0 lf-mk-const1 nat lf-mk-app rot lf-mk-app lf-mk-app ;
T{ true0 goal rounds-hyp 2dup lf-goal-apply run-count rot goal-value rot rounds-lean
   lf-meta-eqv -> 0 true outcome-ok }T
\ appendParentTag under a tagged goal indexes the binder kinds as the
\ filtered list: of h1 and h2 (α and i assigned), h2 sits at i's index,
\ an instance binder, so it keeps its own tag. Lean, for
\   def tg (n : Nat) (h : ∀ {α : Type} [i : Add α] (h1 h2 : True), HAdd α α α) :
\       HAdd Nat Nat Nat := by induction n with | zero => apply h; ...
\ shows the goals case zero.h1 and case h2.
: skip-hyp ( -- fvar )
  type0  0 bv add  true0  true0  3 bv hadd pit s" h2" lf-binder-default rec
  pit s" h1" lf-binder-default rec  pit s" i" lf-binder-instance rec
  pit s" al" lf-binder-implicit rec hyp ;
: zero-goal ( -- goal ) nat hadd goal dup s" zero" lfa-intern lf-mvar-tag! made ;
T{ zero-goal skip-hyp lf-goal-apply dup run-count over 0 run@ tag@ s" zero.h1" lfa-intern =
   rot 1 run@ tag@ s" h2" lfa-intern = -> 2 true true }T
lf-tac-forget
\ elabTermForApply's term that is still a metavariable (Lean then
\ synthesizes; not ported): error 99. No LeanForth term elaborates to a
\ bare metavariable yet, so the elaborator is stood in for.
: elab-mvar ( node mvar-type postpone? -- e outcome ) 2drop drop nat mv-natural lf-mvar-new ;
' lf-tac-elab defer@ constant real-elab
' elab-mvar is lf-tac-elab
: num-node ( -- node ) syn-k-num 0 syn-new drop 0 syn-a! ;
T{ num-node ' lf-tac-elab-for-apply catch nip lf-author-code -> lf-author-throw 99 }T
lf-tac-forget
real-elab is lf-tac-elab
\ isDefEqApply under approxDefEq (review tactic-a2ii B2): congrArg's
\ conclusion ?f ?a₁ = ?f ?a₂ meets Nat.succ a = Nat.succ b only by
\ first-order approximation (foApprox). Lean, for
\   theorem ap_congr (a b : Nat) (h : a = b) : Nat.succ a = Nat.succ b := by
\     apply congrArg; exact h
\ gives @congrArg.{1, 1} Nat Nat a b Nat.succ h: one goal, ?h, here.
: eq-nat ( x y -- t ) >r >r s" Eq" nat lf-level! lf-mk-const1 nat lf-mk-app r> lf-mk-app
  r> lf-mk-app ;
: congr-lean ( h -- e ) >r s" congrArg" nat lf-level! dup 2 lf-mk-const nat lf-mk-app
  nat lf-mk-app fa lf-mk-app fb lf-mk-app s" Nat.succ" lf-mk-const0 lf-mk-app r> lf-mk-app ;
T{ fa succ fb succ eq-nat goal dup s" congrArg" c-fresh lf-goal-apply dup run-count swap
   0 run@ rot goal-value swap congr-lean lf-meta-eqv -> 1 true outcome-ok }T
.( apply test.fs: all tests passed) cr
bye

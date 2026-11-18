\ Unit tests of the goal layer's apply and its helpers (slice a2-iii;
\ src/front/meta-tactic/apply.fs, goal.fs, telescope.fs's bounded
\ telescope and lf-expected-num-args), over the S2 slice and its
\ elaboration data in an authoring run, for what the .lf files of
\ check.py cannot write yet (a goal with a binder, an instance binder), by
\ the classes of docs/development/TEST_COVERAGE_REVIEW.md: 1. outcomes:
\ a later argument count that fits, an instance found, an instance not
\ found (error 125), an unchanged and a changed head-beta type, the three
\ tag cases; 2. malformed input: an assigned goal, a tag of two parts;
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

\ ---- appendTag: tag.suffix; anonymous gives the parent; two parts: unsupported.
: tagged ( c-addr u -- goal ) lfa-intern nat goal tuck swap lf-mvar-tag! made ;
: tag@ ( goal -- name ) lf-mvar-tag drop ;
: succ-tag ( -- name ) s" succ" lfa-intern ;
T{ s" left" tagged dup succ-tag lf-goal-tag-append tag@ s" succ.left" lfa-intern = -> true }T
T{ nat goal dup succ-tag lf-goal-tag-append tag@ succ-tag = -> true }T
T{ s" a.b" tagged succ-tag ' lf-goal-tag-append catch nip nip -> -4205 }T
.( apply test.fs: all tests passed) cr
bye

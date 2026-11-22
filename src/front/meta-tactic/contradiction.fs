\ MVarId.contradiction, the goal operation of the contradiction tactic
\ (plan row TB2, tactic batch 1), a port of Lean 4.35.0's
\ src/lean/Lean/Meta/Tactic/Contradiction.lean:142-229 (contradictionCore
\ with the default configuration: useDecide, emptyType, searchFuel 16,
\ genDiseq off) for the rules that need no case split:
\   lf-goal-contradiction ( goal -- )  in goal's context (checkNotAssigned
\       first), each local, the oldest first, implementation details passed
\       over, tried by Lean's tests in Lean's order; the first that closes
\       the goal assigns it, T goal's type as stored:
\       1. h : ¬p (app-builder.fs's lf-match-not?: Not p, or p -> False,
\          also after whnf) and a local h' : p (assumption.fs's
\          lf-local-index-with-type?, the newest, plain isDefEq):
\          False.elim.{u} T (h h') (mkFalseElim);
\       2. h : Nat.hasNotBit m i: not ported (99);
\       3. h : x ≠ x (lf-match-ne?: Ne, or ¬ an equation) with x and its
\          other side defeq: absurd.{u} (x = x) T (Eq.refl x) h (mkAbsurd);
\       4. h : a = b (lf-match-eq?) or HEq a b (lf-match-heq?), a and b
\          both constructor applications (isConstructorApp?, on the term,
\          then after whnf; a literal is Nat.zero or Nat.succ) of
\          different constructors: noConfusion is not ported (99); the
\          same constructor, or a side that is none, passes on (the
\          constructor's argument count is not checked: a partial
\          application of two different ones answers 99 too, where Lean
\          passes on);
\       5. h : p, p with no free variable (as stored and instantiated)
\          and no metavariable: mkDecide p (app-builder.fs's lf-mk-decide)
\          put in whnf at default transparency; Bool.false closes the goal
\          with absurd.{u} p T h (of_decide_eq_false p I (Eq.refl d)), d
\          the decide term, I its instance; a Lean error there (no
\          instance, p no proposition: rejected) passes on, as Lean's
\          catch does; unsupported, no room or no fuel is thrown on;
\       6. unless h is an equation or HEq, h's type through whnfD an
\          inductive type with no constructor or with indices
\          (isElimEmptyInductiveCandidate): elimEmptyInductive's cases is
\          not ported (99), whatever it would find (a ≤ b is one: Nat.le
\          has an index).
\       Before the locals, nestedFalseElim (the goal's type holding
\       False.elim applied to a proof with no loose bound variable) is not
\       ported: a type that holds the constant False.elim answers 99. No
\       local closes the goal: error 449, Lean's throwTacticEx with no
\       message, "Tactic `contradiction` failed" and the goal.
\ Lean call list: withContext -> lf-with-goal (meta-must.fs);
\ checkNotAssigned -> lf-goal-not-assigned (goal.fs); matchNot?, matchNe?,
\ matchEq?, matchHEq? -> lf-match-not?, lf-match-ne?, lf-match-eq?,
\ lf-match-heq? (app-builder.fs); findLocalDeclWithType? ->
\ lf-local-index-with-type? (assumption.fs); mkFalseElim, mkAbsurd,
\ mkEqRefl, mkDecide -> lf-mk-false-elim, lf-mk-absurd, lf-mk-eq-refl,
\ lf-mk-decide (app-builder.fs); whnfD -> lf-whnf-d!; matchConstInduct ->
\ lf-match-const-induct (meta-must.fs); throwTacticEx -> lf-tac-ex
\ (tactic-msg.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: mcd-frames (a frame per call open, meta-must.fs's lf-with-record),
\ in the checker context (ADR 0009); no other. Loads in decimal whatever
\ BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/slab.fs
require ../../lib/find.fs
require ../../lib/context.fs
require ../../author/errors.fs
require ../../core/input.fs
require ../../core/literals.fs
require ../../core/name-equal.fs
require ../../core/constant-term-boundary.fs
require ../mvars.fs
require ../lctx-views.fs
require ../meta-env.fs
require ../meta-spine.fs
require ../term-eqv.fs
require ../term-find.fs
require ../tactic-run.fs
require ../tactic-msg.fs
require ../meta-must.fs
require ../app-builder.fs
require ./goal.fs
require ./assumption.fs

449 outcome-invalid s" Tactic `contradiction` failed" lfa-code: lfa-e-contradiction

begin-structure /mcd
  field: mcd-goal        \ the goal
  field: mcd-equation    \ the local's type is an equation or HEq (isEq, isHEq)
end-structure
/mcd context-slab: mcd-frames
: mcd ( -- frame ) mcd-frames slab-last ;
: mcd-target ( -- t ) mcd mcd-goal @ lf-goal-type ;
: mcd-close ( e -- true ) mcd mcd-goal @ swap lf-mvar-assign lf-must true ;
: mcd-fvar ( k -- fvar ) lf-mctx-fvar ;
: mcd-type ( k -- t ) mcd-fvar lf-fvar-type ;
\ A rule not ported: lfa-e-tac-form lf-tac-fail (99, with the goals).

\ ---- 1. h : ¬p and h' : p.
: mcd-partner ( k p -- k e true | k false )
  lf-local-index-with-type? 0= if false exit then
  over mcd-fvar swap mcd-fvar lf-mk-app true ;
: mcd-not-pair ( k -- k flag )
  dup mcd-type lf-match-not? 0= if false exit then mcd-partner 0= if false exit then
  mcd-target swap lf-mk-false-elim mcd-close ;

\ ---- 2. Nat.hasNotBit (refutableHasNotBit?): not ported.
: mcd-bit ( k -- k )
  dup mcd-type 2 s" Nat.hasNotBit" lf-meta-app-of? if lfa-e-tac-form lf-tac-fail then ;

\ ---- 3. h : x ≠ y, x and y defeq: absurd T (Eq.refl x) h.
: mcd-absurd ( hp hnp -- true ) mcd-target -rot lf-mk-absurd mcd-close ;
: mcd-refl ( k x -- k true ) lf-mk-eq-refl over mcd-fvar mcd-absurd ;
: mcd-ne ( k -- k flag )
  dup mcd-type lf-match-ne? 0= if false exit then
  rot drop over swap lf-defeq! if mcd-refl else drop false then ;

\ ---- 4. Two constructors (matchConstructorApp?): the same passes on,
\ different ones would be noConfusion (not ported).
: mcd-lit-ctor ( lit -- name )
  lf-term-second@ if s" Nat.succ" else s" Nat.zero" then lfa-intern ;
: mcd-ctor-const ( const -- name true | false )
  lf-const-name dup lf-menv-find ok-then? 0= if 2drop false exit then
  lf-menv-kind lf-kind-constructor = dup 0= if nip then ;
: mcd-ctor-at ( e -- name true | false )
  dup lf-lit-leaf? if mcd-lit-ctor true exit then
  lf-meta-app-head dup lf-term-const? if mcd-ctor-const else drop false then ;
: mcd-ctor? ( e -- name true | false )
  dup mcd-ctor-at if nip true exit then lf-whnf! mcd-ctor-at ;
: mcd-ctors ( a b -- )
  mcd-ctor? 0= if drop exit then swap mcd-ctor? 0= if drop exit then
  lf-name-same? 0= if lfa-e-tac-form lf-tac-fail then ;
: mcd-equation! ( flag -- ) mcd mcd-equation ! ;
: mcd-eq ( k -- k )
  false mcd-equation! dup mcd-type lf-match-eq? 0= if exit then
  rot drop true mcd-equation! mcd-ctors ;
: mcd-heq ( k -- k )
  dup mcd-type lf-match-heq? 0= if exit then nip rot drop true mcd-equation! mcd-ctors ;

\ ---- 5. decide p reduces to false.
: mcd-closed? ( t -- flag )
  dup lf-meta-has-fvar? if drop false exit then
  lf-instantiate! dup lf-meta-has-fvar? swap lf-meta-has-mvar? lf-must or 0= ;
: mcd-dec ( t -- d r ) lf-mk-decide dup lf-whnf-d! ;
: mcd-try-decide ( t -- d r true | false )
  ['] mcd-dec 1 2 lf-meta-catch dup outcome-rejected = if drop 2drop false exit then
  lf-must true ;
: mcd-hn ( d -- hn )
  s" of_decide_eq_false" lf-mk-const0 swap dup lf-meta-args2 rot lf-mk-eq-refl
  3 lf-mk-app-n ;
: mcd-refuted ( k d -- k true ) mcd-hn over mcd-fvar swap mcd-absurd ;
: mcd-decide ( k -- k flag )
  dup mcd-type dup mcd-closed? 0= if drop false exit then
  mcd-try-decide 0= if false exit then
  s" Bool.false" lf-meta-const-named? 0= if drop false exit then mcd-refuted ;

\ ---- 6. An empty inductive type or an indexed family: cases, not ported.
: mcd-data ( d -- data ) lf-menv-data ?dup 0= if lfa-e-tac-form lf-tac-fail 0 then ;
: mcd-candidate? ( t -- flag )
  lf-whnf-d! lf-meta-app-head lf-match-const-induct 0= if false exit then
  mcd-data dup lf-ity-ctors@ nip 0= swap lf-ity-indices cells + @ 0> or ;
: mcd-empty ( k -- k )
  mcd mcd-equation @ if exit then
  dup mcd-type mcd-candidate? if lfa-e-tac-form lf-tac-fail then ;

\ ---- The locals, oldest first; nestedFalseElim before them.
: mcd-rules ( k -- flag )
  mcd-not-pair if drop true exit then mcd-bit mcd-ne if drop true exit then
  mcd-eq mcd-heq mcd-decide if drop true exit then mcd-empty drop false ;
: mcd-local? ( x k -- x flag ) dup lf-local-detail-at? if drop false else mcd-rules then ;
: mcd-locals ( -- flag )
  0 lf-mctx-view lf-view-count ['] mcd-local? find-index dup if nip then ;
: mcd-elim? ( leaf -- flag ) s" False.elim" lf-meta-const-named? ;
: mcd-nested ( -- )
  mcd-target ['] mcd-elim? lf-term-holds? lf-must if lfa-e-tac-form lf-tac-fail then ;
: mcd-failed ( -- ) mcd mcd-goal @ lfa-e-contradiction lf-tac-ex ;
: mcd-run ( -- ) mcd-nested mcd-locals 0= if mcd-failed then ;
: mcd-framed ( goal -- ) dup mcd mcd-goal ! ['] mcd-run lf-with-goal ;
: lf-goal-contradiction ( goal -- )
  lf-goal-not-assigned mcd-frames ['] mcd-framed lf-with-record ;
base !   \ the BASE this file was loaded with

\ Substitution of the tactic library (plan row TB2, piece E, slice E2a;
\ docs/design/TACTIC_PATTERNS.md sections 3-4): Lean 4.35.0's
\ Meta/Tactic/Subst.lean, an equation h : x = t or t = x used to replace
\ the free variable x by t in the goal and every hypothesis after it.
\ Each word throws on failure (meta-must.fs), Lean's errors as authoring
\ errors at the step running (throwTacticEx, Util.lean:43-49: "Tactic
\ `subst` failed: ..." and the goal after a blank line), as Lean's do.
\ Public words:
\   lf-subst-symm, lf-subst-skip ( -- flag )  substCore's flags: symm
\       (the variable is the equation's right side) and tryToSkip
\   lf-goal-subst-core ( goal h fs flags -- fs' goal' )  substCore
\       (:17-119) with clearH true (no Lean caller asks false; not
\       ported): in goal's context (checkNotAssigned first) h's type
\       instantiated, through matchEq? (app-builder.fs's lf-match-eq?)
\       an equation (else 475), a its left side (its right with symm) and
\       b the other; a a free variable (else 477) b does not depend on
\       (else 476); a, h and every later local depending on one reverted
\       in that order (revert.fs's lf-goal-revert-kept, preserveOrder) and
\       a and h introduced again keeping their names (goal.fs's
\       lf-goal-intro-kept: a hidden name stays hidden). With skip, when
\       nothing else was reverted and the goal depends on neither, both
\       cleared and fs given back. Else goal assigned Eq.rec (the goal
\       depending on h) or Eq.ndrec of the motive fun a h => T (symm), fun
\       a (_h : b = a) => T[_h.symm / h], or fun a => T (no dependence),
\       the minor premise a new goal of T[b / a][Eq.refl b / h] with the
\       goal's tag, the major h (symm) or h.symm; then h and a cleared, the
\       other reverted locals introduced again keeping their names (introNP),
\       and fs' fs with each of those to its new free variable, a to b and
\       h to h again (FVarSubst.insert, fvar-subst.fs)
\   lf-goal-heq-to-eq ( goal h -- h' goal' )  heqToEq (:122-137,
\       tryToClear true), in goal's context: h's type through whnf HEq α a
\       β b with α and β defeq gives a = b asserted with proof
\       eq_of_heq h under h's name, h tried for clearing, the new one
\       introduced (assert.fs's lf-goal-intro1-as: a hidden name stays
\       hidden); anything else gives h and goal
\   lf-goal-subst-eq ( goal h fs -- fs' goal' )  substEq (:173-199): heqToEq
\       first, then h's type through matchEq? an equation (else 478); its
\       right side through whnf a free variable: substCore with symm
\       when whnf left it as it was, else the reduced equation lhs = rhs'
\       asserted under h's name with proof h, introduced, h cleared (the
\       throwing clear) and substCore with symm on it (substReduced); else
\       the left side the same way without symm; else 478; skip always
\   lf-goal-subst-var ( goal x -- goal' )  substVar (:144-167), in goal's
\       context: x a let (isLet: a have is none) is 480; the oldest local not an
\       implementation detail whose type instantiated is an equation with x
\       alone on its right and a left free of x (symm), or alone on its
\       left and a right free of x; none is 479; substCore with skip
\   lf-goal-subst ( goal h -- goal' )  subst (:201-212), in goal's
\       context: h's type an equation: substEq; an HEq: heqToEq, then
\       substVar of h when it changed nothing, else substEq of the new
\       hypothesis (Lean's subst again, which finds an equation); anything
\       else: substVar of h
\   lf-goal-subst-vars ( goal -- goal' )  substVars (:276-292): subst
\       of each local of the goal's context in order under observing? (a
\       Lean error undone and forgotten, the next local tried; any other
\       failure thrown on), the first that succeeds starting again on its
\       goal, until none does (goal itself when none ever does)
\ Errors (Lean's text, catchable by try and observing?): 475 argument
\ must be an equality proof; 476 'x' occurs at, the term; 477 invalid
\ equality proof, it is not of the form (x = t) (or (t = x)), the type,
\ after WHNF, variable expected, but obtained, the side; 478 the same of
\ the form (x = t) or (t = x), the type; 479 did not find equation for
\ eliminating 'x'; 480 variable 'x' is a let-declaration; each with the
\ goal after a blank line. 475 and 477 no tactic reaches (substEq and
\ substVar call substCore only on what they checked).
\ Lean call list: withContext -> lf-with-goal, lf-goal-within;
\ matchEq?, matchHEq? -> lf-match-eq?, lf-match-heq-term?; instantiateMVars ->
\ lf-instantiate!; exprDependsOn -> lf-depends-on?; revert -> lf-goal-revert-kept;
\ introNP -> lf-goal-intro-kept; clear -> lf-goal-clear!; tryClear ->
\ lf-goal-try-clear; assert -> lf-goal-assert; intro1P ->
\ lf-goal-intro1-as; mkFreshExprSyntheticOpaqueMVar -> lf-goal-fresh;
\ mkEqRec, mkEqNDRec, mkEqSymm, mkEqRefl, mkEq, mkEqOfHEq -> app-builder.fs;
\ replaceFVar -> lf-replace-fvar; mkLambdaFVars -> lf-mk-lambda-fvars;
\ withLocalDeclD -> lf-with-local-decl; whnf -> lf-whnf!; isDefEq ->
\ lf-defeq!; Expr's == -> lf-meta-eqv; FVarSubst.insert -> lf-fsubst-insert.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: msc-frames (substCore's frame, one per call open, meta-must.fs's
\ lf-with-record) and mse-frames (heqToEq's and substEq's), in the
\ checker context (ADR 0009); no other. Loads in decimal whatever BASE
\ is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/runs.fs
require ../../lib/slab.fs
require ../../lib/bounds.fs
require ../../lib/context.fs
require ../../author/errors.fs
require ../mvars.fs
require ../lctx-views.fs
require ../goals.fs
require ../term-eqv.fs
require ../meta-must.fs
require ../app-builder.fs
require ../telescope.fs
require ../tactic-msg.fs
require ../fvar-subst.fs
require ./goal.fs
require ./revert.fs
require ./assert.fs

475 lfa-lean s" Tactic `subst` failed: argument must be an equality proof"
  lfa-code: lfa-e-subst-eq
476 lfa-lean s" Tactic `subst` failed:" lfa-code: lfa-e-subst-occurs
477 lfa-lean s" Tactic `subst` failed: invalid equality proof, it is not of the form"
  lfa-code: lfa-e-subst-side
478 lfa-lean s" Tactic `subst` failed: invalid equality proof, it is not of the form"
  lfa-code: lfa-e-subst-form
479 lfa-lean s" Tactic `subst` failed: did not find equation for eliminating"
  lfa-code: lfa-e-subst-none
480 lfa-lean s" Tactic `subst` failed: variable" lfa-code: lfa-e-subst-let

1 constant lf-subst-symm
2 constant lf-subst-skip

\ A term framed: indented, then the goal after a blank line (the detail of
\ 476 and 478); a name quoted after the first line's text.
: msb-framed ( goal term code -- )
  >r 0 ['] drop-ok rot 4 ['] lf-tac-framed-with. lf-tac-detail-n
  r> lf-tac-stop ;
\ matchEq? of a type instantiated (instantiateMVars of each side, which
\ gives the same nodes): its two sides.
: msb-sides? ( t -- lhs rhs true | false )
  lf-instantiate! lf-match-eq? dup if >r rot drop r> then ;

\ ---- substCore: a frame per call open (lf-with-record). Pairs of fields
\ stay next to each other, for cell-pair! and the binders' lambda:
\ goal and h, fs and flags (msc-framed), a and b (msc-var), x and y
\ (msc-lam).
begin-structure /msc
  field: msc-goal        \ the goal; once a and h are introduced again, that goal
  field: msc-h           \ the equation asked (hFVarIdOriginal)
  field: msc-fs          \ the substitution
  field: msc-flags       \ lf-subst-symm, lf-subst-skip
  field: msc-a           \ the variable eliminated (aFVarIdOriginal)
  field: msc-b           \ the term that replaces it
  field: msc-kept        \ the reverted locals (revert-kept's run)
  field: msc-x           \ a introduced again, and next to it
  field: msc-y           \ the motive's second binder (h again, or _h)
  field: msc-hx          \ h introduced again
  field: msc-dep         \ true: the goal depends on h (Eq.rec)
end-structure
/msc context-slab: msc-frames
: msc ( -- frame ) msc-frames slab-last ;
: msc-hx@ ( -- h ) msc msc-hx @ ;
: msc-x@ ( -- x ) msc msc-x @ ;
: msc-b@ ( -- b ) msc msc-b @ ;
: msc-flag? ( mask -- flag ) msc msc-flags @ and 0<> ;
: msc-symm? ( -- flag ) lf-subst-symm msc-flag? ;
2 constant msc-ah#   \ a and h, the first two reverted and introduced again
: msc-goal@ ( -- goal ) msc msc-goal @ ;
: msc-type ( -- t ) msc msc-h @ lf-fvar-type ;

\ ---- The equation: a the variable (477), b free of it (476).
: msc-form. ( x -- outcome )
  drop msc-symm? if s"  (t = x)" else s"  (x = t)" then lf-pp-emit outcome-ok ;
: msc-obtained. ( a -- outcome )
  s\" \nafter WHNF, variable expected, but obtained\n" rot lf-tac-line. ;
: msc-no-var ( a -- )
  0 ['] msc-form. lf-tac-inline msc-goal@ swap ['] msc-obtained. msc-type
  4 ['] lf-tac-framed-with. lf-tac-detail-n lfa-e-subst-side lf-tac-stop ;
: msc-occurs-at. ( -- outcome ) s"  occurs at" lf-pp-emit outcome-ok ;
: msc-occurs. ( a -- outcome ) lf-tac-quoted-after. ['] msc-occurs-at. ok-and ;
: msc-occurs ( a b -- )
  swap ['] msc-occurs. lf-tac-inline msc-goal@ swap lfa-e-subst-occurs msb-framed ;
: msc-ab ( -- a b )
  msc-type msb-sides? 0= if msc-goal@ lfa-e-subst-eq lf-tac-ex then
  msc-symm? if swap then ;
: msc-var ( a b -- )
  over lf-meta-fvar? 0= if drop msc-no-var then
  2dup swap lf-depends-on? lf-must if msc-occurs then msc msc-a cell-pair! ;

\ ---- revert #[a, h] true, then introNP 2: a and h again, names kept.
: msc-again ( goal1 kept -- )
  dup msc msc-kept ! msc-ah# lf-goal-intro-kept 0 run-pair@ dup msc msc-hx ! msc msc-y !
  msc msc-x ! msc msc-goal ! ;
: msc-reverted ( -- )
  msc-goal@ msc msc-a @ msc msc-h @ lf-run2 lf-goal-revert-kept msc-again ;
: msc-dep? ( fvar -- flag ) msc-goal@ lf-goal-type swap lf-depends-on? lf-must ;
\ skip: asked, nothing else reverted, the goal depending on neither.
: msc-skip? ( -- flag )
  lf-subst-skip msc-flag? msc msc-kept @ run-count msc-ah# = and
  dup if drop msc-x@ msc-dep? msc-hx@ msc-dep? or 0= then ;
: msc-cleared ( goal -- goal' ) msc-hx@ lf-goal-clear! msc-x@ lf-goal-clear! ;
: msc-skipped ( -- fs goal ) msc msc-fs @ msc-goal@ msc-cleared ;

\ ---- The motive, the minor premise's type and the major premise.
: msc-lam ( t n -- motive ) msc msc-x swap lf-mk-lambda-fvars ;
: msc-aux ( t hAux -- motive )
  dup msc msc-y ! lf-mk-eq-symm msc-hx@ swap lf-replace-fvar 2 msc-lam ;
: msc-aux-type ( -- t ) msc-b@ msc-x@ lf-mk-eq ;
: msc-aux-motive ( t -- motive )
  msc-aux-type s" _h" lfa-intern lf-binder-default ['] msc-aux lf-with-local-decl ;
: msc-motive ( t -- motive )
  msc msc-dep @ 0= if 1 msc-lam exit then
  msc-symm? if 2 msc-lam else msc-aux-motive then ;
: msc-refl ( t -- t' ) msc-hx@ msc-b@ lf-mk-eq-refl lf-replace-fvar ;
: msc-minor-type ( t -- t' )
  msc-x@ msc-b@ lf-replace-fvar msc msc-dep @ if msc-refl then ;
: msc-major ( -- h ) msc-hx@ msc-symm? 0= if lf-mk-eq-symm then ;
: msc-elim ( motive minor major -- e )
  msc msc-dep @ if lf-mk-eq-rec else lf-mk-eq-ndrec then ;

\ ---- The rest introduced again; fs' (each reverted local to its new
\ free variable, a to b, h to h again).
: msc-fs+ ( fvar e -- ) msc msc-fs @ -rot lf-fsubst-insert msc msc-fs ! ;
: msc-old ( i -- fvar ) msc-ah# + msc msc-kept @ swap run@ lf-local-fvar ;
: msc-var+ ( xs i -- xs ) 2dup run@ swap msc-old swap msc-fs+ ;
: msc-subst ( xs -- fs' )
  dup run-count 0 ?do i msc-var+ loop drop msc msc-a cell-pair@ msc-fs+
  msc msc-h @ msc-hx@ msc-fs+ msc msc-fs @ ;
: msc-rest ( goal -- goal' xs )
  msc msc-kept @ msc-ah# run-after lf-must dup run-count lf-goal-intro-kept ;
\ cont: goal assigned the eliminator, the minor premise cleared of h and a.
: msc-assigned ( minor -- )
  >r msc-goal@ lf-goal-type msc-motive r> msc-major msc-elim
  msc-goal@ swap lf-mvar-assign lf-must ;
: msc-minor ( -- minor ) msc-goal@ lf-goal-type msc-minor-type msc-goal@ lf-goal-fresh ;
: msc-cont ( -- fs' goal' )
  msc-hx@ msc-dep? msc msc-dep ! msc-minor dup msc-assigned msc-cleared
  msc-rest msc-subst swap ;
: msc-run ( goal -- fs' goal' )
  drop msc-ab msc-var msc-reverted msc-skip? if msc-skipped exit then
  msc-goal@ ['] msc-cont lf-with-goal ;
: msc-framed ( goal h fs flags -- fs' goal' )
  msc msc-fs cell-pair! msc msc-goal cell-pair! msc-goal@ ['] msc-run lf-goal-within ;
: lf-goal-subst-core ( goal h fs flags -- fs' goal' )
  msc-frames ['] msc-framed lf-with-record ;

\ ---- heqToEq and substEq: a frame per call open; goal and h next to each
\ other (mse-heq-framed's cell-pair!).
begin-structure /mse
  field: mse-goal        \ the goal
  field: mse-h           \ the hypothesis
  field: mse-fs          \ substEq's substitution
  field: mse-local       \ the hypothesis's local (its name and hidden flag)
end-structure
/mse context-slab: mse-frames
: mse ( -- frame ) mse-frames slab-last ;
: mse-goal@ ( -- goal ) mse mse-goal @ ;
: mse-h@ ( -- h ) mse mse-h @ ;
: mse-local! ( -- ) mse-goal@ lf-goal-view mse-h@ lf-view-local-of mse mse-local ! ;
: mse-type ( -- t ) mse-h@ lf-fvar-type ;
\ assert decl.userName type proof, and intro1P of the new hypothesis.
: mse-assert ( type proof -- goal' )
  mse-goal@ mse mse-local @ lf-local-name 2swap lf-goal-assert ;
: mse-intro ( goal -- goal' h' ) mse mse-local @ lf-goal-intro1-as ;
: mse-kept ( -- h goal ) mse-h@ mse-goal@ ;

\ heqToEq: HEq α a β b with α, β defeq made a = b, h tried for clearing.
: mse-to-eq ( a b -- h' goal' )
  lf-mk-eq mse-h@ lf-mk-eq-of-heq mse-assert mse-h@ lf-goal-try-clear mse-intro swap ;
: mse-heq-run ( -- h' goal' )
  mse-local! mse-type lf-match-heq-term? 0= if mse-kept exit then
  lf-heq-homogeneous? if lf-heq-sides mse-to-eq else drop mse-kept then ;
: mse-heq-framed ( goal h -- h' goal' )
  mse mse-goal cell-pair! mse-goal@ ['] mse-heq-run lf-with-goal ;
: lf-goal-heq-to-eq ( goal h -- h' goal' ) mse-frames ['] mse-heq-framed lf-with-record ;

\ substEq: the side whnf makes a variable, the reduced equation first
\ when whnf changed it (substReduced).
: mse-or. ( x -- outcome ) drop s"  (x = t) or (t = x)" lf-pp-emit outcome-ok ;
: mse-not-form ( -- )
  0 ['] mse-or. lf-tac-inline mse-goal@ mse-type lfa-e-subst-form msb-framed ;
: mse-core ( goal h flags -- fs' goal' )
  mse mse-fs @ swap lf-subst-skip or lf-goal-subst-core ;
: mse-plain ( flags -- fs' goal' ) >r mse-goal@ mse-h@ r> mse-core ;
: mse-reduced ( type flags -- fs' goal' )
  >r mse-h@ mse-assert mse-intro swap mse-h@ lf-goal-clear! swap r> mse-core ;
: mse-by-rhs ( lhs rhs rhs' -- fs' goal' )
  tuck lf-meta-eqv lf-must if 2drop lf-subst-symm mse-plain exit then
  lf-mk-eq lf-subst-symm mse-reduced ;
: mse-by-lhs ( lhs rhs lhs' -- fs' goal' )
  rot over lf-meta-eqv lf-must if 2drop 0 mse-plain exit then
  swap lf-mk-eq 0 mse-reduced ;
: mse-var? ( e -- e' flag ) lf-whnf! dup lf-meta-fvar? ;
: mse-sides ( -- lhs rhs ) mse-type lf-match-eq? 0= if mse-not-form then rot drop ;
: mse-eq-run ( -- fs' goal' )
  mse-local! mse-sides dup mse-var? if mse-by-rhs exit then drop
  over mse-var? if mse-by-lhs exit then drop 2drop mse-not-form ;
: mse-eq-framed ( goal h fs -- fs' goal' )
  mse mse-fs ! lf-goal-heq-to-eq mse mse-goal ! mse mse-h !
  mse-goal@ ['] mse-eq-run lf-with-goal ;
: lf-goal-subst-eq ( goal h fs -- fs' goal' )
  mse-frames ['] mse-eq-framed lf-with-record ;

\ ---- substVar: the oldest equation with x alone on a side (the right
\ first), the other side free of x; none 479, a let 480.
: msv-free? ( x e -- x flag ) over lf-depends-on? lf-must 0= ;
: msv-by ( x a b -- x flag ) >r over = if r> msv-free? else r> drop false then ;
\ side 1: x on the right (symm); 2: on the left; 0: neither.
: msv-side ( x t -- x side )
  msb-sides? 0= if 0 exit then
  2>r 2r@ swap msv-by if 2r> 2drop 1 exit then 2r> msv-by 2 and ;
: msv-local ( x k -- x side )
  dup lf-local-detail-at? if drop 0 exit then lf-mctx-fvar lf-fvar-type msv-side ;
: msv-has? ( x k -- x flag ) msv-local 0<> ;
: msv-find ( goal x -- goal x k )
  dup lf-mctx-view lf-view-count ['] msv-has? find-index 0= if
  lfa-e-subst-none lf-tac-ex-quoted then ;
: msv-let. ( x -- outcome ) drop s"  is a let-declaration" lf-pp-emit outcome-ok ;
: msv-is-let ( goal x -- )
  ['] lf-tac-quoted-after. lf-tac-inline 0 ['] msv-let. lf-tac-inline
  lfa-e-subst-let lf-tac-ex ;
: msv-let ( goal x -- goal x ) dup lf-fvar-let? if 2dup msv-is-let then ;
: msv-flags ( x k -- flags ) msv-local nip 1 = lf-subst-symm and lf-subst-skip or ;
: msv-run ( goal x -- goal' )
  msv-let msv-find tuck msv-flags swap lf-mctx-fvar swap 0 swap lf-goal-subst-core
  nip ;
: lf-goal-subst-var ( goal x -- goal' ) over ['] msv-run lf-with-goal ;

\ ---- subst: an equation, an HEq, or a variable.
: msb-eq ( goal h -- goal' ) 0 lf-goal-subst-eq nip ;
: msb-heq ( goal h -- goal' )
  over >r lf-goal-heq-to-eq swap over r> = if lf-goal-subst-var else msb-eq then ;
: msb-run ( goal h -- goal' )
  dup lf-fvar-type dup lf-match-eq? if 2drop 2drop msb-eq exit then
  lf-match-heq-term? if drop msb-heq else lf-goal-subst-var then ;
: lf-goal-subst ( goal h -- goal' ) over ['] msb-run lf-with-goal ;

\ ---- substVars: substSomeVar? again until it finds nothing, each local
\ of the goal's context in order under subst? (observing?: a Lean error
\ undone, its message forgotten, and the next tried; any other thrown on).
: msv-tried ( goal fvar -- goal' true | goal false )
  over >r ['] lf-goal-subst catch ?dup if nip nip lf-tac-forget-lean r> false exit then
  r> drop true ;
: msv-at ( goal k -- goal' true | goal false )
  over lf-goal-view swap lf-view-fvar ['] msv-tried lf-commit-when ;
: msv-some ( goal -- goal' true | goal false )
  dup lf-goal-view lf-view-count 0 ?do i msv-at if true unloop exit then loop false ;
: lf-goal-subst-vars ( goal -- goal' ) begin msv-some 0= until ;
base !   \ the BASE this file was loaded with

\ Asserting and replacing hypotheses (plan row TB2, tactic batch 1): Lean
\ 4.35.0's src/lean/Lean/Meta/Tactic/Assert.lean and Replace.lean. Each
\ word throws on failure (meta-must.fs), as Lean's do.
\ Public words:
\   lf-goal-assert ( goal name type val -- goal' )  MVarId.assert
\       (Assert.lean:22-31): val a proof of type; goal' a new synthetic
\       opaque goal of type (name : type) -> target, target goal's type
\       as stored, the binder explicit and named (present/binder-table.fs),
\       with goal's tag in goal's context (checkNotAssigned first); goal
\       assigned goal' val (have's goal operation, plan row TB2 batch 2)
\   lf-goal-replace ( goal fvar e type -- goal' )  MVarId.replace
\       (Replace.lean:73-80) with type given: the hypothesis fvar's name
\       given to a new hypothesis of type (instantiated) whose proof is e,
\       asserted as soon after fvar as type allows (assertAfter',
\       Assert.lean:89-118: after the newest local type names, fvar
\       itself when it names none later), then fvar cleared when nothing
\       depends on it (tryClear: lf-goal-clear refused keeps the goal).
\       assertAfter (70-83): the locals after that place reverted
\       (revert.fs's lf-goal-revert-after), the hypothesis asserted, and
\       it and they introduced again (intro1P, introNP: introN keeping
\       each binder's name, an inaccessible local's made inaccessible
\       again), goal' the result (specialize's goal operation)
\   lf-goal-replace-local-decl ( goal fvar new proof -- goal' fvar' )
\       MVarId.replaceLocalDecl (Replace.lean:94-97; plan row TB2 batch
\       3a, rw at h): proof : T = new, T fvar's type; MVarId.replace of
\       fvar by Eq.mp.{u} T new proof fvar (app-builder.fs's lf-mk-eq-mp)
\       of type new, as above (the new hypothesis where new allows, fvar
\       cleared unless something depends on it); fvar' the new hypothesis
\       (AssertAfterResult.fvarId: rwa's)
\   lf-goal-replace-local-decl-defeq ( goal fvar type -- goal' )
\       MVarId.replaceLocalDeclDefEq (Replace.lean:110-132; simp at h's
\       result without a proof): type definitionally equal to fvar's; goal
\       itself when they are Expr.equal (term-eqv.fs's lf-meta-equal?),
\       before or after instantiation. Lean keeps fvar and changes its
\       type; LeanForth's core keeps a free variable's type with it, so
\       (route 1 of the simp design's review) a new free variable fvar' of
\       type (instantiated) in fvar's place, with its name and kind
\       (lctx-views.fs's lf-view-refvar), goal' a new goal of goal's type,
\       kind and tag in that context, and goal assigned ?d fvar, ?d a new
\       synthetic opaque metavariable delayed-assigned fvar' := goal': once
\       instantiated, goal's value is goal''s with fvar' made fvar again,
\       Lean's term node for node. Not supported yet (thrown unsupported):
\       a hypothesis another local or the target depends on
\       (goals.fs's lf-goal-fvar-free)
\   lf-goal-assert-hyps ( goal run -- goal' )  MVarId.assertHypotheses
\       (Assert.lean:139-159): run a run of (local type value) triples,
\       each value a proof of its type; goal itself for none; else goal'
\       of type (n1 : t1) -> .. -> (nk : tk) -> target with goal's tag,
\       each name its local's, goal assigned goal' v1 .. vk (lf-goal-assert
\       of each, last first), and the k introduced again at once (introNP:
\       lf-goal-intro-n, an inaccessible local's name made inaccessible
\       again); simpGoal's (simp/goal.fs)
\   lf-goal-change-local-decl ( goal fvar type -- goal' )
\       MVarId.changeLocalDecl (Replace.lean:200-217, checkDefEq true;
\       change at h): fvar reverted (revert.fs; checkNotAssigned there);
\       the pi's domain must be definitionally equal to type (isDefEq at
\       the transparency in force; unequal is Lean's changeLocalDecl
\       error, which elabChange's check before it leaves unreachable: not
\       supported, thrown unsupported); the target that pi with domain
\       type, its binder's name and kind kept (replaceTargetDefEq: @id),
\       then introNP 1: the hypothesis again under its own name (an
\       inaccessible one stays so), goal' the result. Not supported yet
\       (thrown unsupported): a hypothesis another local depends on, which
\       revert takes along (Lean reintroduces them all)
\   lf-goal-intro1-as ( goal local -- goal' fvar )  intro1P after an
\       assert of the hypothesis local's name (heqToEq's and substEq's,
\       Subst.lean:132, :184; changeLocalDecl's introNP 1): introN 1
\       given local's name, or 0 (the binder's own name, made
\       inaccessible) when local's is inaccessible, so a hidden name
\       stays hidden; the binder's own kind; fvar the new hypothesis
\   lf-goal-try-clear ( goal fvar -- goal' )  MVarId.tryClear
\       (Clear.lean:48-51): goals.fs's lf-goal-clear, or goal itself when
\       it refuses (replace's, specialize's)
\   lf-goal-have-with ( goal name type val xt -- body )  the have term
\       as refine elaborates it (Elab/Binders.lean:745-860,
\       elabLetDeclAux: withLetDecl, the body, mkLetFVars #[x] body
\       with generalizeNondepLet false): in goal's context
\       (checkNotAssigned first, before xt runs) a new local name : type
\       := val, a have (its value hidden: Lean's nondep); xt ( goal --
\       body ) makes the body in the context with it (current while xt
\       runs); goal assigned have name : type := val; body
\       (telescope.fs's lf-mk-let-fvars, whose elimMVar makes a body that
\       is a goal ?b into ?n x, delayed-assigned ?b); the body given back
\       (suffices', whose body is its e)
\   lf-goal-have ( goal name type val -- goal' )  refine's
\       have name : type := val; ?_ (Init/Tactics.lean:942, refine_lift):
\       the same whose body is goal', a new synthetic opaque goal of
\       goal's type instantiated (lf-goal-target: getMainTarget) with
\       goal's tag (refine's one new goal, tagUntaggedGoals)
\   lf-goal-let ( goal name type val -- goal' )  refine's
\       let name : type := val; ?_ (Init/Tactics.lean:980): the same with
\       a let local, whose value later steps see
\   lf-goal-target ( goal -- type tag )  goal's type instantiated and tag
\ Not supported yet (thrown unsupported: the runner's 93): a type that
\ still holds an open metavariable
\ once instantiated (findMaxFVar would place the hypothesis after the
\ locals of its context), and what revert.fs and goal.fs's
\ lf-goal-intro-n refuse (a let, an instance binder, an implementation
\ detail among the reverted).
\ Lean call list: checkNotAssigned -> lf-goal-not-assigned (goal.fs);
\ mkForall -> lf-term-pi and lf-binder-named (app-builder.fs);
\ mkFreshExprSyntheticOpaqueMVar
\ -> lf-goal-fresh (goal.fs); assign -> lf-mvar-assign; revertAfter ->
\ lf-goal-revert-after (revert.fs); intro1P, introNP -> lf-goal-intro-n
\ (goal.fs); instantiateMVars -> lf-instantiate!; findMaxFVar -> mat-max;
\ tryClear -> lf-goal-clear (goals.fs); mkEqMP -> lf-mk-eq-mp; revert ->
\ lf-goal-revert; isDefEq -> lf-tac-defeq; replaceTargetDefEq ->
\ lf-goal-replace-target-defeq (goal.fs); introNP -> lf-goal-intro-n.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: mat-frames (a frame per call open, meta-must.fs's lf-with-record)
\ and mat-cells (introN's names and free variables, lf-with-cells), in
\ the checker context (ADR 0009); no other. Loads in decimal whatever
\ BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/slab.fs
require ../../lib/find.fs
require ../../lib/runs.fs
require ../../lib/context.fs
require ../../core/terms.fs
require ../../present/binder-table.fs
require ../mvars.fs
require ../lctx-views.fs
require ../goals.fs
require ../term-find.fs
require ../term-eqv.fs
require ../meta-must.fs
require ../app-builder.fs
require ../telescope.fs
require ./goal.fs
require ./revert.fs

\ ---- MVarId.assert: (name : type) -> target, goal assigned goal' val.
: mat-pi ( name type target -- pi ) lf-term-pi lf-made! swap lf-binder-named ;
: mat-goal-pi ( goal name type -- goal pi ) rot dup >r lf-goal-type mat-pi r> swap ;
: lf-goal-assert ( goal name type val -- goal' )
  >r rot lf-goal-not-assigned -rot mat-goal-pi over lf-goal-fresh tuck r> lf-mk-app
  lf-mvar-assign lf-must ;

\ ---- assertAfter and replace: a frame per call open.
begin-structure /mat
  field: mat-goal        \ the goal
  field: mat-old         \ the hypothesis replaced (tryClear's)
  field: mat-fvar        \ the local the new one follows
  field: mat-name        \ its name
  field: mat-type        \ its type, instantiated
  field: mat-val         \ its proof
  field: mat-n           \ the locals after mat-fvar
  field: mat-nondep      \ mat-let-with's: true for a have
  field: mat-xt          \ and its body's maker ( goal -- body )
end-structure
/mat context-slab: mat-frames
: mat ( -- frame ) mat-frames slab-last ;
1 cells context-slab: mat-cells
: mat-view ( -- view ) mat mat-goal @ lf-goal-view ;
: mat-at ( fvar -- k ) mat-view swap lf-view-find lf-found ;
: mat-k ( -- k ) mat mat-fvar @ mat-at ;
: mat-fvar-at ( k -- fvar ) mat-view swap lf-view-fvar ;

\ ---- findMaxFVar: the newest local after fvar that the type names.
: mat-is? ( fvar leaf -- fvar flag ) over = ;
: mat-names? ( k j -- k flag )
  over + 1+ mat-fvar-at mat mat-type @ swap ['] mat-is? lf-term-holds-with? lf-must ;
: mat-later ( -- k n ) mat-k mat-view lf-view-count over - 1- ;
: mat-max ( -- )
  mat-later ['] mat-names? find-last-index 0= if exit then
  mat-k + 1+ mat-fvar-at mat mat-fvar ! ;

\ ---- assertAfter: revertAfter, assert, intro1P and introNP at once (one
\ introN of n + 1 binders, the same term once instantiated). introN's
\ names: the new one's, then each reverted local's, 0 for an
\ inaccessible one (introN makes the binder's own name inaccessible).
: mat-count ( -- ) mat-later nip mat mat-n ! ;
: mat-own ( local -- name|0 )
  dup lf-local-flags lf-local-inaccessible and if drop 0 else lf-local-name then ;
: mat-own@ ( j -- name|0 ) mat-k + mat-view swap lf-view-local mat-own ;
: mat-name! ( addr j -- addr ) 2dup cells + swap mat-own@ swap ! ;
: mat-names ( addr -- addr ) mat mat-name @ over ! mat mat-n @ 0 ?do i 1+ mat-name! loop ;
: mat-binders ( -- n ) mat mat-n @ 1+ ;
: mat-xs ( addr -- xs ) mat-binders cells + ;
: mat-revert ( -- goal1 ) mat mat-goal @ mat mat-fvar @ lf-goal-revert-after drop ;
: mat-assert ( goal1 -- goal2 )
  mat mat-name @ mat mat-type @ mat mat-val @ lf-goal-assert ;
: mat-intro ( goal2 addr -- goal3 )
  mat-names dup 0 swap mat-binders swap mat-xs lf-goal-intro-n ;
: mat-run ( addr -- goal' fvar' )
  dup >r mat-revert mat-assert swap mat-intro r> mat-xs @ ;
: mat-after ( -- goal' fvar' )
  mat-count mat-binders 2* mat-cells ['] mat-run lf-with-cells ;

\ ---- tryClear (Clear.lean:48): clear, or goal itself when clear refuses.
: lf-goal-try-clear ( goal fvar -- goal' )
  over swap lf-goal-clear dup outcome-invalid = if 2drop exit then lf-must nip ;

\ ---- replace: the old hypothesis's name, assertAfter', tryClear; the
\ new goal and the new hypothesis (AssertAfterResult's mvarId, fvarId).
: mat-cleared ( goal' fvar' -- goal'' fvar' ) swap mat mat-old @ lf-goal-try-clear swap ;
: mat-old-local ( -- local ) mat-view mat mat-old @ lf-view-local-of ;
: mat-ready ( -- )
  mat mat-goal @ lf-goal-not-assigned drop mat-old-local lf-local-name mat mat-name !
  mat mat-type @ lf-instantiate! lf-open-mvar-free mat mat-type ! ;
: mat-fill ( goal fvar e type -- )
  mat mat-type ! mat mat-val ! dup mat mat-old ! mat mat-fvar ! mat mat-goal ! ;
: mat-replaced ( goal fvar e type -- goal' fvar' )
  mat-fill mat-ready mat-max mat-after mat-cleared ;
: mat-replace ( goal fvar e type -- goal' fvar' )
  mat-frames ['] mat-replaced lf-with-record ;
: lf-goal-replace ( goal fvar e type -- goal' ) mat-replace drop ;
\ replaceLocalDecl: replace with Eq.mp proof fvar of type new.
: lf-goal-replace-local-decl ( goal fvar new proof -- goal' fvar' )
  rot tuck lf-mk-eq-mp rot mat-replace ;

\ ---- replaceLocalDeclDefEq, route 1: fvar' of type new in fvar's place;
\ goal' of goal's type, kind and tag there; goal assigned ?d fvar, ?d
\ delayed-assigned fvar' := goal'.
: mat-equal-to? ( type new -- flag ) lf-meta-equal? lf-must ;
\ Expr.equal before and after instantiation; new kept instantiated.
: mat-equal? ( -- flag )
  mat mat-old @ lf-fvar-type mat mat-type @ 2dup mat-equal-to? if 2drop true exit then
  lf-instantiate! dup mat mat-type ! swap lf-instantiate! mat-equal-to? ;
: mat-free ( -- )
  mat mat-goal cell-pair@ lf-goal-fvar-free dup outcome-invalid =
  if drop outcome-unsupported then lf-must ;
: mat-retyped-view ( -- view )
  mat mat-type @ lf-lctx-local lf-must dup mat mat-fvar !
  mat-view mat mat-old @ rot lf-view-refvar lf-must ;
: mat-like ( view -- goal' )
  >r mat mat-goal @ dup lf-goal-type swap lf-goal-kind r> lf-mvar-new-at lf-must
  dup mat mat-goal @ lf-goal-tag lf-mvar-tag! lf-must ;
: mat-aux ( -- aux )
  mat-old-local lf-local-name mat mat-type @ mat mat-goal @ lf-goal-type mat-pi
  mv-opaque mat-view lf-mvar-new-at lf-must ;
: mat-delayed ( goal' aux -- )
  mat mat-fvar @ lf-delay-fvar lf-must tuck swap 1 lf-mvar-delay lf-must
  mat mat-old @ lf-mk-app mat mat-goal @ swap lf-mvar-assign lf-must ;
: mat-defeq-run ( -- goal' )
  mat mat-goal @ lf-goal-not-assigned drop mat-equal? if mat mat-goal @ exit then
  mat-free mat-retyped-view mat-like dup mat-aux mat-delayed ;
: mat-defeq ( goal fvar type -- goal' )
  mat mat-type ! mat mat-goal cell-pair! mat-defeq-run ;
: lf-goal-replace-local-decl-defeq ( goal fvar type -- goal' )
  mat-frames ['] mat-defeq lf-with-record ;

\ ---- assertHypotheses: a run of (local type value) triples asserted
\ last first, one goal each, then introduced again at once (introNP).
: mat-hyps# ( run -- n ) run-count 3 / ;
: mat-triple ( run k -- local type val ) 3 * 3 0 do 2dup i + run@ -rot loop 2drop ;
: mat-assert-at ( goal run k -- goal' run )
  over >r mat-triple >r >r lf-local-name r> r> lf-goal-assert r> ;
: mat-assert-all ( goal run -- goal' run )
  0 over mat-hyps# 1- do i mat-assert-at -1 +loop ;
: mat-own-at ( run addr k -- run addr )
  >r over r@ 3 * run@ mat-own over r> cells + ! ;
: mat-intro-hyps ( goal run addr -- goal' )
  over mat-hyps# 0 ?do i mat-own-at loop
  swap mat-hyps# >r dup r@ cells + 0 swap r> swap lf-goal-intro-n ;
: mat-hyps-run ( goal run addr -- goal' ) >r mat-assert-all r> mat-intro-hyps ;
: lf-goal-assert-hyps ( goal run -- goal' )
  dup run-count 0= if drop exit then
  dup mat-hyps# 2* mat-cells ['] mat-hyps-run lf-with-cells ;

\ ---- changeLocalDecl of a hypothesis nothing else depends on: revert
\ it, the pi's domain made type (isDefEq first, unequal not supported),
\ replaceTargetDefEq, introNP 1 with its own name (0 when inaccessible).
: mat-revert1 ( -- goal1 )
  mat mat-goal @ 0 mat mat-old @ lf-run+ lf-goal-revert
  1 <> outcome-unsupported and lf-must ;
: mat-checked ( pi -- pi )
  mat mat-type @ over lf-term-first@ lf-tac-defeq lf-must
  0= outcome-unsupported and lf-must ;
: mat-domain ( pi -- pi' )
  mat mat-type @ over lf-term-second@ lf-term-pi lf-made! swap lf-meta-named lf-must ;
: mat-retyped ( goal1 -- goal2 )
  dup lf-goal-type mat-checked mat-domain lf-goal-replace-target-defeq ;
: mat-intro1 ( goal local addr -- goal' fvar )
  swap mat-own over ! dup >r 0 1 r@ cell+ lf-goal-intro-n r> cell+ @ ;
: lf-goal-intro1-as ( goal local -- goal' fvar )
  2 mat-cells ['] mat-intro1 lf-with-cells ;
: mat-change-run ( -- goal' )
  mat-revert1 mat-retyped mat-old-local lf-goal-intro1-as drop ;
: mat-changed ( goal fvar type -- goal' )
  mat mat-type ! mat mat-goal cell-pair! mat-change-run ;
: lf-goal-change-local-decl ( goal fvar type -- goal' )
  mat-frames ['] mat-changed lf-with-record ;

\ ---- The have and let terms as refine elaborates them (elabLetDeclAux):
\ a let local in goal's context, the body made in the new context, goal
\ assigned mkLetFVars #[x] body.
: mat-decl! ( name type val nondep -- )
  mat mat-nondep ! mat mat-val ! mat mat-type ! mat mat-name ! ;
: mat-let-fill ( goal name type val nondep xt -- ) mat mat-xt ! mat-decl! mat mat-goal ! ;
: mat-decl ( -- type val name nondep )
  mat mat-type @ mat mat-val @ mat mat-name @ mat mat-nondep @ ;
: mat-let-local ( -- view' ) mat-decl lf-let-decl-new swap mat mat-fvar ! ;
\ goal assigned let x := v; body (mkLetFVars over the frame's cell).
: mat-bound ( goal body -- body )
  tuck mat mat-fvar 1 lf-mk-let-fvars lf-mvar-assign lf-must ;
: mat-let-bind ( -- body ) mat mat-goal @ dup mat mat-xt @ execute mat-bound ;
: mat-let-run ( -- body ) mat-let-local ['] mat-let-bind swap lf-with-view ;
: mat-let ( goal name type val nondep xt -- body )
  mat-let-fill mat mat-goal @ lf-goal-not-assigned ['] mat-let-run lf-with-goal ;
\ The have (nondep true) or let of xt's body.
: mat-let-with ( goal name type val nondep xt -- body )
  mat-frames ['] mat-let lf-with-record ;
: lf-goal-have-with ( goal name type val xt -- body ) true swap mat-let-with ;
\ ?_ elaborated against the target instantiated (refine's getMainTarget);
\ refine's one new goal takes the goal's tag (tagUntaggedGoals).
: lf-goal-target ( goal -- type tag ) dup lf-goal-type lf-instantiate! swap lf-goal-tag ;
: mat-hole ( goal -- goal' ) lf-goal-target lf-mctx-view lf-goal-new lf-must ;
: mat-holed ( goal name type val nondep -- goal' ) ['] mat-hole mat-let-with ;
: lf-goal-have ( goal name type val -- goal' ) true mat-holed ;
: lf-goal-let ( goal name type val -- goal' ) false mat-holed ;
base !   \ the BASE this file was loaded with

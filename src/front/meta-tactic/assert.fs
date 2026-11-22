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
\ tryClear -> lf-goal-clear (goals.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: mat-frames (a frame per call open, meta-must.fs's lf-with-record)
\ and mat-cells (introN's names and free variables, lf-with-cells), in
\ the checker context (ADR 0009); no other. Loads in decimal whatever
\ BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/slab.fs
require ../../lib/find.fs
require ../../lib/context.fs
require ../../core/terms.fs
require ../../present/binder-table.fs
require ../mvars.fs
require ../lctx-views.fs
require ../goals.fs
require ../term-find.fs
require ../meta-must.fs
require ../app-builder.fs
require ./goal.fs
require ./revert.fs

\ ---- MVarId.assert: (name : type) -> target, goal assigned goal' val.
: mat-pi ( goal name type -- goal pi )
  2 pick lf-goal-type lf-term-pi lf-made! swap lf-binder-named ;
: lf-goal-assert ( goal name type val -- goal' )
  >r rot lf-goal-not-assigned -rot mat-pi over lf-goal-fresh tuck r> lf-mk-app
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
: mat-names ( addr -- addr )
  mat mat-name @ over ! mat mat-n @ 0 ?do i 1+ dup mat-own@ swap cells 2 pick + ! loop ;
: mat-binders ( -- n ) mat mat-n @ 1+ ;
: mat-xs ( addr -- xs ) mat-binders cells + ;
: mat-revert ( -- goal1 ) mat mat-goal @ mat mat-fvar @ lf-goal-revert-after drop ;
: mat-assert ( goal1 -- goal2 )
  mat mat-name @ mat mat-type @ mat mat-val @ lf-goal-assert ;
: mat-intro ( goal2 addr -- goal3 )
  mat-names dup 0 swap mat-binders swap mat-xs lf-goal-intro-n ;
: mat-run ( addr -- goal' ) mat-revert mat-assert swap mat-intro ;
: mat-after ( -- goal' ) mat-count mat-binders 2* mat-cells ['] mat-run lf-with-cells ;

\ ---- replace: the old hypothesis's name, assertAfter', tryClear.
: mat-cleared ( goal' -- goal'' )
  dup mat mat-old @ lf-goal-clear dup outcome-invalid = if 2drop exit then lf-must nip ;
: mat-user-name ( -- name )
  mat mat-old @ mat-at mat-view swap lf-view-local lf-local-name ;
: mat-ready ( -- )
  mat mat-goal @ lf-goal-not-assigned drop mat-user-name mat mat-name !
  mat mat-type @ lf-instantiate! lf-open-mvar-free mat mat-type ! ;
: mat-fill ( goal fvar e type -- )
  mat mat-type ! mat mat-val ! dup mat mat-old ! mat mat-fvar ! mat mat-goal ! ;
: mat-replaced ( goal fvar e type -- goal' )
  mat-fill mat-ready mat-max mat-after mat-cleared ;
: lf-goal-replace ( goal fvar e type -- goal' )
  mat-frames ['] mat-replaced lf-with-record ;
base !   \ the BASE this file was loaded with

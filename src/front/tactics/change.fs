\ T by-change and T by-show: Lean's change T and show T on the goal (plan
\ row TB2, tactic batch 1), ports of Lean 4.35.0's elabChange and
\ evalChange's target case (src/lean/Lean/Elab/Tactic/Change.lean:26-46,
\ 71-81) and elabShow (Elab/Tactic/Show.lean:22-62):
\ - elabChange e p: the pattern p elaborated against e's type
\   (elabTermEnsuringType, no postponing: tactic-core.fs's
\   lf-tac-elab-ensuring; Lean synthesizes after the first isDefEq, which
\   meets the same problems), then isDefEq p e, again with synthetic
\   opaque metavariables assignable; unequal is the caller's error with
\   Lean's text (the pattern and the target indented; the explicit
\   arguments addPPExplicitToExposeDiff adds are not printed, as rfl's);
\   p instantiated. A metavariable left open in p is not supported yet
\   (93): Lean makes a ?_ hole a new goal and refuses a natural one
\   (withCollectingNewGoalsFrom), and LeanForth's terms have no holes, so
\   such a p comes only from an implicit argument nothing fixed.
\ - by-change: in the main goal's context elabChange of the main goal's
\   type instantiated, then MVarId.replaceTargetDefEq (meta-tactic/
\   goal.fs: the goal itself when nothing changed, else @id T goal') and
\   the new goal in the main goal's place. Error 443, "'change' tactic
\   failed, pattern". With a trailing at[ ] (plan row TB2 batch 3a; Lean's
\   withLocation, tactic-core.fs's lf-with-location): each hypothesis
\   named, elabChange of its local's type as stored (h.getType), then
\   MVarId.changeLocalDecl (meta-tactic/assert.fs: reverted, its type
\   replaced, introduced again under its name, so later steps name the
\   new one), then the goal when |- is named. at[ * ] is not supported yet
\   (99).
\ - by-show: the unsolved goals in order, each tried in its own context
\   (elabChange of its type as stored, then replaceTargetDefEq) from a
\   saved state; the first that succeeds is the new main goal, the goals
\   before it after it in their order, then the rest. With one goal, its
\   failure is error 444, "'show' tactic failed, pattern"; with several and
\   none that fits, the first is tried again for Lean's error 445, "'show'
\   tactic failed, no goals unify with the given pattern." with its
\   pattern and target. No goal: error 90. Lean tries the goal list as it
\   is (getGoals); LeanForth tries the unsolved ones, the same goals less
\   the assigned ones, which Lean's tries always refuse (checkNotAssigned).
\ Lean call list: liftMetaTactic -> lf-lift-target1, lf-lift-local1
\ (tactic-core.fs);
\ Term.elabTermEnsuringType -> lf-tac-elab-ensuring; isDefEq ->
\ lf-tac-defeq; withAssignableSyntheticOpaque -> lf-with-assignable-opaque
\ (meta-config.fs); instantiateMVars -> lf-instantiate!; replaceTargetDefEq
\ -> lf-goal-replace-target-defeq (meta-tactic/goal.fs); withLocation ->
\ lf-with-location; FVarId.getType -> lf-fvar-type; changeLocalDecl ->
\ lf-goal-change-local-decl (meta-tactic/assert.fs); getGoals ->
\ lf-goals-unsolved; saveState and restore -> lf-tac-try-lean;
\ setGoals -> lf-goals!.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: show's fields in its step record (tactic-run.fs's
\ lf-tac-in-record); no other.

require ../tactic-api.fs
require ../meta-tactic/assert.fs

443 outcome-invalid s" 'change' tactic failed, pattern" lfa-code: lfa-e-change
444 outcome-invalid s" 'show' tactic failed, pattern" lfa-code: lfa-e-show
445 outcome-invalid s" 'show' tactic failed, no goals unify with the given pattern."
  lfa-code: lfa-e-show-none
tac-shape-term-at lf-tactic: by-change constant tac-k-change
s" change" tac-k-change lf-tactic-lean!
tac-shape-term lf-tactic: by-show constant tac-k-show
s" show" tac-k-show lf-tactic-lean!

\ ---- The errors: the pattern and the target, as each message words it.
: tch-target. ( tgt -- outcome )
  s\" \nis not definitionally equal to target\n" lf-pp-emit lf-tac-indented. ;
: tch-pair. ( p tgt -- outcome )
  swap lf-tac-indented. dup ok? if drop tch-target. else nip then ;
: tch-omitted. ( outcome -- outcome )
  dup ok? if s\" \n(Errors for other goals omitted)" lf-pp-emit then ;
: tch-first. ( tgt -- outcome )
  s\" \nis not definitionally equal to the target\n" lf-pp-emit
  lf-tac-indented. tch-omitted. ;
: tch-many. ( p tgt -- outcome )
  s\" \nIn the first goal, the pattern\n" lf-pp-emit swap lf-tac-indented.
  dup ok? if drop tch-first. else nip then ;
\ An error: its printer xt ( p tgt -- outcome ) and its code.
: tch-fail ( p e xt code -- ) >r 2 swap lf-tac-detail-n r> lf-tac-stop ;

\ ---- elabChange.
: tch-type ( node e -- p ) lf-infer! lf-tac-elab-ensuring ;
: tch-defeq? ( p e -- flag ) lf-tac-defeq lf-tac-must ;
: tch-opaque? ( p e -- flag ) ['] tch-defeq? lf-with-assignable-opaque ;
: tch-unified? ( p e -- flag ) 2dup tch-defeq? if 2drop true else tch-opaque? then ;
: tch-unify ( p e xt code -- p )
  2>r 2dup tch-unified? if drop 2r> 2drop exit then 2r> tch-fail 0 ;
: tch-elab ( node e xt code -- p )
  2>r tuck tch-type swap 2r> tch-unify lf-instantiate! lf-open-mvar-free ;

\ ---- change: the main goal's target, or a hypothesis's type (at[ ]).
: tch-pattern ( i e -- p ) swap 0 lf-tac-arg swap ['] tch-pair. lfa-e-change tch-elab ;
: tch-tac ( i goal -- goal' )
  tuck lf-goal-type lf-instantiate! tch-pattern lf-goal-replace-target-defeq ;
: tch-new-type ( i fvar -- fvar type ) tuck lf-fvar-type tch-pattern ;
: tch-local ( i fvar goal -- goal' ) -rot tch-new-type lf-goal-change-local-decl ;
: tch-at-target ( i -- i ) ['] tch-tac lf-lift-target1 ;
: tch-at-local ( i fvar -- i ) ['] tch-local lf-lift-local1 ;
: tch-run ( i -- ) ['] tch-at-local ['] tch-at-target lf-at-location ;
' tch-run tac-k-change lf-tactic-action!

\ ---- show: the first goal the pattern fits, brought to the front.
begin-structure /tsh      \ the step's fields
  field: tsh-step         \ the by-show step
  field: tsh-goals        \ the unsolved goals
  field: tsh-k            \ the place of the goal tried
  field: tsh-xt           \ the error's printer
  field: tsh-code         \ and code
end-structure
/tsh lf-tac-work-cells cells >
[if] .( tactics/change.fs: its fields are wider than a step record) cr abort [then]
: tsh ( -- addr ) lf-tac-record ;
: tsh-goal ( -- goal ) tsh tsh-goals @ tsh tsh-k @ run@ ;
: tsh-node ( -- node ) tsh tsh-step @ 0 lf-tac-arg ;
: tsh-error ( -- xt code ) tsh tsh-xt @ tsh tsh-code @ ;
: tsh-change ( -- goal' )
  tsh-node tsh-goal lf-goal-type tsh-error tch-elab tsh-goal swap
  lf-goal-replace-target-defeq ;
\ goal' :: the goals before it :: the goals after it.
: tsh-cat ( run1 run2 -- run ) run-cat lf-tac-must ;
: tsh-before ( goal' -- run )
  0 swap run-push lf-tac-must tsh tsh-goals @ tsh tsh-k @ run-take lf-tac-must tsh-cat ;
: tsh-after ( run -- run' )
  tsh tsh-goals @ tsh tsh-k @ 1+ run-after lf-tac-must tsh-cat ;
\ tryGoal: goal k with the error given (xt and code).
: tsh-attempt ( k xt code -- )
  tsh tsh-code ! tsh tsh-xt ! tsh tsh-k ! tsh-goal ['] tsh-change lf-with-goal
  tsh-before tsh-after lf-goals! lf-tac-must ;
: tsh-simple ( k -- ) ['] tch-pair. lfa-e-show tsh-attempt ;
: tsh-tried ( -- ) tsh tsh-k @ tsh-simple ;
: tsh-try ( k -- done? ) tsh tsh-k ! ['] tsh-tried lf-tac-try-lean ;
: tsh-count ( -- n ) tsh tsh-goals @ run-count ;
: tsh-none ( -- ) 0 ['] tch-many. lfa-e-show-none tsh-attempt ;
: tsh-search ( -- ) tsh-count 0 ?do i tsh-try if unloop exit then loop tsh-none ;
: tsh-show ( i -- )
  tsh tsh-step ! lf-tac-main drop lf-goals-unsolved lf-tac-must tsh tsh-goals !
  tsh-count 1 = if 0 tsh-simple else tsh-search then ;
: tsh-run ( i -- ) ['] tsh-show lf-tac-in-record ;
' tsh-run tac-k-show lf-tactic-action!

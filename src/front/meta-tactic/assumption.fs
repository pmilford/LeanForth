\ MVarId.assumption, the goal operation of the assumption tactic
\ (docs/design/TACTIC_PLUGINS.md 2.4; slice a2-iii), a port of Lean
\ 4.35.0's src/lean/Lean/Meta/Tactic/Assumption.lean:
\   lf-goal-assumption ( goal -- )  MVarId.assumption (Assumption.lean:
\       26-35) under evalAssumption's withAssignableSyntheticOpaque
\       (Elab/Tactic/BuiltinTactic.lean:309): in goal's context
\       (checkNotAssigned first), findLocalDeclWithType? (:15-23) of the
\       goal's type as stored: the locals from the newest to the oldest,
\       implementation details passed over, the first whose type is
\       defeq the goal's (isDefEq in the configuration in force, synthetic
\       opaque metavariables assignable); the goal assigned its free
\       variable. None: Lean's throwTacticEx with no message, error 381,
\       "Tactic `assumption` failed" and the goal.
\ Lean call list: withContext -> the caller's (tactic-core.fs);
\ checkNotAssigned -> lf-goal-not-assigned (goal.fs); getType ->
\ lf-mvar-type; getLCtx/findDeclRevM? -> the goal's view (lctx-views.fs,
\ lf-view-count, lf-view-local) walked from its end; isImplementationDetail
\ -> lf-local-detail?; isDefEq -> lf-defeq! under lf-meta-with;
\ assign -> lf-mvar-assign; throwTacticEx -> lf-tac-failed (tactic-basic.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own. Loads in decimal whatever BASE is, then
\ restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../author/errors.fs
require ../../core/local-context.fs
require ../mvars.fs
require ../meta-config.fs
require ../lctx-views.fs
require ../goals.fs
require ../defeq.fs
require ../tactic-basic.fs
require ../meta-must.fs
require ./goal.fs

381 outcome-invalid s" Tactic `assumption` failed" lfa-code: lfa-e-assumption

\ isDefEq with synthetic opaque metavariables assignable.
: mas-defeq ( t s -- flag )
  ['] lf-defeq! lf-defeq-flags lf-defeq-opaque or lf-defeq-mode lf-meta-with ;
\ Local i of view fits type: no implementation detail, its type defeq.
: mas-fits? ( type view i -- flag )
  lf-view-local dup lf-local-detail? if 2drop false exit then
  lf-local-fvar lf-fvar-type mas-defeq ;
: mas-find ( type view -- fvar true | false )
  dup lf-view-count begin dup while 1-
    2 pick 2 pick 2 pick mas-fits? if lf-view-local lf-local-fvar nip true exit then
  repeat drop 2drop false ;
: mas-view ( goal -- view ) lf-mvar-view 0= if outcome-invalid lf-must then ;
: lf-goal-assumption ( goal -- )
  lf-goal-not-assigned dup lf-mvar-type drop over mas-view mas-find
  if lf-mvar-assign lf-must exit then
  ['] lf-tac-goal-of. lf-tac-detail lfa-e-assumption lf-tac-stop ;
base !   \ the BASE this file was loaded with

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
\ Lean call list: withContext -> lf-with-goal (meta-must.fs);
\ checkNotAssigned -> lf-goal-not-assigned (goal.fs); getType ->
\ lf-goal-type; getLCtx/findDeclRevM? -> the goal's view (lctx-views.fs,
\ lf-view-count, lf-view-local) searched from its end (lib/find.fs's
\ find-last-index); isImplementationDetail
\ -> lf-local-detail?; isDefEq -> lf-defeq! under lf-with-assignable-opaque
\ (meta-config.fs);
\ assign -> lf-mvar-assign; throwTacticEx -> lf-tac-ex (tactic-msg.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own. Loads in decimal whatever BASE is, then
\ restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/find.fs
require ../../author/errors.fs
require ../../core/local-context.fs
require ../mvars.fs
require ../meta-config.fs
require ../lctx-views.fs
require ../goals.fs
require ../defeq.fs
require ../tactic-msg.fs
require ../meta-must.fs
require ./goal.fs

381 outcome-invalid s" Tactic `assumption` failed" lfa-code: lfa-e-assumption

\ isDefEq with synthetic opaque metavariables assignable.
: mas-defeq ( t s -- flag ) ['] lf-defeq! lf-with-assignable-opaque ;
\ Local k of the goal's context fits type: no implementation detail, its
\ type defeq; findDeclRevM?: the last k that fits.
: mas-fits? ( type k -- type flag )
  lf-mctx-view swap lf-view-local dup lf-local-detail? if drop false exit then
  lf-local-fvar lf-fvar-type over swap mas-defeq ;
: mas-find ( type -- k true | false )
  lf-mctx-view lf-view-count ['] mas-fits? find-last-index ;
: mas-none ( goal -- ) lfa-e-assumption lf-tac-ex ;
: mas-run ( goal -- )
  lf-goal-not-assigned dup lf-goal-type lf-instantiate! mas-find
  if lf-mctx-fvar lf-mvar-assign lf-must exit then mas-none ;
: lf-goal-assumption ( goal -- ) dup ['] mas-run lf-with-goal ;
base !   \ the BASE this file was loaded with

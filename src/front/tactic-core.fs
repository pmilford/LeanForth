\ The tactic library's Elab glue (docs/design/TACTIC_PLUGINS.md 2.5;
\ slices a2-ii, a2-iii and 9.4.8l-I), after Lean 4.35.0's
\ Elab/Tactic/Basic.lean and Elab/Tactic/ElabTerm.lean:
\   lf-tac-elab ( node expected postpone? -- term outcome )  a deferred
\       word front/elab-decl.fs sets (Lean's Tactic.elabTerm: Term.elabTerm
\       against expected, a negative one for none, the synthetic
\       metavariables synthesized, postponing when postpone? is true,
\       Lean's mayPostpone, the result instantiated); error 71 without
\       front/elab-decl.fs
\   lf-tac-step-run ( i*x i xt -- j*x )  xt ( i*x i -- j*x ) in a new step
\       record (tactic-run.fs's lf-tac-in-record), the main goal's fields
\       in tb, its context current (withMainContext); tb's fields: the
\       goal, its type, its context and the metavariable count when the
\       step began (tb-goal, tb-want, tb-view, tb-from), then the older
\       tactics' own until they move (plan 9.4.8l-I)
\   lf-tac-pop-main ( -- )  the main goal off the list (popMainGoal)
\   lf-tac-goal. ( -- outcome )  the step's goal after a blank line;
\   lf-tac-framed. ( term xt -- outcome )  term indented, what xt ( --
\       outcome ) prints, then the step's goal (Lean's throwTacticEx with
\       a message: its text, then the goal)
\   lf-lift-meta-tactic ( i*x i xt -- )  liftMetaTactic (Basic.lean:581):
\       step i runs in a new step record, xt ( i*x goal -- goals ) gets the
\       main goal and its new goals (a run) take the main goal's place
\       (replaceMainGoal)
\   lf-tac-args# ( i -- n ), lf-tac-arg ( i k -- x ), lf-tac-arg-at ( i k
\       -- pos )  getArg: how many arguments step i has (names, rules),
\       its argument k from 0 (a syntax node or a name, 0 for _) and that
\       argument's place in the text
\   lf-tac-only ( goal -- )  setGoals [goal] (an alternative's or a case's)
\   lf-tac-with-synth ( i*x xt -- j*x )  Term.withSynthesize (with
\       synthesizeSyntheticMVarsNoPostponing): xt run with the pending
\       problems set aside, the ones it adds synthesized with no
\       postponing (elab-pending.fs's lf-elab-with-synth), the list put
\       back however it ends; the stack passes through to xt
\   lf-tac-try-lean ( xt -- flag )  try (observing?): xt ( -- ) from a
\       saved state (lf-tac-try); true when it ran to its end; a Lean
\       error (tactic-msg.fs's lf-tac-lean-error?) undone and forgotten,
\       false; anything else (not supported, no room, no fuel, a fault)
\       thrown on, never turned into success
\   lf-tac-elab-for-apply ( node -- e )  elabTermForApply
\       (ElabTerm.lean:264) as evalApplyLikeTactic calls it (:284-292): an
\       identifier resolved with no argument inserted (elab-term.fs's
\       lf-elab-ident), any other term elaborated with no expected type,
\       postponing allowed (lf-tac-elab); the result instantiated; Lean
\       then synthesizes when it is a metavariable, which LeanForth does
\       not port (unsupported, error 99)
\ Untrusted: only the kernel's check of the finished term decides.
\ State: tb, the running step record's fields (tactic-run.fs's
\ lf-tac-record, review fe1g3 M2), in the checker context (ADR 0009); no
\ other. Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/runs.fs
require ../author/errors.fs
require ./syntax.fs
require ./mvars.fs
require ./goals.fs
require ./goal-print.fs
require ./elab-term.fs
require ./elab-pending.fs
require ./tactic-syntax.fs
require ./tactic-run.fs
require ./tactic-msg.fs
require ./meta-must.fs

\ ---- The elaborator's hook.
defer lf-tac-elab ( node expected postpone? -- term outcome )
: tcr-unelaborated ( node expected postpone? -- term outcome )
  2drop drop lfa-e-elaborate lf-tac-fail -1 outcome-unsupported ;
' tcr-unelaborated is lf-tac-elab

\ ---- The step record: the main goal's fields, then the older tactics'.
begin-structure /tb
  field: tb-goal        \ the goal the step works on
  field: tb-view        \ its context
  field: tb-from        \ the metavariable count when the step began
  field: tb-want        \ the goal's type
  field: tb-term        \ exact's term, or rfl's left side
  field: tb-type        \ its type, or rfl's right side
  field: tb-pi          \ intro's binder
  field: tb-dom         \ its domain, head-beta reduced
  field: tb-x           \ its free variable
  field: tb-name        \ the hypothesis's name
  field: tb-flags       \ and its local's flags
  field: tb-new         \ the goal in its place
end-structure
/tb lf-tac-work-cells cells >
[if] .( tactic-core.fs: tb is wider than a step record) cr abort [then]
\ The step's fields: in the running step record, else the last one's.
: tb ( -- addr ) lf-tac-record ;
: tcr-start ( goal -- goal )
  dup tb tb-goal ! dup lf-goal-type tb tb-want ! dup lf-goal-view tb tb-view !
  lf-mvar-count tb tb-from ! ;
: tcr-run ( i*x xt i -- j*x ) swap lf-tac-main tcr-start swap lf-with-goal ;
: lf-tac-step-run ( i*x i xt -- j*x ) swap ['] tcr-run lf-tac-in-record ;
: lf-tac-pop-main ( -- ) 0 lf-replace-main lf-tac-must ;
: lf-tac-goal. ( -- outcome ) s\" \n\n" lf-pp-emit tb tb-goal @ lf-goal-print ;
\ A term indented, what xt ( -- outcome ) prints, then the step's goal.
: lf-tac-framed. ( term xt -- outcome )
  swap lf-tac-indented. swap ok-and ['] lf-tac-goal. ok-and ;

\ ---- liftMetaTactic.
: tcr-lifted ( i*x xt i -- ) drop tb tb-goal @ swap execute lf-replace-main lf-tac-must ;
: lf-lift-meta-tactic ( i*x i xt -- ) swap ['] tcr-lifted lf-tac-step-run ;

\ ---- getArg, setGoals.
: lf-tac-args# ( i -- n ) lf-tactic-step tac-count @ ;
: tcr-arg ( i k -- x pos ) swap lf-tactic-step tac-first @ + lf-tactic-arg ;
: lf-tac-arg ( i k -- x ) tcr-arg drop ;
: lf-tac-arg-at ( i k -- pos ) tcr-arg nip ;
: lf-tac-only ( goal -- ) 0 swap run-push lf-tac-must lf-goals! lf-tac-must ;

\ ---- withSynthesize: xt run under the pending list's window, the
\ window's mode (no postponing) given back above the caller's cells.
: tcr-under ( i*x xt mode -- j*x mode ) drop execute lf-postpone-no ;
: lf-tac-with-synth ( i*x xt -- j*x )
  ['] tcr-under lf-postpone-no lf-elab-with-synth lf-tac-must ;

\ ---- try.
: lf-tac-try-lean ( xt -- flag )
  lf-tac-try ?dup 0= if true exit then lf-tac-forget-lean false ;

\ ---- elabTermForApply.
: tcr-ident ( node -- e ) lf-elab-ident lf-tac-must ;
: tcr-term ( node -- e ) -1 true lf-tac-elab lf-tac-must ;
: tcr-not-mvar ( e -- e ) dup lf-mvar? if lfa-e-tac-form lf-tac-fail then ;
: lf-tac-elab-for-apply ( node -- e )
  dup lf-elab-ident? if tcr-ident else tcr-term then lf-instantiate! tcr-not-mvar ;
base !   \ the BASE this file was loaded with

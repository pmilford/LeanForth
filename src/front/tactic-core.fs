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
\       step began (tb-goal, tb-want, tb-view, tb-from), then
\       lf-tac-intro1's cells (tb-name, tb-kind, tb-x)
\   lf-tac-pop-main ( -- )  the main goal off the list (popMainGoal)
\   lf-tac-goal. ( -- outcome )  the step's goal after a blank line
\       (Lean's throwTacticEx with a message: its text, then the goal;
\       a framed term with the goal is tactic-msg.fs's
\       lf-tac-framed-with.)
\   lf-lift-meta-tactic ( i*x i xt -- )  liftMetaTactic (Basic.lean:581):
\       step i runs in a new step record, xt ( i*x goal -- goals ) gets the
\       main goal and its new goals (a run) take the main goal's place
\       (replaceMainGoal)
\   lf-lift-meta-tactic1 ( i*x i xt -- )  liftMetaTactic1 (Basic.lean:586)
\       as LeanForth's goal words give it: the same with xt ( i*x goal --
\       goal' ), goal' alone in the main goal's place (a goal word that
\       closes its goal is run by lf-lift-meta-tactic instead)
\   lf-goals1 ( goal -- goals )  the goal list [goal] (a new run)
\   lf-tac-args# ( i -- n ), lf-tac-arg ( i k -- x ), lf-tac-arg-at ( i k
\       -- pos )  getArg: how many arguments step i has (names, rules),
\       its argument k from 0 (a syntax node or a name, 0 for _) and that
\       argument's place in the text
\   lf-tac-only ( goal -- )  setGoals [goal] (an alternative's or a case's)
\   lf-tac-with-synth ( i*x xt -- j*x )  Term.withSynthesize (with
\       synthesizeSyntheticMVarsNoPostponing): xt run with the pending
\       problems set aside, the ones it adds synthesized with no
\       postponing (elab-pending.fs's lf-elab-with-synth), the list put
\       back however it ends; the stack passes through to xt. A problem
\       no instance fills stops the step with the elaborator's own error
\       (125 failed to synthesize, 126 stuck: Lean's), as lf-tac-elab's
\       do (lf-tac-elab-fail; plan 9.4.8l S)
\   lf-tac-elab-detail ( -- ), lf-tac-elab-fail ( outcome -- )  the
\       elaborator's failure as an error: its recorded term indented as
\       the detail (none: no detail), then its code with its position as
\       the second one, else the outcome's code (elab-pending.fs's
\       lf-elab-code: no room 60, fuel 138, a step not ported 139),
\       stopping the step (elab-decl.fs's hook and #check use them too)
\   lf-tac-try-lean ( xt -- flag )  try (observing?): xt ( -- ) from a
\       saved state (lf-tac-try); true when it ran to its end; a Lean
\       error (tactic-msg.fs's lf-tac-lean-error?) undone and forgotten,
\       false; anything else (not supported, no room, no fuel, a fault)
\       thrown on, never turned into success
\   lf-tac-first-of ( xtn .. xt1 n -- )  first | t1 | .. | tn
\       (BuiltinTactic.lean:631-641, evalFirst's loop), the first
\       alternative on top, n >= 1 (else a fault, invalid), each xt ( -- )
\       a tactic on the step running (lf-tac-step): xt1 .. xtn-1 tried in
\       turn from a saved state (lf-tac-try-lean), the first that runs to
\       its end kept and the rest not run; a Lean error undone and
\       forgotten; anything else thrown on at once; xtn, the deepest, when
\       all before it failed, runs bare, so its error is the one reported,
\       as Lean's. Also an extensible macro's rules (Elab/Tactic/
\       Basic.lean's expandEval: tried newest first, the error of the last
\       tried, the first registered, reported, Lean issue #3770): trivial's
\       (tactics/trivial.fs)
\   lf-tac-elab-term ( node expected postpone? -- e )  Tactic.elabTerm
\       (ElabTerm.lean:45): lf-tac-elab, its failure thrown as the
\       runner's error (Term codes 125-139, 71 without an elaborator)
\   lf-tac-elab-ensuring ( node expected -- e )  elabTermEnsuringType
\       (ElabTerm.lean:51) with no postponing: e's type inferred and
\       compared with expected by isDefEq with synthetic opaque
\       metavariables assignable (withAssignableSyntheticOpaque:
\       meta-config.fs's lf-with-assignable-opaque over meta-must.fs's
\       lf-tac-defeq; a goal in either type may be assigned, plan 9.4.8l
\       J); false is error 96 with Lean's text (tactic-msg.fs's
\       lf-has-type-but-expected.)
\   lf-tac-ensure-type ( e expected -- e )  that check alone, of a term
\       elaborated already (ensureHasType's isDefEq; by-absurd's, whose
\       expected ¬?a the elaborator cannot take: an expected pi is its
\       error 133, elab-term.fs)
\   lf-close-main-goal-using ( i*x i xt -- )  closeMainGoalUsing
\       (ElabTerm.lean:85): step i runs in a new step record, xt ( i*x
\       type tag -- e ) gets the main goal's type and tag; e instantiated
\       must hold no metavariable the step made and left unassigned
\       (filterOldMVars and logUnassignedAndAbort: error 95), then closes
\       the goal (meta-tactic/goal.fs's lf-goal-checked-assign) and leaves
\       the list
\   lf-tac-intro1 ( name kind i -- )  liftMetaTactic1 of introN 1
\       (meta-tactic/goal.fs's lf-goal-intro-n): step i's main goal's
\       first binder introduced, named name (0: its own, inaccessible), of
\       kind kind (-1: the node's: explicit, implicit or strict implicit,
\       as Lean's intro; plan row TB1), in its place the new
\       goal (intro NAME; an alternative's field, tactic-alts.fs)
\   lf-tac-elab-for-apply ( node -- e )  elabTermForApply
\       (ElabTerm.lean:264) as evalApplyLikeTactic calls it (:284-292): an
\       identifier resolved with no argument inserted (elab-term.fs's
\       lf-elab-ident), any other term elaborated with no expected type,
\       postponing allowed (lf-tac-elab); the result instantiated; Lean
\       then synthesizes when it is a metavariable, which LeanForth does
\       not port (unsupported, error 99)
\   lf-tac-get-fvar ( node -- fvar )  getFVarId (ElabTerm.lean:272-277): the
\       term elaborated as elabTermForApply does with no postponing (an
\       identifier with no argument inserted), instantiated; anything but
\       a free variable is error 389, Lean's "Unexpected term `e`; expected
\       single reference to variable" (a metavariable too: Lean prints its
\       ?m.N, LeanForth's name differs, never accepted)
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
require ./meta-spine.fs
require ./meta-config.fs
require ./goals.fs
require ./goal-print.fs
require ./elab-term.fs
require ./elab-pending.fs
require ./tactic-syntax.fs
require ./tactic-run.fs
require ./tactic-msg.fs
require ./meta-must.fs
require ./term-find.fs
require ./infer.fs
require ./meta-tactic/goal.fs

\ ---- The elaborator's hook.
defer lf-tac-elab ( node expected postpone? -- term outcome )
: tcr-unelaborated ( node expected postpone? -- term outcome )
  2drop drop lfa-e-elaborate lf-tac-fail -1 outcome-unsupported ;
' tcr-unelaborated is lf-tac-elab

\ ---- The step record: the main goal's fields, then a tactic's cells.
begin-structure /tb
  field: tb-goal        \ the goal the step works on
  field: tb-view        \ its context
  field: tb-from        \ the metavariable count when the step began
  field: tb-want        \ the goal's type
  field: tb-kind        \ lf-tac-intro1's kind, name
  field: tb-name
  field: tb-x           \ and free variable
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
: lf-tac-goal. ( -- outcome ) tb tb-goal @ lf-tac-goal-below. ;

\ ---- liftMetaTactic, liftMetaTactic1: xt on the main goal, its goals
\ (one goal: [goal']) in the main goal's place.
: lf-goals1 ( goal -- goals ) 0 swap run-push lf-tac-must ;
: tcr-main ( i*x xt i -- j*x ) drop tb tb-goal @ swap execute ;
: tcr-lifted ( i*x xt i -- ) tcr-main lf-replace-main lf-tac-must ;
: lf-lift-meta-tactic ( i*x i xt -- ) swap ['] tcr-lifted lf-tac-step-run ;
: tcr-lifted1 ( i*x xt i -- ) tcr-main lf-goals1 lf-replace-main lf-tac-must ;
: lf-lift-meta-tactic1 ( i*x i xt -- ) swap ['] tcr-lifted1 lf-tac-step-run ;

\ ---- introN of one binder: its name, kind and variable in tb's cells.
: tcr-kinds ( -- kinds ) tb tb-kind dup @ 0< if drop 0 then ;
: tcr-intro1 ( name kind goal -- goal' )
  drop tb tb-kind ! tb tb-name ! tb tb-goal @ tb tb-name tcr-kinds 1 tb tb-x
  lf-goal-intro-n ;
: lf-tac-intro1 ( name kind i -- ) ['] tcr-intro1 lf-lift-meta-tactic1 ;

\ ---- getArg, setGoals.
: lf-tac-args# ( i -- n ) lf-tactic-step tac-count @ ;
: tcr-arg ( i k -- x pos ) swap lf-tactic-step tac-first @ + lf-tactic-arg ;
: lf-tac-arg ( i k -- x ) tcr-arg drop ;
: lf-tac-arg-at ( i k -- pos ) tcr-arg nip ;
: lf-tac-only ( goal -- ) lf-goals1 lf-goals! lf-tac-must ;

\ ---- The elaborator's failure: its error, as Lean's throwError gives it.
: lf-tac-elab-detail ( -- )
  lf-elab-error-term dup 0< if drop else ['] lf-tac-indented. lf-tac-detail then ;
: lf-tac-elab-fail ( outcome -- ) lf-tac-elab-detail lf-elab-code lfa-see! lf-tac-stop ;

\ ---- withSynthesize: xt run under the pending list's window, the
\ window's mode (no postponing) given back above the caller's cells.
: tcr-under ( i*x xt mode -- j*x mode ) drop execute lf-postpone-no ;
: tcr-synthesized ( outcome -- ) dup ok? 0= if lf-tac-elab-fail then drop ;
: lf-tac-with-synth ( i*x xt -- j*x )
  ['] tcr-under lf-postpone-no lf-elab-with-synth tcr-synthesized ;

\ ---- try.
: lf-tac-try-lean ( xt -- flag )
  lf-tac-try ?dup 0= if true exit then lf-tac-forget-lean false ;

\ ---- first: the alternative on top tried first (lf-tac-try-lean); one
\ that ends is kept and the rest dropped; the deepest, the last, runs bare,
\ so its error is the one thrown.
: tcr-alts ( xtn..xt1 n -- )
  begin dup 1 > while swap lf-tac-try-lean if 1- ndrop exit then 1- repeat drop execute ;
: lf-tac-first-of ( xtn..xt1 n -- ) dup 0> 0= if outcome-invalid lf-must then tcr-alts ;

\ ---- Tactic.elabTerm, elabTermEnsuringType.
: lf-tac-elab-term ( node expected postpone? -- e ) lf-tac-elab lf-tac-must ;
: tcr-typed ( e expected -- e type expected ) over lf-infer lf-tac-must swap ;
: tcr-mismatch ( e type expected -- ) lfa-e-tac-mismatch lf-tac-type-mismatch ;
: tcr-defeq ( type expected -- flag outcome ) ['] lf-tac-defeq lf-with-assignable-opaque ;
: tcr-ensured ( e type expected -- e )
  2dup tcr-defeq lf-tac-must if 2drop exit then tcr-mismatch ;
: lf-tac-ensure-type ( e expected -- e ) tcr-typed tcr-ensured ;
: lf-tac-elab-ensuring ( node expected -- e )
  tuck false lf-tac-elab-term swap lf-tac-ensure-type ;

\ ---- closeMainGoalUsing: the step's new metavariables (numbered from
\ tb-from) that the term leaves unassigned are Lean's logUnassigned.
: tcr-new? ( from leaf -- from flag )
  dup lf-mvar-open? if lf-term-first@ over < 0= else drop false then ;
: tcr-fresh-free ( e -- e )
  dup tb tb-from @ ['] tcr-new? lf-term-holds-with? lf-tac-must
  if lfa-e-tac-unassigned lf-tac-fail then ;
: tcr-closing ( i*x xt i -- )
  drop tb tb-want @ swap tb tb-goal @ lf-goal-tag swap execute lf-instantiate!
  tcr-fresh-free tb tb-goal @ swap lf-goal-checked-assign lf-tac-pop-main ;
: lf-close-main-goal-using ( i*x i xt -- ) swap ['] tcr-closing lf-tac-step-run ;

\ ---- elabTermForApply, with mayPostpone given.
: tcr-ident ( node postpone? -- e ) drop lf-elab-ident lf-tac-must ;
: tcr-term ( node postpone? -- e ) -1 swap lf-tac-elab-term ;
: tcr-for-apply ( node postpone? -- e )
  over lf-elab-ident? if tcr-ident else tcr-term then lf-instantiate! ;
: tcr-not-mvar ( e -- e ) dup lf-mvar? if lfa-e-tac-form lf-tac-fail then ;
: lf-tac-elab-for-apply ( node -- e ) true tcr-for-apply tcr-not-mvar ;

\ ---- getFVarId: elabTermForApply with no postponing, a free variable.
389 outcome-invalid s" Unexpected term" lfa-code: lfa-e-tac-not-fvar
: tcr-expected. ( -- outcome )
  s" ; expected single reference to variable" lf-pp-emit outcome-ok ;
: tcr-unexpected. ( e -- outcome )
  s"  " lf-pp-emit lf-tac-inline. ['] tcr-expected. ok-and ;
: tcr-fvar ( e -- fvar )
  dup lf-meta-fvar? if exit then
  ['] tcr-unexpected. lf-tac-inline lfa-e-tac-not-fvar lf-tac-stop ;
: lf-tac-get-fvar ( node -- fvar ) false tcr-for-apply tcr-fvar ;
base !   \ the BASE this file was loaded with

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
\   lf-goals1 ( goal -- goals )  the goal list [goal] (a new run);
\       lf-goals2 ( goal1 goal2 -- goals ) [goal1, goal2]
\   lf-tac-args# ( i -- n ), lf-tac-arg ( i k -- x ), lf-tac-arg-at ( i k
\       -- pos )  getArg: how many arguments step i has (names, rules),
\       its argument k from 0 (a syntax node or a name, 0 for _) and that
\       argument's place in the text; lf-tac-arg-symm? ( i k -- flag )
\       whether argument k is a rule written right to left (<-, Lean's ←:
\       rwRule's symm flag, withRWRulesSeq); lf-tac-arg-span ( i k -- n )
\       a pattern item's span (pattern-syntax.fs), 0 for any other
\       argument; lf-tac-name ( i k -- name ) argument k, a name, _ (0)
\       not supported yet (99: Lean's parser wants an identifier there)
\   lf-tac-row ( kind -- )  kind's run word on the step running
\       (lf-tac-step): a tactic Lean writes as another one, run on the
\       same step (lf-tac-eval)
\   lf-tac-rfl-reducible ( -- )  with_reducible rfl on the step running:
\       by-rfl's row at reducible transparency (rw's and rwa's closing)
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
\       stopping the step (elab-decl.fs's hook and #check use them too);
\       Lean's logged class (tactic-run.fs's lf-tac-log-fail): final in a
\       block that recovers, as Lean's errToSorry logs it
\   lf-tac-try-lean ( xt -- flag )  try (observing?): xt ( -- ) from a
\       saved state (lf-tac-try) with recover false (withoutRecover, as
\       Lean's try is first | xt | skip; tactic-run.fs's
\       lf-tac-no-recover, plan row TB2 blocks slice 1); true when it ran
\       to its end; a Lean error (tactic-run.fs's lf-tac-lean-error?)
\       undone and forgotten, false; anything else (not supported, no
\       room, no fuel, a malformed record, a fault) thrown on, never
\       turned into success
\   lf-tac-first-of ( xtn .. xt1 n -- )  first | t1 | .. | tn
\       (BuiltinTactic.lean:631-641, evalFirst's loop), the first
\       alternative on top, n >= 1 (else a fault, invalid), each xt ( -- )
\       a tactic on the step running (lf-tac-step): xt1 .. xtn-1 tried in
\       turn from a saved state with recover false (lf-tac-try-lean,
\       orElse's withoutRecover, Basic.lean:437), the first that runs to
\       its end kept and the rest not run; a Lean error undone and
\       forgotten; anything else thrown on at once; xtn, the deepest, when
\       all before it failed, runs bare, so its error is the one reported,
\       as Lean's
\   lf-tac-macro-alts ( xtn .. xt1 n -- )  an extensible macro's rules
\       (Elab/Tactic/Basic.lean:247-258's expandEval: tried newest first,
\       each from a saved state, the error of the last tried, the first
\       registered, reported, Lean issue #3770): as lf-tac-first-of, but
\       the rules before the last keep the block's recover (expandEval
\       has no withoutRecover); rfl's and trivial's rules (tactics/rfl.fs,
\       tactics/trivial.fs)
\   lf-tac-elab-term ( node expected postpone? -- e )  Tactic.elabTerm
\       (ElabTerm.lean:45): lf-tac-elab, its failure thrown as the
\       runner's error (Term codes 125-139, 71 without an elaborator);
\       lf-tac-elab-arg ( i k -- e ) the same of step i's argument k with
\       no expected type and no postponing (elabTerm stx none)
\   lf-tac-elab-ensuring ( node expected -- e )  elabTermEnsuringType
\       (ElabTerm.lean:51) with no postponing: e's type inferred and
\       compared with expected by isDefEq with synthetic opaque
\       metavariables assignable (withAssignableSyntheticOpaque:
\       meta-config.fs's lf-with-assignable-opaque over meta-must.fs's
\       lf-tac-defeq; a goal in either type may be assigned, plan 9.4.8l
\       J); false is error 96 with Lean's text (tactic-msg.fs's
\       lf-has-type-but-expected.)
\   lf-tac-elab-as-type ( node -- type outcome )  a deferred word
\       front/elab-decl.fs sets: Term.elabType (against a new Sort ?u,
\       then ensureType: elab-term.fs's lf-elab-type; error 130 "type
\       expected" for a term that is no type) under withSynthesize
\       (postpone := .partial), as Lean's have, let and suffices
\       elaborate their type (Elab/Binders.lean:775), the result
\       instantiated; its failure stops the step as lf-tac-elab's does;
\       error 71 without front/elab-decl.fs. lf-tac-elab-type ( node --
\       type ) the same with the outcome thrown (lf-tac-must); inside
\       lf-tac-with-synth, synthesized with no postponing after it
\       (Mathlib's have h : T)
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
\       the list (since batch 3b the check is new-goals.fs's: a hole left
\       open is Lean's placeholder error, 461); lf-close-main-goal-unchecked
\       the same with checkNewUnassigned := false (calc's: xt makes its
\       new goals itself, with lf-tac-new-goals)
\   lf-tac-new-goals ( e allow? -- goals )  withCollectingNewGoalsFrom's
\       goals of a term elaborated already (ElabTerm.lean:171-182): e's
\       new metavariables still open (numbered from tb-from), oldest
\       first, a natural one among them refused unless allow? (as
\       lf-tac-elab-holes'), to be tagged with lf-tac-tag-new
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
\   lf-tac-ensure-type-as ( e expected code -- e )  lf-tac-ensure-type
\       with another code for its mismatch (rwa's 456)
\   lf-tac-located? ( i -- flag ), lf-tac-loc# ( i -- n ), lf-tac-loc-hyp
\       ( i k -- name ), lf-tac-loc-goal? ( i -- flag ), lf-tac-loc-all?
\       ( i -- flag )  expandOptLocation (Location.lean:32-46) of step i's
\       at[ ] (tactic-syntax.fs, plan row TB2 batch 3a): whether one was
\       written, its hypothesis names (name IDs, in order), whether the
\       goal is a location (|- written, or no at[ ]: Lean's targets #[]
\       true) and whether it is the wildcard (at[ * ])
\   lf-tac-name-fvar ( name -- fvar )  getFVarId of a name in the main
\       goal's context: the newest accessible local of the name
\       (resolveLocalName), so a hypothesis an earlier location replaced
\       is found again; none is Lean's 455, "Unknown identifier `h`", or,
\       when a constant has the name (Lean's 389 for it), not supported
\       yet (99); lf-tac-loc-fvar ( i k -- fvar ) that of step i's
\       location name k; lf-tac-arg-names ( i -- names ) step i's
\       arguments in order, a run (a header's or a list's names: case's,
\       rename_i's); lf-tac-arg-fvars ( i -- fvars ) getFVarIds of them,
\       a run (by-revert[, by-clear[)
\   lf-tac-elab-holes ( node expected allow? -- e goals ) and
\   lf-tac-tag-new ( goals suffix -- goals ), one after the other
\       elabTermWithHoles (ElabTerm.lean:150-205; plan row TB2, batch 3b):
\       the term elaborated, ensuring expected (-1: none), with no
\       postponing; goals (a run) its new metavariables still open, the
\       step's (numbered from tb-from), oldest first (new-goals.fs's
\       lf-fresh-mvars); unless allow? a natural one among them is
\       logUnassignedAndAbort's error (lf-tac-log-unassigned: 461, 95,
\       99); then lf-tac-tag-new tags each anonymous one from the main
\       goal's tag with the suffix, a counted string (tagUntaggedGoals,
\       lf-tag-untagged); allow? elaborates
\       with holes synthetic opaque and assignable
\       (lf-with-holes-as-goals: refine', specialize)
\   lf-tac-refine ( node goal -- goals )  refineCore (ElabTerm.lean:209-
\       222) with the suffix refine and natural holes refused, as refine
\       and the macros over it call it (plan row TB2, batch 3c:
\       tactics/refine.fs, exists.fs): in goal's context, node elaborated
\       against goal's type, instantiated, with its new goals
\       (lf-tac-elab-holes, lf-tac-tag-new), goal assigned the value;
\       the goals the result (the main goal's place is the caller's)
\   lf-tac-elab-detail's message with a rest (elab-pending.fs's
\       lf-elab-rest+, batch 3c): the term inline, then the rest, on the
\       message's line, and what lf-elab-below! gave as the detail
\   lf-with-location ( i*x i xt-local xt-target -- i*x )  withLocation
\       (Location.lean:58-77) of step i's location: each hypothesis name
\       in order resolved (lf-tac-loc-fvar) in the main goal's context and
\       given to xt-local ( i*x fvar -- i*x ), then, when the goal is a
\       location, xt-target ( i*x -- i*x ); a failure stops at once (the
\       targets case has no failure rule of its own). The wildcard, which
\       tries the goal and then every hypothesis newest first from saved
\       states, is not supported yet (99).
\   lf-at-location ( i xt-local xt-target -- )  the same for actions of
\       step i alone, xt-local ( i fvar -- i ) and xt-target ( i -- i );
\       lf-lift-target1 ( i xt -- i ) and lf-lift-local1 ( i fvar xt -- i )
\       make such actions of a goal operation, xt ( i goal -- goal' ) at
\       the goal and ( i fvar goal -- goal' ) at a hypothesis, each lifted
\       to the main goal (lf-lift-meta-tactic1)
\ Untrusted: only the kernel's check of the finished term decides.
\ State: tb, the running step record's fields (tactic-run.fs's
\ lf-tac-record, review fe1g3 M2), and tlc-frames (lf-with-location's
\ frame per call open, meta-must.fs's lf-with-record), in the checker
\ context (ADR 0009); no other. Loads in decimal whatever BASE is, then restores it.

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
require ./new-goals.fs

\ ---- The elaborator's hooks.
defer lf-tac-elab ( node expected postpone? -- term outcome )
: tcr-unelaborated ( node expected postpone? -- term outcome )
  2drop drop lfa-e-elaborate lf-tac-fail -1 outcome-unsupported ;
' tcr-unelaborated is lf-tac-elab
defer lf-tac-elab-as-type ( node -- type outcome )
: tcr-untyped ( node -- type outcome ) -1 false tcr-unelaborated ;
' tcr-untyped is lf-tac-elab-as-type

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
: lf-goals1 ( goal -- goals ) run-one lf-tac-must ;
: lf-goals0/1 ( goal | 0 -- goals ) ?dup if lf-goals1 else 0 then ;   \ 0: closed, none
: lf-goals2 ( goal1 goal2 -- goals ) swap lf-goals1 swap run-push lf-tac-must ;
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
: tcr-arg-index ( i k -- j ) swap lf-tactic-step tac-first @ + ;
: tcr-arg ( i k -- x pos ) tcr-arg-index lf-tactic-arg ;
: lf-tac-arg ( i k -- x ) tcr-arg drop ;
: lf-tac-name ( i k -- name ) lf-tac-arg dup 0= if lf-tac-unported then ;
: lf-tac-arg-at ( i k -- pos ) tcr-arg nip ;
: lf-tac-arg-symm? ( i k -- flag ) tcr-arg-index lf-tactic-arg-symm? ;
: lf-tac-arg-span ( i k -- n ) tcr-arg-index lf-tactic-arg-span ;
: lf-tac-only ( goal -- ) lf-goals1 lf-goals! lf-tac-must ;

\ ---- A row on the step running; with_reducible rfl.
: lf-tac-row ( kind -- ) lf-tac-step swap lf-tac-eval ;
: lf-tac-rfl-reducible ( -- ) tac-k-rfl ['] lf-tac-row lf-with-reducible ;

\ ---- The elaborator's failure: its error, as Lean's throwError gives it.
\ One with a rest (elab-pending.fs's lf-elab-rest+, plan row TB2 batch
\ 3c): its term, when it has one, inline between blanks (inlineExpr),
\ then the rest, on the message's line; the text below it as the detail.
: tcr-rest. ( x -- outcome ) drop lf-elab-rest lf-pp-emit outcome-ok ;
: tcr-blank. ( -- outcome ) s"  " lf-pp-emit outcome-ok ;
: tcr-inline. ( term -- outcome )
  dup 0< if tcr-rest. exit then
  ['] tcr-blank. lf-tac-spaced. 0 swap ['] tcr-rest. ok-with nip ;
: tcr-rest-detail ( term -- )
  ['] tcr-inline. lf-tac-inline lf-elab-below ?dup if ['] execute lf-tac-detail then ;
: tcr-term-detail ( term -- )
  dup 0< if drop else ['] lf-tac-indented. lf-tac-detail then ;
: lf-tac-elab-detail ( -- )
  lf-elab-error-term lf-elab-rest nip if tcr-rest-detail else tcr-term-detail then ;
\ (Lean's logged class, tactic-run.fs's lf-tac-log-fail: final when the
\ block recovers, Elab/Tactic/ElabTerm.lean:31-39's errToSorry.)
: lf-tac-elab-fail ( outcome -- )
  lf-tac-elab-detail lf-elab-code lfa-see! lf-tac-log-fail ;

\ ---- withSynthesize: xt run under the pending list's window, the
\ window's mode (no postponing) given back above the caller's cells.
: tcr-under ( i*x xt mode -- j*x mode ) drop execute lf-postpone-no ;
: tcr-synthesized ( outcome -- ) dup ok? 0= if lf-tac-elab-fail then drop ;
: lf-tac-with-synth ( i*x xt -- j*x )
  ['] tcr-under lf-postpone-no lf-elab-with-synth tcr-synthesized ;

\ ---- try: first | xt | skip (Init/Tactics.lean:445), xt a non-last
\ alternative, run withoutRecover (Basic.lean:436-437's orElse);
\ tcr-try-kept: the same with the block's recover (a macro's rule).
: tcr-try-kept ( xt -- flag )
  lf-tac-try ?dup 0= if true exit then lf-tac-forget-lean false ;
: lf-tac-try-lean ( xt -- flag ) ['] tcr-try-kept lf-tac-no-recover ;

\ ---- first and a macro's rules: the alternative on top tried first; one
\ that ends is kept and the rest dropped (tcr-some: true), else the
\ deepest, the last, is left (false) and runs bare, so its error is the
\ one thrown. first tries them withoutRecover, a macro's rules with the
\ block's recover.
: tcr-some ( xtn..xt1 n -- xtn false | true )
  begin dup 1 > while swap tcr-try-kept if 1- ndrop true exit then 1- repeat drop false ;
: tcr-last ( xtn false | true -- ) 0= if execute then ;
: tcr-counted ( n -- n ) dup 0> 0= if outcome-invalid lf-must then ;
: lf-tac-first-of ( xtn..xt1 n -- ) tcr-counted ['] tcr-some lf-tac-no-recover tcr-last ;
: lf-tac-macro-alts ( xtn..xt1 n -- ) tcr-counted tcr-some tcr-last ;

\ ---- Tactic.elabTerm, elabTermEnsuringType, elabType.
: lf-tac-elab-term ( node expected postpone? -- e ) lf-tac-elab lf-tac-must ;
: lf-tac-elab-arg ( i k -- e ) lf-tac-arg -1 false lf-tac-elab-term ;
: lf-tac-elab-type ( node -- type ) lf-tac-elab-as-type lf-tac-must ;
: tcr-typed ( e expected -- e type expected ) over lf-infer lf-tac-must swap ;
: tcr-defeq ( type expected -- flag outcome ) ['] lf-tac-defeq lf-with-assignable-opaque ;
: tcr-ensured ( e type expected code -- e )
  >r 2dup tcr-defeq lf-tac-must if r> drop 2drop exit then r> lf-tac-type-mismatch ;
: lf-tac-ensure-type-as ( e expected code -- e ) >r tcr-typed r> tcr-ensured ;
: lf-tac-ensure-type ( e expected -- e ) lfa-e-tac-mismatch lf-tac-ensure-type-as ;
: lf-tac-elab-ensuring ( node expected -- e )
  tuck false lf-tac-elab-term swap lf-tac-ensure-type ;

\ ---- elabTermWithHoles (ElabTerm.lean:150-205, withCollectingNewGoalsFrom):
\ elabTermEnsuringType (no expected type: elabTerm), its new
\ metavariables collected (numbered from tb-from: the step's own), the
\ natural ones refused unless allowed (logUnassignedAndAbort); then, in
\ a word of its own, each anonymous one tagged from the main goal's tag
\ (tagUntaggedGoals); allowed, the elaboration runs with holes synthetic
\ opaque and those assignable (meta-config.fs's lf-with-holes-as-goals).
: tcr-ensuring ( node expected -- e )
  dup 0< if false lf-tac-elab-term else lf-tac-elab-ensuring then ;
: tcr-holes-elab ( node expected allow? -- e )
  if ['] tcr-ensuring lf-with-holes-as-goals else tcr-ensuring then ;
: lf-tac-new-goals ( e allow? -- goals )
  swap tb tb-from @ lf-fresh-mvars swap if exit then
  dup lf-natural-mvars lf-tac-log-unassigned ;
: lf-tac-elab-holes ( node expected allow? -- e goals )
  dup >r tcr-holes-elab dup r> lf-tac-new-goals ;
: lf-tac-tag-new ( goals suffix -- goals )
  over swap lf-tac-main lf-goal-tag lf-tag-untagged ;
\ refineCore stx `refine false (ElabTerm.lean:209-222), refine's and the
\ macros' that expand to it: node elaborated against goal's type with its
\ holes (natural ones refused), tagged refine, goal assigned the value.
: tcr-refine-holes ( node goal -- goal e goals )
  tuck lf-goal-type lf-instantiate! false lf-tac-elab-holes ;
: tcr-assign ( goal e -- ) lf-instantiate! lf-mvar-assign lf-must ;
: lf-tac-refine ( node goal -- goals )
  tcr-refine-holes c" refine" lf-tac-tag-new >r tcr-assign r> ;

\ ---- closeMainGoalUsing: the step's new metavariables (numbered from
\ tb-from) that the term leaves unassigned, logUnassignedAndAbort's
\ (new-goals.fs).
: tcr-fresh-free ( e -- e ) dup tb tb-from @ lf-fresh-mvars lf-tac-log-unassigned ;
: tcr-using ( i*x xt -- e )
  tb tb-want @ swap tb tb-goal @ lf-goal-tag swap execute lf-instantiate! ;
: tcr-assigned ( e -- ) tb tb-goal @ swap lf-goal-checked-assign lf-tac-pop-main ;
: tcr-closing ( i*x xt i -- ) drop tcr-using tcr-fresh-free tcr-assigned ;
: lf-close-main-goal-using ( i*x i xt -- ) swap ['] tcr-closing lf-tac-step-run ;
\ checkNewUnassigned := false: the term's open metavariables are xt's own.
: tcr-closing-unchecked ( i*x xt i -- ) drop tcr-using tcr-assigned ;
: lf-close-main-goal-unchecked ( i*x i xt -- )
  swap ['] tcr-closing-unchecked lf-tac-step-run ;

\ ---- elabTermForApply, with mayPostpone given.
: tcr-ident ( node postpone? -- e ) drop lf-elab-ident lf-tac-must ;
: tcr-term ( node postpone? -- e ) -1 swap lf-tac-elab-term ;
: tcr-for-apply ( node postpone? -- e )
  over lf-elab-ident? if tcr-ident else tcr-term then lf-instantiate! ;
: tcr-not-mvar ( e -- e ) dup lf-mvar? if lf-tac-unported then ;
: lf-tac-elab-for-apply ( node -- e ) true tcr-for-apply tcr-not-mvar ;

\ ---- getFVarId: elabTermForApply with no postponing, a free variable.
389 lfa-lean s" Unexpected term" lfa-code: lfa-e-tac-not-fvar
: tcr-expected. ( -- outcome )
  s" ; expected single reference to variable" lf-pp-emit outcome-ok ;
: tcr-unexpected. ( e -- outcome ) ['] tcr-expected. lf-tac-spaced. ;
: tcr-fvar ( e -- fvar )
  dup lf-meta-fvar? if exit then
  ['] tcr-unexpected. lf-tac-inline lfa-e-tac-not-fvar lf-tac-stop ;
: lf-tac-get-fvar ( node -- fvar ) false tcr-for-apply tcr-fvar ;

\ ---- Locations: step i's at[ ] (tactic-syntax.fs), expandOptLocation.
: tcr-loc ( i -- flags ) lf-tactic-step tac-loc @ ;
: lf-tac-located? ( i -- flag ) tcr-loc 0<> ;
: lf-tac-loc# ( i -- n ) lf-tactic-step tac-loc# @ ;
: lf-tac-loc-goal? ( i -- flag ) tcr-loc dup 0= swap tac-loc-goal and 0<> or ;
: lf-tac-loc-all? ( i -- flag ) tcr-loc tac-loc-all and 0<> ;
: tcr-loc-k ( i k -- i k' ) over lf-tac-args# + ;
: lf-tac-loc-hyp ( i k -- name ) tcr-loc-k lf-tac-arg ;
\ getFVarId of name k: the newest accessible local so named in the main
\ goal's context (resolveLocalName); else a constant of that name is
\ Lean's 389, not ported here (99), and no name at all Lean's unknown
\ identifier, 455 (at the step's word, as getFVarId's 389 is).
455 lfa-lean s" Unknown identifier" lfa-code: lfa-e-tac-unknown-id
: tcr-quoted. ( name -- outcome ) s"  " lf-pp-emit lf-tac-.name outcome-ok ;
: tcr-constant? ( name -- flag ) lf-menv-find nip ok? ;
: tcr-unknown ( name -- )
  dup tcr-constant? if lf-tac-unported then
  ['] tcr-quoted. lf-tac-inline lfa-e-tac-unknown-id lf-tac-stop ;
: lf-tac-name-fvar ( name -- fvar )
  dup lf-tac-main lf-goal-view swap lf-view-named-fvar if nip else tcr-unknown then ;
: lf-tac-loc-fvar ( i k -- fvar ) lf-tac-loc-hyp lf-tac-name-fvar ;
\ Step i's arguments as a run (a header's or a list's names, 0 for _),
\ and getFVarIds of them (by-revert[ and by-clear['s).
: lf-tac-arg-names ( i -- names )
  0 over lf-tac-args# 0 ?do over i lf-tac-arg run-push lf-tac-must loop nip ;
: tcr-fvar+ ( run name -- run' outcome ) lf-tac-name-fvar run-push ;
: lf-tac-arg-fvars ( i -- fvars )
  0 swap lf-tac-arg-names ['] tcr-fvar+ run-each lf-tac-must ;
\ withLocation's targets case, a frame per call (xt-local and xt-target
\ take and give the caller's values, which the stack holds beneath):
\ each name in order resolved in the main goal's context then given to
\ xt-local, then the goal to xt-target when named or at[ ] is absent. The
\ wildcard (at[ * ]) is not supported yet (99).
begin-structure /tlc
  field: tlc-step        \ the step whose at[ ] is read
  field: tlc-local       \ ( i*x fvar -- i*x )
  field: tlc-target      \ ( i*x -- i*x )
end-structure
/tlc context-slab: tlc-frames
: tlc ( -- frame ) tlc-frames slab-last ;
: tlc-hyp ( i*x k -- i*x ) tlc tlc-step @ swap lf-tac-loc-fvar tlc tlc-local @ execute ;
: tlc-hyps ( i*x -- i*x ) tlc tlc-step @ lf-tac-loc# 0 ?do i tlc-hyp loop ;
: tlc-goal ( i*x -- i*x )
  tlc tlc-step @ lf-tac-loc-goal? if tlc tlc-target @ execute then ;
: tlc-all ( -- ) tlc tlc-step @ lf-tac-loc-all? if lf-tac-unported then ;
: tlc-run ( i*x i xt-local xt-target -- i*x )
  tlc tlc-target ! tlc tlc-local ! tlc tlc-step ! tlc-all tlc-hyps tlc-goal ;
: lf-with-location ( i*x i xt-local xt-target -- i*x )
  tlc-frames ['] tlc-run lf-with-record ;
\ The same for a run word whose actions take step i alone: ( i -- i ) and
\ ( i fvar -- i ).
: lf-at-location ( i xt-local xt-target -- ) rot dup 2swap lf-with-location drop ;
\ Such actions of a goal operation (the header gives their xts).
: lf-lift-target1 ( i xt -- i ) over tuck swap lf-lift-meta-tactic1 ;
: lf-lift-local1 ( i fvar xt -- i ) >r over tuck r> lf-lift-meta-tactic1 ;
base !   \ the BASE this file was loaded with

\ MVarId.apply, the goal operation of the apply tactic (docs/design/
\ TACTIC_PLUGINS.md 2.4; slice a2-iii), a port of Lean 4.35.0's
\ src/lean/Lean/Meta/Tactic/Apply.lean, with the same choices in the
\ same order, building the same proof term:
\   lf-goal-apply ( goal e -- goals )  MVarId.apply (Apply.lean:169-232)
\       with ApplyConfig's defaults (approx, synthAssignedInstances, no
\       allowSynthFailures, newGoals nonDependentFirst). In goal's
\       context: getExpectedNumArgsAux of e's type (telescope.fs's
\       lf-expected-num-args) gives the range of argument counts: from
\       numArgs less the target's own count (numArgs alone when the
\       type's conclusion has a metavariable head) up to numArgs. For each
\       count in turn, from a saved state (lf-commit-when): a natural
\       metavariable per binder (synthetic for an instance binder, named
\       as the binder; forallMetaTelescopeReducing with maxMVars, kinds
\       from e's declaration when e is a constant) and isDefEqApply (the
\       configuration's flags with Lean's approxDefEq: foApprox, ctxApprox,
\       quasiPatternApprox) of what is left of the type with the goal's
\       type; the first that fits wins. None fits: throwApplyError, error
\       380 at the step running with Lean's text (the conclusion, made by
\       the telescope at the lowest count when that count is not 0, else
\       the type; the goal's type; the full type as a note; the goal).
\       Then postprocessAppMVars (synthAppInstances: every instance
\       metavariable's instance searched, rounds while one found after a
\       failure; none: error 125 with the type, Lean's "failed to
\       synthesize"; found but not defeq the metavariable: 384), the goal
\       assigned e (instantiated) applied to the new metavariables, the
\       unassigned ones kept, appendParentTag (one: the goal's tag; more,
\       under a tagged goal: tag.binder for each whose binder at the same
\       index of the unfiltered list, as Lean indexes it, is no instance
\       binder), reorderGoals nonDependentFirst (those no other new
\       metavariable's type names first, the others after, each in
\       order) and headBetaType of each (meta-tactic/goal.fs).
\ Not ported (unsupported, error 99, never a wrong answer): Lean's other
\ goals, the metavariables of e itself (getMVarsNoDelayed): e
\ instantiated must hold none. Lean's addPPExplicitToExposeDiff and
\ mkUnfoldAxiomsNote (empty outside a module) are not printed.
\ Lean call list (Apply.lean, one level down): withContext ->
\ lf-with-goal's caller (tactic-core.fs); checkNotAssigned ->
\ lf-goal-not-assigned (goal.fs); getType -> lf-mvar-type; inferType ->
\ lf-infer! (meta-must.fs); getExpectedNumArgsAux, getExpectedNumArgs ->
\ lf-expected-num-args (telescope.fs); saveState/restore -> lf-commit-when;
\ forallMetaTelescopeReducing -> lf-forall-meta-bounded-telescope;
\ approxDefEq isDefEqGuarded -> lf-meta-defeq-guarded under lf-meta-with;
\ synthInstance -> lf-synth-instance (synth.fs); isDefEq -> lf-defeq!;
\ instantiateMVars -> lf-instantiate!; mkAppN -> lf-mk-app-n's fold
\ (app-builder.fs); assign -> lf-mvar-assign; isAssigned ->
\ lf-goal-assigned?; getTag/setTag/appendTag -> lf-goal-tag-append
\ (goal.fs); findMVar? -> lf-term-holds?; headBetaType ->
\ lf-goal-head-beta-type (goal.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: the record ap (the call's goal, term and types) and the slabs
\ ap-news (the new metavariables with their binder kinds), ap-goals (the
\ unassigned ones, then the result) and ap-todo, ap-later (instances to
\ synthesize), in the checker context (ADR 0009); one apply runs at a time
\ (instance search never applies). Loads in decimal whatever BASE is, then
\ restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/slab.fs
require ../../lib/runs.fs
require ../../core/terms.fs
require ../../core/constant-term-boundary.fs
require ../../present/binder-table.fs
require ../../author/errors.fs
require ../mvars.fs
require ../meta-config.fs
require ../goals.fs
require ../meta-env.fs
require ../term-eqv.fs
require ../term-find.fs
require ../defeq.fs
require ../synth.fs
require ../tactic-run.fs
require ../tactic-basic.fs
require ../meta-must.fs
require ../app-builder.fs
require ../telescope.fs
require ./goal.fs

380 outcome-invalid s" Tactic `apply` failed: could not unify the" lfa-code: lfa-e-apply
384 outcome-invalid s" Tactic `apply` failed: failed to assign synthesized instance"
  lfa-code: lfa-e-apply-inst

begin-structure /ap
  field: ap-goal         \ the goal
  field: ap-e            \ the term applied
  field: ap-etype        \ its type
  field: ap-target       \ the goal's type
  field: ap-d            \ e's declaration when e is a constant, else -1
  field: ap-lower        \ the range of argument counts
  field: ap-upper
  field: ap-sought       \ the metavariable findMVar? looks for (its number)
end-structure
/ap context-record: ap
2 cells context-slab: ap-news   \ (mvar, kind): Lean's newMVars and binderInfos
1 cells context-slab: ap-goals
1 cells context-slab: ap-todo
1 cells context-slab: ap-later

\ ---- The new metavariables.
: ap-new# ( -- n ) ap-news slab-count ;
: ap-new ( k -- mvar kind ) ap-news slab-at 2@ ;
: ap-new+ ( acc mvar kind -- acc ) ap-news slab-2push lf-must ;
: ap-inst? ( k -- flag ) ap-new nip lf-binder-instance = ;

\ ---- The range of argument counts (Lean's rangeNumArgs).
: ap-d! ( e -- )
  dup lf-term-const? if lf-const-name lf-menv-find lf-must else drop -1 then ap ap-d ! ;
: ap-range ( -- )
  ap ap-etype @ lf-expected-num-args swap dup ap ap-upper ! swap if ap ap-lower ! exit then
  ap ap-target @ lf-expected-num-args drop - 0 max ap ap-lower ! ;

\ ---- One count: the telescope, then isDefEqApply.
: ap-flags ( -- flags ) lf-defeq-flags lf-defeq-fo or lf-defeq-ctx or lf-defeq-quasi or ;
: ap-defeq ( t s -- flag )
  ['] lf-meta-defeq-guarded ap-flags lf-defeq-mode lf-meta-with outcome-sane lf-must ;
: ap-telescope ( i -- body )
  >r 0 ap ap-etype @ ap ap-d @ r> ['] ap-new+ lf-forall-meta-bounded-telescope nip ;
: ap-try ( i -- flag ) ap-news slab-clear ap-telescope ap ap-target @ ap-defeq ;
: ap-fits? ( i -- flag ) ['] ap-try lf-commit-when ;

\ ---- throwApplyError (error 380).
: ap-conclusion? ( -- flag ) ap ap-lower @ 0<> ;
: ap-what ( -- c-addr u ) ap-conclusion? if s"  conclusion of " else s"  type of " then ;
: ap-head. ( x -- outcome ) drop ap-what lf-pp-emit ap ap-e @ lf-tac-inline. ;
: ap-concl ( -- t ) ap-conclusion? if ap ap-lower @ ap-telescope else ap ap-etype @ then ;
: ap-full. ( -- outcome ) s\"  is\n" ap ap-etype @ lf-tac-line. ;
: ap-note. ( -- outcome )
  ap-conclusion? 0= if outcome-ok exit then
  s\" \n\nNote: The full type of " lf-pp-emit ap ap-e @ lf-tac-inline. ['] ap-full. ok-and ;
: ap-with. ( -- outcome ) s\" \nwith the goal\n" ap ap-target @ lf-tac-line. ;
: ap-goal. ( -- outcome ) s\" \n" lf-pp-emit ap ap-goal @ lf-tac-goal-of. ;
: ap-unify. ( concl -- outcome )
  lf-tac-indented. ['] ap-with. ok-and ['] ap-note. ok-and ['] ap-goal. ok-and ;
: ap-unify-fail ( -- )
  0 ['] ap-head. lf-tac-inline ap-concl ['] ap-unify. lf-tac-detail lfa-e-apply lf-tac-stop ;
: ap-search ( -- )
  ap ap-upper @ 1+ ap ap-lower @ ?do i ap-fits? if unloop exit then loop ap-unify-fail ;

\ ---- synthAppInstances: rounds over the instance metavariables.
: ap-insts ( -- ) ap-todo slab-clear
  ap-new# 0 ?do i ap-inst? if i ap-new drop ap-todo slab-push lf-must then loop ;
: ap-type. ( mvar -- outcome ) lf-mvar-type drop lf-tac-indented. ;
: ap-no-instance ( mvar -- ) ['] ap-type. lf-tac-detail lfa-e-elab-synth lf-tac-stop ;
: ap-assign-inst ( mvar inst -- )
  lf-defeq! 0= if ap ap-goal @ ['] lf-tac-goal-of. lf-tac-detail lfa-e-apply-inst lf-tac-stop
  then ;
\ One metavariable: found (true), else put off (false).
: ap-synth-one ( mvar -- found? )
  dup lf-infer! lf-synth-instance lf-must if ap-assign-inst true exit then
  drop ap-later slab-push lf-must false ;
\ A round: ( failed progress ), Lean's ex? (the last metavariable not
\ found, else 0) and progressAfterEx (one found after a failure).
: ap-tried ( failed progress mvar found? -- failed' progress' )
  if drop over 0<> or else rot drop swap then ;
: ap-round ( -- failed progress )
  ap-later slab-clear 0 false
  ap-todo slab-count 0 ?do i ap-todo slab-at @ dup ap-synth-one ap-tried loop ;
: ap-again ( -- )
  ap-todo slab-clear ap-later slab-count 0 ?do i ap-later slab-at @ ap-todo slab-push lf-must
  loop ;
: ap-synth-instances ( -- )
  ap-insts begin ap-todo slab-count while ap-round
    over 0= if 2drop ap-todo slab-clear else if drop ap-again else ap-no-instance then then
  repeat ;

\ ---- The goal assigned, the new goals.
: ap-applied ( -- e )
  ap ap-e @ lf-instantiate! ap-new# 0 ?do i ap-new drop lf-mk-app loop ;
: ap-assign ( -- ) ap ap-goal @ ap-applied lf-mvar-assign lf-must ;
: ap-unassigned ( -- )
  ap-goals slab-clear ap-new# 0 ?do i ap-new drop dup lf-goal-assigned?
    if drop else ap-goals slab-push lf-must then loop ;
: ap-goal@ ( k -- mvar ) ap-goals slab-at @ ;
: ap-tag ( -- tag ) ap ap-goal @ lf-mvar-tag drop ;
\ appendParentTag: binderInfos indexed as the unfiltered list (Lean's).
: ap-tag-one ( k -- )
  dup ap-inst? if drop exit then ap-goal@ ap-tag lf-goal-tag-append ;
: ap-parent-tag ( -- )
  ap-goals slab-count 1 = if 0 ap-goal@ ap-tag lf-mvar-tag! lf-must exit then
  ap-tag 0= if exit then ap-goals slab-count 0 ?do i ap-tag-one loop ;
\ getMVarsNoDelayed e: not ported; e instantiated must hold no metavariable.
: ap-open? ( leaf -- flag ) dup lf-mvar? if lf-goal-assigned? 0= else drop false then ;
: ap-alone ( -- )
  ap ap-e @ lf-instantiate! ['] ap-open? lf-term-holds? lf-must
  if lfa-e-tac-form lf-tac-fail then ;

\ ---- reorderGoals nonDependentFirst, then headBetaType.
: ap-sought? ( leaf -- flag )   \ (inside lf-term-holds?'s walk: throws nothing)
  dup lf-mvar? if lf-term-first@ ap ap-sought @ = else drop false then ;
: ap-names? ( mvar other -- flag )   \ other's type, as stored, holds mvar
  2dup = if 2drop false exit then
  swap lf-term-first@ ap ap-sought ! lf-mvar-type drop ['] ap-sought? lf-term-holds? lf-must ;
: ap-dependent? ( mvar -- flag )
  ap-goals slab-count 0 ?do dup i ap-goal@ ap-names? if drop true unloop exit then loop
  drop false ;
: ap-push ( run mvar -- run ) lf-goal-head-beta-type run-push lf-must ;
: ap-those ( run dependent? -- run )
  ap-goals slab-count 0 ?do i ap-goal@ dup ap-dependent? 2 pick = if swap >r ap-push r>
    else drop then loop drop ;
: ap-result ( -- goals ) 0 false ap-those true ap-those ;

\ (The goal's type and e's are instantiated first: LeanForth's Meta words
\ take instantiated terms, Lean's isDefEq instantiates as it goes, and
\ Lean's messages print them instantiated; nothing else differs.)
: ap-run ( -- goals )
  ap ap-goal @ lf-goal-not-assigned lf-mvar-type drop lf-instantiate! ap ap-target !
  ap ap-e @ dup ap-d! lf-infer! lf-instantiate! ap ap-etype ! ap-range ap-search
  ap-synth-instances
  ap-assign ap-unassigned ap-parent-tag ap-alone ap-result ;
: lf-goal-apply ( goal e -- goals ) ap ap-e ! ap ap-goal ! ap-run ;
base !   \ the BASE this file was loaded with

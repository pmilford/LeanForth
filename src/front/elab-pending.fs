\ Pending instance problems and default instances (plan S1, FE1e6; design
\ docs/design/FE1E_APPLICATIONS.md 2.5, docs/design/S1_INTERFACE.md), after
\ Lean 4.35.0's Elab/SyntheticMVars.lean (synthesizeSyntheticMVars and its
\ step, synthesizeUsingDefault, withSynthesize, withSynthesizeLight) and
\ Elab/Term/TermElabM.lean (synthesizeInstMVarCore, mkInstMVar). The
\ elaborator (elab-app.fs, elab-term.fs) registers here the instance
\ metavariables it cannot fill yet, and here they are filled when they can.
\ - The pending list (Lean's pendingMVars): instance metavariables, oldest
\   first, each with the position of the syntax that made it. A window
\   hides the entries below its base, as withSynthesize and
\   withSynthesizeLight set the list aside and put it back after theirs:
\   lf-elab-window{ ( -- saved ), }lf-elab-window ( saved -- );
\   lf-elab-pending# ( -- n ) counts the window.
\ - lf-elab-synthesize ( mode -- outcome ), synthesizeSyntheticMVars: the
\   step (each entry of the window, oldest first, through
\   synthesizeInstMVarCore; those not filled stay, before any made
\   meanwhile) while it fills one; with lf-postpone-yes nothing more;
\   otherwise Lean's further rounds, the step again, default instances, the
\   step twice more (the same for instance problems), and with
\   lf-postpone-no an entry still left is Lean's "typeclass instance problem
\   is stuck" (126), at the oldest (Lean reports the smallest syntax range,
\   the earliest first: of S1's problems the first made); lf-postpone-check
\   leaves it (#check's ignoreStuckTC). Default instances
\   (synthesizeUsingDefault): for each priority a default instance has
\   (elab-data.fs's records), highest first, the first entry of the window
\   that one of its class's default instances of that priority fills, in
\   Lean's list order (the most recent first), each tried under a mark
\   (commitWhen): the instance at new universe metavariables applied to a
\   new metavariable per binder (forallMetaTelescopeReducing: synthetic for
\   an instance binder, natural otherwise, kinds from the declared type,
\   lf-menv-kind@; a pi that only whnf shows is 136), isDefEqGuarded with
\   synthetic opaque metavariables assignable, then its instance binders
\   filled, the last binder first as Lean prepends them (synthesizePending:
\   by instances while that fills one, else one by a default instance of any
\   priority, again). Without elaboration data default instances are unknown
\   (139). The recursion runs as lib/frame.fs steps on heap stacks, no host
\   recursion.
\ - lf-elab-synth-core ( mvar -- flag outcome ), synthesizeInstMVarCore:
\   the type instantiated, trySynthInstance (synth.fs's lf-try-synth,
\   through defeq.fs's hook lf-meta-synth; undef, the stuck signal, is
\   false: try later); found: assigned by isDefEq (false: 129, "failed to
\   assign"), or, already assigned, compared with the value (false is
\   139: Lean's containsPendingMVar test is not ported); none: Lean's
\   "failed to synthesize" (125); a search that fails with a code of its
\   own (synth.fs's 110-121) records that code.
\   lf-elab-inst-mvar ( type -- mvar outcome ), mkInstMVar: a new
\   synthetic metavariable, pending when it cannot be filled yet.
\ - Errors (Lean's throwError at the current ref): lf-elab-at! ( pos -- ),
\   lf-elab-at ( -- pos ); lf-elab-fail ( code -- outcome ) records the
\   first error at the position and gives the code's outcome
\   (author/errors.fs); lf-elab-error ( -- code pos ) (0 -1: none);
\   lf-elab-error-reset; lf-elab-meta ( outcome -- outcome ) records a
\   Meta step's failure: no room 60, fuel 138, unsupported 139, else 76.
\   lf-elab-catch ( outcome -- flag ), Lean's try ... catch _ (commitWhen,
\   trySynthesizeAppInstMVars): true for a Lean error (invalid with a
\   recorded code other than 76), which is forgotten; false for anything
\   else, which goes on: malformed or corrupt state, unsupported,
\   exhausted (Lean's runtime limits are not caught either), full.
\ - The trace (FE1E 1.6, for tests): lf-elab-trace! ( flag -- ),
\   lf-elab-trace ( -- c-addr u ), one event a line; lf-elab-note
\   ( c-addr u -- ), lf-elab-term. ( term -- ) and lf-elab-n. ( n -- )
\   write while it is on (lf-elab-nl ends a line). Lazy delta's unfolding
\   (defeq-delta.fs's hook lf-delta-unfolded, set here) is a line
\   "unfold HEAD", Lean's trace.Meta.isDefEq.delta.
\ - Shared words of the elaborator: lf-elab-defeq, lf-elab-guarded ( t s
\   -- flag outcome ): isDefEq, isDefEqGuarded, made sane (the stuck
\   signal never leaves the Meta layer); lf-elab-spend ( -- outcome ): one
\   step of the budget (meta-config.fs), exhausted when none is left;
\   lf-elab-frames-ready ( frames -- frames ): an idle frame record reset
\   for a pass, a busy one (a nested pass) left as it is. Constants come
\   from mvars.fs's lf-meta-const-fresh and meta-env.fs's
\   lf-meta-const-at.
\ - The instance tables (front/instances.fs) through deferred words a
\   test may stand in for: lf-elab-class? ( type -- class true outcome |
\   false outcome ), isClass? (lf-class?), and lf-elab-default-instances
\   ( class -- addr n outcome ), getDefaultInstances (lf-default-instances:
\   default-instance record numbers by rank, a negative cell a gap,
\   unsupported when a search reaches it).
\ Outcomes: ok; invalid for Lean's errors (recorded with their codes);
\ unsupported; exhausted; full when a slab cannot grow. Untrusted: only
\ the kernel's check of a finished term decides anything.
\ State: the record ep (window, position, first error, trace switch, the
\ priorities' sorter), the frames ep-frames and the slabs ep-pending,
\ ep-scratch, ep-prios, ep-defs, ep-goals, ep-bs, ep-cs and ep-trace, in
\ the checker context (ADR 0009); lf-elab-pending-reset empties them.
\ Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/sort.fs
require ../core/terms.fs
require ../core/levels.fs
require ../core/names.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/mvar-leaves.fs
require ../core/reach.fs
require ../present/print-job.fs
require ../present/term-printer.fs
require ../author/errors.fs
require ./mvars.fs
require ./meta-config.fs
require ./meta-env.fs
require ./elab-data.fs
require ./instantiate.fs
require ./whnf.fs
require ./infer.fs
require ./defeq.fs
require ./defeq-delta.fs
require ./instances.fs
require ./synth.fs
require ../lib/decimal.fs

0 constant lf-postpone-yes   1 constant lf-postpone-partial   2 constant lf-postpone-no
3 constant lf-postpone-check   \ no, a stuck problem left (#check's ignoreStuckTC)

begin-structure /ep
  field: ep-base      \ the window's first pending entry
  field: ep-at        \ the position elaboration works at (Lean's ref)
  field: ep-code      \ the first error's code, 0: none
  field: ep-where     \ and its position
  field: ep-tracing   \ true: events go to ep-trace
  /sorter +field ep-sorter   \ the priorities, highest first
end-structure
/ep context-record: ep
2 cells context-slab: ep-pending   \ (mvar, position) by 2!, oldest first
2 cells context-slab: ep-scratch   \ a step's entries, then those it keeps
1 cells context-slab: ep-prios     \ the default instances' priorities, highest first
1 cells context-slab: ep-defs      \ default-instance records, a range per attempt
1 cells context-slab: ep-goals     \ synthesizePending's lists, a range each
1 chars context-slab: ep-trace     \ the trace's text
begin-structure /epb   \ synthesizeUsingDefault[Prio] on one metavariable
  field: epb-mvar
  field: epb-only      \ the one priority to try, or -1: each in turn
  field: epb-defs      \ its class's default instances: first cell in ep-defs
  field: epb-p         \ the priority tried: its index in ep-prios
  field: epb-j         \ the next default instance to look at
  field: epb-mark      \ the mark of the attempt in progress (commitWhen)
  field: epb-goals     \ the attempt's instance binders: first cell in ep-goals
  field: epb-d         \ the attempt's instance (a declaration)
  field: epb-app       \ the instance applied to the binders' metavariables so far
  field: epb-type      \ the rest of its type
  field: epb-k         \ the binders entered
end-structure
/epb context-slab: ep-bs
begin-structure /epc   \ synthesizePending on a list of metavariables
  field: epc-first     \ the list: its first cell in ep-goals, to the top
  field: epc-i         \ the next to try a default instance on
end-structure
/epc context-slab: ep-cs

\ ---- The trace.
: lf-elab-trace! ( flag -- ) ep ep-tracing ! ;
: lf-elab-trace ( -- c-addr u ) 0 ep-trace slab-at ep-trace slab-count ;
: ep-tracing? ( -- flag ) ep ep-tracing @ ;
: ep-chars ( c-addr u -- )
  dup ep-trace slab-claim ok? if ep-trace slab-at swap move else 2drop drop then ;
: lf-elab-note ( c-addr u -- ) ep-tracing? if ep-chars else 2drop then ;
: lf-elab-nl ( -- ) s\" \n" lf-elab-note ;
: lf-elab-n. ( n -- ) ep-tracing? if u>decimal ep-chars else drop then ;

\ ---- Errors and the position (Lean's ref and throwError).
: lf-elab-at! ( pos -- ) ep ep-at ! ;
: lf-elab-at ( -- pos ) ep ep-at @ ;
: lf-elab-error ( -- code pos ) ep ep-code @ ep ep-where @ ;
: lf-elab-error-reset ( -- ) 0 ep ep-code ! -1 ep ep-where ! ;
: ep-error. ( code -- code ) s" error " lf-elab-note dup lf-elab-n. lf-elab-nl ;
: ep-record ( code -- )
  ep ep-code @ if drop exit then ep-error. ep ep-code ! lf-elab-at ep ep-where ! ;
: lf-elab-fail ( code -- outcome ) dup ep-record lf-author-outcome ;
: ep-meta-code ( outcome -- code )
  case outcome-full of lfa-e-terms-full endof outcome-exhausted of lfa-e-elab-fuel endof
    outcome-unsupported of lfa-e-elab-step endof lfa-e-malformed swap endcase ;
: lf-elab-meta ( outcome -- outcome ) dup ok? if exit then dup ep-meta-code ep-record ;
\ A failure's error: the one recorded with its position, else the
\ outcome's code at no position (-1).
: lf-elab-code ( outcome -- code pos )
  lf-elab-error over if rot drop else 2drop ep-meta-code -1 then ;
\ A Lean error that a caller's try ... catch takes (commitWhen): forgotten.
: ep-lean-error? ( outcome -- flag )
  outcome-invalid = ep ep-code @ dup 0<> swap lfa-e-malformed <> and and ;
: lf-elab-catch ( outcome -- flag ) ep-lean-error? dup if lf-elab-error-reset then ;
: lf-elab-spend ( -- outcome )
  lf-meta-spend? if outcome-ok else lfa-e-elab-fuel lf-elab-fail then ;

\ ---- The trace's terms, printed plain to the trace's text (a print that
\ fails leaves its part there: the trace is for tests).
: lf-elab-term. ( term -- )
  ep-tracing? if ['] ep-chars false lf-print-to drop else drop then ;
: ep-mvar. ( mvar -- ) s" ?" lf-elab-note lf-term-first@ lf-elab-n. ;
: ep-unfold. ( e -- )
  ep-tracing? if s" unfold " lf-elab-note lf-meta-head lf-elab-term. lf-elab-nl
  else drop then ;
' ep-unfold. is lf-delta-unfolded

\ ---- The instance tables (front/instances.fs): isClass? and
\ getDefaultInstances, deferred so that a test can stand in for them.
defer lf-elab-class? ( type -- class true outcome | false outcome )
' lf-class? is lf-elab-class?
defer lf-elab-default-instances ( class -- addr n outcome )
' lf-default-instances is lf-elab-default-instances

\ ---- Whether a term reaches a metavariable, term or level
\ (core/reach.fs's tables, made for the question and freed).
: lf-elab-holes? ( term -- flag outcome )
  lf-reach-open 0= if drop false outcome-full exit then
  lf-reach-term lf-reach-sweep lf-reach-holes? lf-reach-close outcome-ok ;
\ The term kept when it reaches no metavariable, else the error code.
: lf-elab-closed ( term code -- term outcome )
  >r dup lf-elab-holes? ok-then? 0= if r> drop exit then
  if r> lf-elab-fail else r> drop outcome-ok then ;

\ ---- The Meta layer seen from the elaborator: its outcomes made sane.
: lf-elab-defeq ( t s -- flag outcome ) lf-meta-defeq outcome-sane ;
: lf-elab-guarded ( t s -- flag outcome ) lf-meta-defeq-guarded outcome-sane ;

\ ---- The pending list and its window.
: ep-count ( -- n ) ep-pending slab-count ;
: lf-elab-pending# ( -- n ) ep-count ep ep-base @ - ;
: ep-window-at ( k -- addr ) ep ep-base @ + ep-pending slab-at ;
: lf-elab-window{ ( -- saved ) ep ep-base @ ep-count ep ep-base ! ;
: }lf-elab-window ( saved -- ) ep ep-base ! ;
: ep-window-cut ( -- ) ep ep-base @ ep-pending slab-cut ;
: lf-elab-pend ( mvar -- outcome )
  s" pending " lf-elab-note dup ep-mvar. lf-elab-nl lf-elab-at ep-pending slab-2push ;
\ Entry k of the window taken out, the later ones moved down.
: ep-remove ( k -- ) ep ep-base @ + ep-pending slab-remove ;

\ ---- synthesizeInstMVarCore over trySynthInstance's answer (synth.fs's
\ lf-synth-some, lf-synth-none, lf-synth-undef: the stuck signal). A
\ failed search records its own code when it set one of that outcome.
: ep-synth-code? ( outcome -- code true | false )
  lf-synth-error dup 0= if 2drop false exit then
  tuck lf-author-outcome = if true else drop false then ;
: ep-synth-failed ( outcome -- outcome )
  dup ep-synth-code? if ep-record else lf-elab-meta then ;
: ep-synth-type ( mvar -- type outcome )
  lf-mvar-type 0= if -1 outcome-invalid exit then lf-instantiate-mvars ;
: ep-assigned? ( mvar -- flag ) lf-mvar-value dup if nip then ;
: ep-judged ( flag outcome code -- flag outcome )
  >r dup ok? 0= if r> drop lf-elab-meta exit then drop
  if r> drop true outcome-ok else false r> lf-elab-fail then ;
: ep-again ( mvar inst -- flag outcome )
  swap lf-instantiate-mvars ok-then? 0= if nip false swap lf-elab-meta exit then
  swap lf-elab-defeq lfa-e-elab-step ep-judged ;
: ep-found ( mvar inst -- flag outcome )
  over ep-assigned? if ep-again else lf-elab-defeq lfa-e-elab-instance ep-judged then ;
: ep-none ( mvar -- flag outcome ) drop false lfa-e-elab-synth lf-elab-fail ;
: ep-answer-text ( code -- c-addr u )
  case lf-synth-some of s" : found" endof lf-synth-none of s" : none" endof
    >r s" : stuck" r> endcase ;
: ep-synth. ( type inst code -- inst code )
  ep-tracing? 0= if rot drop exit then s" synth " lf-elab-note rot lf-elab-term.
  dup ep-answer-text lf-elab-note lf-elab-nl ;
: ep-answered ( mvar inst code -- flag outcome )
  case lf-synth-some of ep-found endof lf-synth-none of drop ep-none endof
    >r 2drop false outcome-ok r> endcase ;
: lf-elab-synth-core ( mvar -- flag outcome )
  dup ep-synth-type ok-then? 0= if nip false swap lf-elab-meta exit then
  dup lf-try-synth ok-then2? 0= if nip nip false swap ep-synth-failed exit then
  ep-synth. ep-answered ;

\ ---- mkInstMVar.
: ep-pend ( mvar flag outcome -- mvar outcome )
  dup ok? 0= if nip exit then drop if outcome-ok else dup lf-elab-pend then ;
: lf-elab-inst-mvar ( type -- mvar outcome )
  mv-synthetic lf-mvar-new lf-elab-meta ok-then? 0= if no-result exit then
  dup lf-elab-synth-core ep-pend ;

\ ---- The step: the window's entries to ep-scratch (from first), the
\ window emptied; each resumed; those not filled, then the entries made
\ meanwhile, back in the window.
: ep-scratch-at ( i -- addr ) ep-scratch slab-at ;
: ep-scratch-cut ( first -- ) ep-scratch slab-cut ;
: ep-to-scratch ( k -- outcome ) ep-window-at 2@ ep-scratch slab-2push ;
: ep-take ( -- first n outcome )
  ep-scratch slab-count lf-elab-pending# dup ['] ep-to-scratch ok-each
  dup ok? if ep-window-cut then ;
: ep-resumed. ( mvar flag -- flag )
  ep-tracing? 0= if nip exit then s" resume " lf-elab-note swap ep-mvar.
  dup if s" : succeeded" else s" : not ready" then lf-elab-note lf-elab-nl ;
\ An entry resumed (at its syntax's position): kept when not filled.
: ep-keep ( mvar pos filled? -- outcome )
  if 2drop outcome-ok else ep-scratch slab-2push then ;
: ep-try-entry ( mvar pos -- outcome )
  dup lf-elab-at! over lf-elab-synth-core ok-then? 0= if nip nip exit then
  >r over r> ep-resumed. ep-keep ;
: ep-resume ( first k -- first outcome ) over + ep-scratch-at 2@ ep-try-entry ;
: ep-resume-all ( first n -- first n outcome ) 2dup ['] ep-resume ok-each nip ;
: ep-kept ( first n -- from m ) + ep-scratch slab-count over - ;
: ep-to-window ( i -- outcome ) ep-scratch-at 2@ ep-pending slab-2push ;
: ep-back ( from m -- outcome )
  over + swap ?do i ep-to-window dup ok? 0= if unloop exit then drop loop outcome-ok ;
: ep-merge ( first n -- outcome )
  lf-elab-pending# ['] ep-to-scratch ok-each dup ok? 0= if nip nip exit then
  drop ep-window-cut ep-kept ep-back ;
: ep-abandon ( first outcome -- false outcome ) swap ep-scratch-cut false swap ;
: ep-step ( -- progress outcome )
  ep-take dup ok? 0= if nip ep-abandon exit then drop
  ep-resume-all dup ok? 0= if nip ep-abandon exit then drop
  2dup ep-kept nip over <> >r over >r ep-merge r> ep-scratch-cut r> swap ;

\ ---- Default instances: the priorities any default instance has, each
\ once, highest first (Lean's getDefaultInstancesPriorities, a set), from
\ the data.
: ep-prio@ ( i -- p ) ep-prios slab-at @ ;
: ep-prio-new? ( p -- flag ) ep-prios slab-base ep-prios slab-count cells-has? 0= ;
: ep-prio+ ( i -- outcome )
  elab-default@ nip nip dup ep-prio-new? if ep-prios slab-push else drop outcome-ok then ;
: ep-desc ( p1 p2 -- n ) swap sort-signed ;
: ep-prios-sort ( -- outcome )
  ['] ep-desc ep ep-sorter sorter-cells dup ok? 0= if exit then
  drop ep-prios slab-base ep-prios slab-count ep ep-sorter sort-records ;
: ep-prios-ready ( -- outcome )
  elab-loaded? 0= if lfa-e-elab-step lf-elab-fail exit then
  ep-prios slab-clear elab-default elab-count ['] ep-prio+ ok-each
  ['] ep-prios-sort ok-and ;

\ ---- The frames: a visit takes two cells (a b) and gives (result
\ outcome); one step of the budget each.
: ep-refuse ( a b frames cont outcome -- -1 outcome frames cont )
  2>r nip nip -1 swap 2r> -rot ;
: ep-admit ( frames -- outcome )
  frame-admit dup ok? if drop lf-elab-spend then ;
: lf-elab-open ( a b frames cont xt -- ... frames next )
  >r over ep-admit dup ok? if drop r> frame-open else r> drop ep-refuse then ;
: ep-visit-none ( x frames -- x frames 0 ) 0 ;
' ep-visit-none context-frames: ep-frames
\ A pass's frames: reset when idle; a busy record (a step running a
\ nested pass) goes on from the cells in use.
: lf-elab-frames-ready ( frames -- frames )
  dup frame-busy? 0= if dup frame-reset max-n over frame-budget drop then ;
defer ep-c-call ( first x frames cont -- ... frames next )

\ ---- B: synthesizeUsingDefault (each priority) or synthesizeUsingDefaultPrio
\ (only one) on a metavariable: its class's default instances, the
\ attempts in Lean's order, each under a mark.
: epb ( -- addr ) ep-bs slab-last ;
: ep-defs-cut ( first -- ) ep-defs slab-cut ;
: ep-goals-cut ( first -- ) ep-goals slab-cut ;
: ep-b-fill ( m only addr -- )
  dup /epb erase tuck epb-only ! tuck epb-mvar ! ep-defs slab-count swap epb-defs ! ;
: ep-b-new ( m only -- outcome )
  1 ep-bs slab-claim ok-then? if ep-bs slab-at ep-b-fill outcome-ok else nip nip then ;
: ep-b-end ( flag outcome frames -- flag outcome frames 0 )
  epb epb-defs @ ep-defs-cut ep-bs slab-drop 0 ;
: ep-defs+ ( addr n -- outcome )
  dup ep-defs slab-claim ok-then? 0= if nip nip exit then
  ep-defs slab-at swap cells move outcome-ok ;
: ep-b-defaults ( class -- outcome )
  lf-elab-default-instances ok-then2? if ep-defs+ then ;
: ep-b-type ( -- type ) epb epb-mvar @ lf-mvar-type drop ;
\ The attempts: priority p (one, or each of ep-prios), default instance j.
: ep-only? ( -- flag ) epb epb-only @ 0< 0= ;
: ep-prio ( -- p ) ep-only? if epb epb-only @ else epb epb-p @ ep-prio@ then ;
: ep-prios# ( -- n ) ep-only? if 1 else ep-prios slab-count then ;
: ep-defs# ( -- n ) ep-defs slab-count epb epb-defs @ - ;
: ep-b-wrap ( -- )
  epb epb-j @ ep-defs# < if exit then 0 epb epb-j ! 1 epb epb-p +! ;
: ep-b-done? ( -- flag ) epb epb-p @ ep-prios# < 0= ;
: ep-b-taken ( -- v ) epb epb-j @ epb epb-defs @ + ep-defs slab-at @ 1 epb epb-j +! ;
: ep-b-hit? ( v -- v flag )
  dup lf-default-gap? if true exit then dup elab-default@ nip nip ep-prio = ;
\ The next default instance of the priority tried, or a gap; false when
\ none is left (a class with none: at once).
: ep-b-find ( -- v true | false )
  ep-defs# 0= if false exit then
  begin ep-b-wrap ep-b-done? if false exit then ep-b-taken ep-b-hit? 0= while drop repeat
  true ;
\ forallMetaTelescopeReducing over the attempt's type, the binders' kinds
\ from its declared type; its instance binders' metavariables pushed on
\ ep-goals.
: ep-t-kind ( -- kind true | false ) epb epb-d @ epb epb-k @ lf-menv-kind@ ;
: ep-t-mvar ( kind -- mvar outcome )
  lf-binder-instance = if mv-synthetic else mv-natural then
  epb epb-type @ lf-term-first@ swap lf-mvar-new lf-elab-meta ;
: ep-t-goal ( mvar kind -- outcome )
  lf-binder-instance = if ep-goals slab-push else drop outcome-ok then ;
: ep-t-apply ( mvar -- outcome )
  epb epb-app @ swap lf-term-app if epb epb-app ! outcome-ok else outcome-full then ;
: ep-t-open ( mvar -- outcome )
  epb epb-type @ lf-term-second@ swap lf-meta-instantiate1 lf-elab-meta
  ok-then? if epb epb-type ! outcome-ok then ;
: ep-t-binder ( -- outcome )
  ep-t-kind 0= if lfa-e-elab-binder lf-elab-fail exit then
  dup ep-t-mvar ok-then? 0= if nip exit then tuck swap ep-t-goal
  ['] ep-t-apply ok-with ['] ep-t-open ok-with nip 1 epb epb-k +! ;
: ep-t-end ( -- outcome )
  epb epb-type @ lf-meta-whnf lf-elab-meta ok-then? 0= if exit then
  lf-term-pi? if lfa-e-elab-binder lf-elab-fail else outcome-ok then ;
: ep-telescope ( -- outcome )
  begin epb epb-type @ lf-term-pi? while ep-t-binder dup ok? 0= if exit then drop repeat
  ep-t-end ;
: ep-b-start ( v -- outcome )
  elab-default@ drop nip lf-menv-of-data ok-then? 0= if exit then
  dup epb epb-d ! lf-meta-const-fresh ok-then? 0= if exit then
  dup epb epb-app ! lf-infer lf-elab-meta ok-then? 0= if exit then
  epb epb-type ! 0 epb epb-k ! ep-telescope ;
\ isDefEqGuarded with synthetic opaque metavariables assignable
\ (withAssignableSyntheticOpaque).
: ep-opaque ( -- flags mode ) lf-defeq-flags lf-defeq-opaque or lf-defeq-mode ;
: ep-b-unify ( -- flag outcome )
  epb epb-mvar @ epb epb-app @ ['] lf-elab-guarded ep-opaque lf-meta-with lf-elab-meta ;
: ep-b-attempt ( v -- flag outcome )
  ep-b-start dup ok? if drop ep-b-unify else false swap then ;
: ep-b-undo ( -- outcome ) epb epb-goals @ ep-goals-cut epb epb-mark @ lf-mctx-rollback ;
: ep-b-default. ( flag -- flag )
  ep-tracing? 0= if exit then s" default " lf-elab-note epb epb-mvar @ ep-mvar.
  s"  " lf-elab-note epb epb-d @ lf-menv-name lf-name-text lf-elab-note
  dup if s" : ok" else s" : rolled back" then lf-elab-note lf-elab-nl ;
: ep-b-failed ( flag outcome frames -- flag outcome frames 0 )
  >r ep-b-undo outcome-and r> ep-b-end ;
: ep-b-won ( frames -- flag outcome frames 0 )
  true ep-b-default. drop epb epb-goals @ ep-goals-cut epb epb-mark @ lf-mctx-commit
  true swap rot ep-b-end ;
defer ep-b-next ( frames -- ... frames next )
: ep-b-lost ( frames -- frames next | flag outcome frames 0 )
  false ep-b-default. drop ep-b-undo dup ok? 0= if false swap rot ep-b-end exit then
  drop ['] ep-b-next ;
: ep-goals# ( -- n ) ep-goals slab-count epb epb-goals @ - ;
: ep-b-after ( flag outcome frames -- ... frames next )
  over ok? 0= if ep-b-failed exit then rot if nip ep-b-won else nip ep-b-lost then ;
: ep-b-tried ( flag outcome frames -- ... frames next )
  over ok? 0= if ep-b-failed exit then
  rot 0= if nip ep-b-lost exit then nip
  ep-goals# 0= if ep-b-won exit then
  epb epb-goals @ 0 rot ['] ep-b-after ep-c-call ;
: ep-b-try ( v frames -- ... frames next )
  >r lf-mctx-mark ok-then? 0= if nip false swap r> ep-b-end exit then
  epb epb-mark ! ep-goals slab-count epb epb-goals ! ep-b-attempt r> ep-b-tried ;
:noname ( frames -- ... frames next )
  >r ep-b-find 0= if false outcome-ok r> ep-b-end exit then
  dup lf-default-gap? if drop false lfa-e-elab-step lf-elab-fail r> ep-b-end exit then
  r> ep-b-try ;
is ep-b-next
: ep-b-class ( frames -- ... frames next )
  >r ep-b-type lf-elab-class? ok-then? 0= if false swap r> ep-b-end exit then
  0= if false outcome-ok r> ep-b-end exit then
  ep-b-defaults dup ok? 0= if false swap r> ep-b-end exit then drop r> ['] ep-b-next ;
: ep-b-visit ( m only frames -- ... frames next )
  >r ep-b-new dup ok? 0= if false swap r> 0 exit then drop r> ep-b-class ;
: ep-b-call ( m only frames cont -- ... frames next ) ['] ep-b-visit lf-elab-open ;

\ ---- C: synthesizePending on the list from first to the top of
\ ep-goals: by instances while that fills one (each attempt under a mark,
\ a Lean error read as false), else the first a default instance fills.
: epc ( -- addr ) ep-cs slab-last ;
: ep-c-first ( -- first ) epc epc-first @ ;
: ep-c# ( -- n ) ep-goals slab-count ep-c-first - ;
: ep-c-at ( k -- i ) ep-goals slab-count 1- swap - ;   \ Lean's list: the newest first
: ep-c-goal ( k -- mvar ) ep-c-at ep-goals slab-at @ ;
: ep-c-remove ( k -- ) ep-c-at ep-goals slab-remove ;
: ep-when-ok ( mark flag -- flag outcome )
  if lf-mctx-commit true swap else lf-mctx-rollback false swap then ;
: ep-when-failed ( mark flag outcome -- flag outcome )
  nip swap lf-mctx-rollback ok-then? 0= if nip false swap exit then
  dup lf-elab-catch if drop false outcome-ok else false swap then ;
: ep-commit-when ( mark flag outcome -- flag outcome )
  dup ok? if drop ep-when-ok else ep-when-failed then ;
: ep-c-inst ( k -- filled? outcome )
  ep-c-goal lf-mctx-mark ok-then? 0= if nip false swap exit then
  swap lf-elab-synth-core ep-commit-when ;
: ep-c-one ( p k -- p' k' outcome )
  dup ep-c-inst dup ok? 0= if nip exit then drop
  if dup ep-c-remove nip true swap else 1+ then outcome-ok ;
: ep-c-pass ( -- progress outcome )
  false 0 begin dup ep-c# < while ep-c-one dup ok? 0= if nip exit then drop repeat
  drop outcome-ok ;
: ep-c-instances ( -- outcome )
  begin ep-c-pass dup ok? 0= if nip exit then drop 0= until outcome-ok ;
: ep-c-new ( first -- outcome )
  1 ep-cs slab-claim ok-then? 0= if nip exit then
  ep-cs slab-at tuck epc-first ! 0 swap epc-i ! outcome-ok ;
: ep-c-end ( flag outcome frames -- flag outcome frames 0 ) ep-cs slab-drop 0 ;
defer ep-c-loop ( frames -- ... frames next )
defer ep-c-some ( frames -- ... frames next )
: ep-c-after ( flag outcome frames -- ... frames next )
  over ok? 0= if ep-c-end exit then
  rot if nip epc epc-i @ ep-c-remove ['] ep-c-loop exit then
  nip 1 epc epc-i +! ['] ep-c-some ;
:noname ( frames -- ... frames next )
  epc epc-i @ ep-c# < 0= if false outcome-ok rot ep-c-end exit then
  epc epc-i @ ep-c-goal -1 rot ['] ep-c-after ep-b-call ;
is ep-c-some
:noname ( frames -- ... frames next )
  >r ep-c-instances dup ok? 0= if false swap r> ep-c-end exit then drop
  ep-c# 0= if true outcome-ok r> ep-c-end exit then 0 epc epc-i ! r> ['] ep-c-some ;
is ep-c-loop
: ep-c-visit ( first x frames -- ... frames next )
  >r drop ep-c-new dup ok? 0= if false swap r> 0 exit then drop r> ['] ep-c-loop ;
:noname ( first x frames cont -- ... frames next ) ['] ep-c-visit lf-elab-open ;
is ep-c-call

\ ---- synthesizeUsingDefault over the window: for each priority, the
\ first entry, oldest first, that a default instance of it fills (B as a
\ pass of its own on ep-frames), taken out of the window.
: ep-frames-ready ( -- frames ) ep-frames lf-elab-frames-ready ;
: ep-pass ( m only -- flag outcome ) ep-frames-ready ['] ep-b-call frame-through drop ;
: ep-default-entry ( prio k -- flag outcome ) ep-window-at 2@ lf-elab-at! swap ep-pass ;
: lf-elab-settled? ( flag outcome -- flag outcome stop? ) 2dup ok? 0= or ;
: ep-some-prio ( prio -- flag outcome )
  0 begin dup lf-elab-pending# < while
    2dup ep-default-entry dup ok? 0= if 2swap 2drop exit then drop
    if nip ep-remove true outcome-ok exit then 1+
  repeat 2drop false outcome-ok ;
: ep-try-prios ( -- flag outcome )
  ep-prios slab-count 0 ?do
    i ep-prio@ ep-some-prio lf-elab-settled? if unloop exit then 2drop
  loop false outcome-ok ;
: ep-using-default ( -- flag outcome )
  lf-elab-pending# 0= if false outcome-ok exit then
  ep-prios-ready dup ok? 0= if false swap exit then drop ep-try-prios ;

\ ---- synthesizeSyntheticMVars.
: ep-or ( progress outcome xt -- progress' outcome' )
  >r lf-elab-settled? if r> drop exit then 2drop r> execute ;
: ep-later ( -- progress outcome )
  ep-step ['] ep-using-default ep-or ['] ep-step ep-or ['] ep-step ep-or ;
: ep-rounds ( mode -- progress outcome )
  ep-step lf-elab-settled? if rot drop exit then 2drop
  lf-postpone-yes = if false outcome-ok else ep-later then ;
: ep-oldest-at ( -- ) 0 ep-window-at @ lf-elab-at! ;
: ep-stuck ( mode -- outcome )
  lf-postpone-no = if ep-oldest-at lfa-e-elab-stuck lf-elab-fail else outcome-ok then ;
: ep-loop ( mode -- outcome )
  begin lf-elab-pending# while
    dup ep-rounds dup ok? 0= if nip nip exit then drop 0= if ep-stuck exit then
  repeat drop outcome-ok ;
: lf-elab-synthesize ( mode -- outcome ) lf-elab-at >r ep-loop r> lf-elab-at! ;
\ synthesizeUsingDefaultLoop, synthesizeSyntheticMVarsUsingDefault.
: ep-default-loop ( -- outcome )
  begin ep-using-default dup ok? 0= if nip exit then drop
  while lf-postpone-yes lf-elab-synthesize dup ok? 0= if exit then drop repeat
  outcome-ok ;
: lf-elab-synthesize-default ( -- outcome )
  lf-postpone-yes lf-elab-synthesize ['] ep-default-loop ok-and ;
\ withSynthesize (SyntheticMVars.lean:662): lf-elab-synth{ sets the list
\ aside; }lf-elab-synth ( saved mode -- outcome ) synthesizes in mode
\ (lf-postpone-yes: with the default-instance loop after), then puts the
\ list back after what is left, whatever happened.
: lf-elab-synth{ ( -- saved ) lf-elab-window{ ;
: ep-synth-end ( mode -- outcome )
  dup lf-elab-synthesize swap lf-postpone-yes = if ['] ep-default-loop ok-and then ;
: }lf-elab-synth ( saved mode -- outcome ) ep-synth-end swap }lf-elab-window ;

\ ---- The reset.
: lf-elab-pending-reset ( -- )
  ep-pending slab-clear ep-scratch slab-clear ep-defs slab-clear
  ep-goals slab-clear ep-bs slab-clear ep-cs slab-clear ep-trace slab-clear
  0 ep ep-base ! -1 lf-elab-at! lf-elab-error-reset ;
' lf-elab-pending-reset context-setup

base !   \ the BASE this file was loaded with

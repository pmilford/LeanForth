\ Reverting hypotheses of a goal (plan row TB2, tactic batch 1): Lean
\ 4.35.0's src/lean/Lean/Meta/Tactic/Revert.lean, with the part of
\ MetavarContext.lean's revert (collectForwardDeps, elimMVarDeps on the
\ goal) that a goal of the tactics' needs. Each word throws on failure
\ (meta-must.fs), as Lean's do.
\ Public words:
\   lf-goal-revert ( goal fvars -- goal' n )  MVarId.revert (Revert.lean:
\       18-48, preserveOrder false): fvars a run (lib/runs.fs) of free
\       variables of goal's context; none gives goal itself and 0 (Lean
\       asks nothing then, not even checkNotAssigned). Else in goal's
\       context (checkNotAssigned first) the reverted are the locals asked
\       and every later local whose type or value depends on one reverted
\       (collectForwardDeps, oldest first; goals.fs's
\       lf-local-depends-on?, Lean's localDeclDependsOn), n of them, x1 ..
\       xn in the context's order; goal' a new synthetic opaque goal of
\       type (x1 : T1) -> .. -> (xn : Tn) -> T (telescope.fs's
\       lf-mk-forall-fvars of goal's type as stored: each binder named and
\       of the kind of its local), with goal's tag, in goal's context
\       without them (Lean's reduceLocalContext); goal assigned
\       goal' x1 .. xn (elimMVar's mkAppN of the new metavariable)
\   lf-goal-revert-kept ( goal fvars -- goal' kept )  MVarId.revert with
\       preserveOrder true as Meta induction (Induction.lean:229) and
\       substCore (Subst.lean:34) ask it: goal' of the same kind, the
\       binders in collectForwardDeps' preserveOrder order
\       (MetavarContext.lean): the locals asked, in the order asked, then
\       every later local depending on one reverted, oldest first (a
\       local asked that depends on one asked after it is thrown invalid,
\       Lean's revertFailure: subst asks a variable, then an equation
\       over it; generalize's at[ hv v ] asks so, and the runner answers
\       93, not supported yet, where Lean refuses the text); and kept, a run of the
\       reverted locals in that order (lctx-views.fs's records, which
\       never change: each one's name, kind and inaccessible flag, for goal.fs's
\       lf-goal-intro-kept to put back, as Lean's introNP keeps a
\       binder's name, hygienic or not); none asked gives goal and 0
\   lf-goal-revert-after ( goal fvar -- goal' n )  MVarId.revertAfter
\       (Revert.lean:51-56): every local after fvar in goal's context
\       reverted so, oldest first (preserveOrder true asks the same order)
\ A local asked that is not in goal's context is thrown invalid (Lean's
\ unknown free variable: a fault here, no tactic asks one). Not supported
\ yet (thrown unsupported: the runner's 93): an implementation detail
\ among the reverted (Lean refuses an auxiliary declaration asked by name
\ and clears one that depends); a let among them and a metavariable of
\ goal's type that sees one (telescope.fs's mkBinding: Lean's
\ elimMVarDeps would revert it).
\ Lean call list: withContext -> lf-with-goal (meta-must.fs);
\ checkNotAssigned -> lf-goal-not-assigned (goal.fs); collectForwardDeps ->
\ mrv-collect over lf-local-depends-on? (goals.fs); mkAuxMVarType ->
\ lf-mk-forall-fvars (telescope.fs); reduceLocalContext -> lf-view-erase
\ (lctx-views.fs); mkFreshExprMVarAt, setKind, setTag -> lf-goal-new
\ (goals.fs); assign -> lf-mvar-assign; mkAppN -> lf-mk-app (app-builder.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: mrv-frames (a frame per call open, meta-must.fs's
\ lf-with-record) and mrv-cells (the reverted free variables, n cells a
\ call, lf-with-cells), in the checker context (ADR 0009); no other.
\ Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/runs.fs
require ../../lib/slab.fs
require ../../lib/find.fs
require ../../lib/context.fs
require ../mvars.fs
require ../lctx-views.fs
require ../goals.fs
require ../meta-must.fs
require ../app-builder.fs
require ../telescope.fs
require ./goal.fs

begin-structure /mrv
  field: mrv-goal        \ the goal
  field: mrv-in          \ the free variables asked for, a run
  field: mrv-out         \ the reverted, a run, oldest first
  field: mrv-keep        \ true: preserveOrder (the asked first, as asked)
end-structure
/mrv context-slab: mrv-frames
: mrv ( -- frame ) mrv-frames slab-last ;
1 cells context-slab: mrv-cells
: mrv-out# ( -- n ) mrv mrv-out @ run-count ;
: mrv-out@ ( i -- fvar ) mrv mrv-out @ swap run@ ;

\ ---- collectForwardDeps: a local asked, or one whose type or value
\ depends on one reverted before it, is reverted.
: mrv-in# ( -- n ) mrv mrv-in @ run-count ;
: mrv-in@ ( i -- fvar ) mrv mrv-in @ swap run@ ;
: mrv-found ( k true | false -- flag ) dup if nip then ;
: mrv-is? ( fvar k -- fvar flag ) mrv-in@ over = ;
: mrv-asked? ( fvar -- flag ) mrv-in# ['] mrv-is? find-index mrv-found ;
: mrv-dep? ( lfvar k -- lfvar flag ) mrv-out@ over swap lf-local-depends-on? lf-must ;
: mrv-depends? ( fvar -- flag ) mrv-out# ['] mrv-dep? find-index mrv-found ;
: mrv-reverted? ( fvar -- flag ) dup mrv-asked? if drop true else mrv-depends? then ;
: mrv-plain ( k -- k ) dup lf-local-detail-at? if lf-unported then ;
: mrv-push ( fvar -- ) mrv mrv-out lf-run+! ;
: mrv-take ( k flag -- ) if mrv-plain lf-mctx-fvar mrv-push else drop then ;
: mrv-local ( k -- ) dup lf-mctx-fvar mrv-reverted? mrv-take ;
\ preserveOrder: the asked are out first, in their order; a local asked
\ is only checked, a dependent follows them.
: mrv-local-kept ( k -- )
  dup lf-mctx-fvar dup mrv-asked? if drop mrv-plain drop exit then mrv-depends? mrv-take ;
: mrv-in-view ( i -- )
  mrv-in@ lf-mctx-view swap lf-view-has? 0= if outcome-invalid lf-must then ;
\ A local asked must not be one that a local asked before it depends on
\ (collectForwardDeps' revertFailure check), thrown invalid (generalize's
\ at[ hv v ] reaches it: 93 at the step, where Lean refuses with "failed
\ to create binder"; Lean's own error text: slice E4,
\ docs/design/TACTIC_PATTERNS.md).
: mrv-needed? ( fvar k -- fvar flag ) mrv-out@ over lf-local-depends-on? lf-must ;
: mrv-ordered ( fvar -- fvar )
  mrv-out# ['] mrv-needed? any? if outcome-invalid lf-must then ;
: mrv-seed ( -- xt )
  mrv-in# 0 ?do i mrv-in@ mrv-ordered mrv-push loop ['] mrv-local-kept ;
: mrv-each ( -- xt ) mrv mrv-keep @ if mrv-seed else ['] mrv-local then ;
: mrv-collect ( -- )
  mrv-in# 0 ?do i mrv-in-view loop mrv-each
  lf-mctx-view lf-view-count 0 ?do i over execute loop drop ;

\ ---- The new goal: (x1 : T1) -> .. -> T in the context without them, its
\ tag the goal's; the goal assigned it applied to x1 .. xn.
: mrv-fill ( addr -- addr ) mrv-out# 0 ?do i mrv-out@ over i cells + ! loop ;
: mrv-bound ( type addr -- type' ) mrv-fill mrv-out# lf-mk-forall-fvars ;
: mrv-type ( -- type )
  mrv mrv-goal @ lf-goal-type mrv-out# mrv-cells ['] mrv-bound lf-with-cells ;
: mrv-erase ( view i -- view' ) mrv-out@ lf-view-erase lf-must ;
: mrv-view ( -- view ) mrv mrv-goal @ lf-goal-view mrv-out# 0 ?do i mrv-erase loop ;
: mrv-new ( -- goal' ) mrv-type mrv mrv-goal @ lf-goal-tag mrv-view lf-goal-new lf-must ;
: mrv-applied ( goal' -- e ) mrv-out# 0 ?do i mrv-out@ lf-mk-app loop ;
: mrv-assign ( e -- ) mrv mrv-goal @ swap lf-mvar-assign lf-must ;
: mrv-reverted ( -- goal' ) mrv-collect mrv-new dup mrv-applied mrv-assign ;
: mrv-run ( -- goal' n ) mrv-reverted mrv-out# ;
\ The reverted locals, as goal's context holds them (revert-kept's kept).
: mrv-local+ ( run i -- run' )
  mrv mrv-goal @ lf-goal-view swap mrv-out@ lf-view-local-of lf-run+ ;
: mrv-run-kept ( -- goal' kept ) mrv-reverted 0 mrv-out# 0 ?do i mrv-local+ loop ;
: mrv-with ( goal fvars xt -- goal' x ) >r mrv mrv-in ! dup mrv mrv-goal ! r>
  lf-with-goal ;
: mrv-framed ( goal fvars xt -- goal' x )
  rot lf-goal-not-assigned -rot mrv-frames ['] mrv-with lf-with-record ;
\ None asked: goal itself and 0 (Lean asks nothing then).
: mrv-by ( goal fvars xt -- goal' x ) over run-count if mrv-framed exit then 2drop 0 ;
: lf-goal-revert ( goal fvars -- goal' n ) ['] mrv-run mrv-by ;
: mrv-keep-run ( -- goal' kept ) true mrv mrv-keep ! mrv-run-kept ;
: lf-goal-revert-kept ( goal fvars -- goal' kept ) ['] mrv-keep-run mrv-by ;

\ ---- revertAfter: the locals after fvar, a run.
: mrv-fvar+ ( run view i -- run' view )
  over swap lf-view-fvar rot swap lf-run+ swap ;
: mrv-tail ( view k -- run ) 0 -rot over lf-view-count swap ?do i mrv-fvar+ loop drop ;
: mrv-after ( goal fvar -- goal run )
  over lf-goal-view tuck swap lf-view-find lf-found 1+ mrv-tail ;
: lf-goal-revert-after ( goal fvar -- goal' n ) mrv-after lf-goal-revert ;
base !   \ the BASE this file was loaded with

\ Goals and the proof state of the tactic framework (plan FE1g-1;
\ docs/design/FE1G_TACTICS.md §4.1), after Lean 4.35.0's
\ Elab/Tactic/Basic.lean and Meta/Tactic/Clear.lean, Rename.lean. A goal
\ is a metavariable (mvars.fs), synthetic opaque as Lean's tactic goals
\ are, with its own local context (a view, lctx-views.fs) and its tag
\ (Lean's MetavarDecl.userName: zero, succ for induction's cases; 0 for
\ none). A goal list is a run of goals (runs.fs), so a list never changes
\ and a saved one stays as it was.
\ - lf-goal-new ( type tag view -- goal outcome ): Lean's
\   mkFreshExprMVarAt view {} type .syntheticOpaque tag. For a goal in an
\   extended context (withLocalDecl, intro), push the local on a view
\   first (lf-view-push).
\ - lf-goal-assigned? ( goal -- flag ): Lean's MVarId.isAssigned (a plain
\   assignment; a delayed one is not).
\ - lf-goal-clear ( goal fvar -- goal' outcome ): Lean's MVarId.clear,
\   refused (invalid) when the goal is assigned, its context does not hold
\   fvar, another local's type or (shown) value depends on it, or its type
\   does (lf-depends-on?); else a new goal with the same type and tag in
\   the context without fvar, the old goal assigned the new one.
\ - lf-goal-rename ( goal fvar name -- goal' outcome ): MVarId.rename,
\   the same with fvar's local renamed (refused when assigned or absent).
\ The proof state pst (Lean's Tactic.State, plus the root goal): the goal
\ list and the declaration's goal ?g. FE1g-3's runner adds its fields.
\ - lf-pst-open ( goal -- outcome ): goals [goal], root goal;
\   lf-pst-reset ( -- ): no goals; lf-pst-root ( -- goal ).
\ - lf-goals ( -- list ), lf-goals! ( list -- outcome ): getGoals,
\   setGoals; a list from before lf-mctx-reset reads as empty.
\ - lf-goals-unsolved ( -- list outcome ): getUnsolvedGoals, the goals
\   not assigned (pruneSolvedGoals: the list becomes that).
\ - lf-main-goal ( -- goal outcome ): getMainGoal, the first goal not
\   assigned, the ones before it dropped from the list; none is invalid
\   (Lean's "no goals to be proved").
\ - lf-replace-main ( list -- outcome ): replaceMainGoal, the list in
\   place of the first goal; lf-goals-append ( list -- outcome ):
\   appendGoals, the list after the goals.
\ Outcomes: ok; invalid as above and for a goal that is no live
\ metavariable, a list that names no run; full when a store or the heap
\ has no room; unsupported where an instantiation is (lf-depends-on?).
\ A failure changes no goal list. Untrusted: a wrong goal can only make
\ the kernel refuse the finished term.
\ State: the record pst in the checker context (ADR 0009).

require ../lib/lib.fs
require ./runs.fs
require ./lctx-views.fs
require ./mvars.fs

begin-structure /pst
  field: pst-goals    \ the goal list, a run
  field: pst-epoch    \ lf-runs-epoch when it was set
  field: pst-root     \ the declaration's goal, or -1
end-structure
/pst context-record: pst

\ ---- Goals. A failure has no goal: -1 in its place.
: gl-result ( goal outcome -- goal outcome ) dup ok? 0= if nip no-result then ;
: gl-tagged ( tag goal -- goal outcome ) tuck swap lf-mvar-tag! gl-result ;
: lf-goal-new ( type tag view -- goal outcome )
  over lf-user-name? 0= if drop 2drop -1 outcome-invalid exit then
  >r swap mv-opaque r> lf-mvar-new-at ok-then? if gl-tagged else nip no-result then ;
: lf-goal-assigned? ( goal -- flag ) lf-mvar-value dup if nip then ;
\ A goal tactics may change: live and not assigned (checkNotAssigned).
: gl-open? ( goal -- flag )
  dup lf-mvar-live? if lf-goal-assigned? 0= else drop false then ;
: gl-view ( goal -- view ) lf-mvar-view drop ;
\ A new goal with the old one's type and tag in view, assigned to it.
: gl-new-like ( goal view -- goal' outcome )
  >r dup lf-mvar-type drop swap lf-mvar-tag drop r> lf-goal-new ;
: gl-replace ( goal view -- goal' outcome )
  over swap gl-new-like ok-then? 0= if nip no-result exit then
  tuck lf-mvar-assign gl-result ;

\ Clearing (Lean's MVarId.clear): no other local's type, nor a let's
\ value that is not hidden, may depend on fvar (localDeclDependsOn), nor
\ the goal's type.
: gl-decided? ( flag outcome -- flag outcome true | false )
  over over ok? 0= or if true else 2drop false then ;
: gl-type-dep ( lfvar fvar -- flag outcome ) swap lf-fvar-type swap lf-depends-on? ;
: gl-value-dep ( lfvar fvar -- flag outcome )
  over lf-fvar-let? 0= if 2drop false outcome-ok exit then
  swap lf-fvar-value swap lf-depends-on? ;
: gl-local-dep ( lfvar fvar -- flag outcome )
  2dup gl-type-dep gl-decided? if 2swap 2drop else gl-value-dep then ;
: gl-fvar-at ( view i -- fvar ) lf-view-local lf-local-fvar ;
: gl-dep-at ( view fvar i -- view fvar flag outcome )
  >r over r> gl-fvar-at over 2dup = if 2drop false outcome-ok else gl-local-dep then ;
: gl-others-dep ( view fvar -- flag outcome )
  over lf-view-count 0 ?do i gl-dep-at gl-decided? if 2swap 2drop unloop exit then loop
  2drop false outcome-ok ;
: gl-none ( flag outcome -- outcome ) dup ok? if drop 0= flag>outcome else nip then ;
: gl-target-dep ( goal fvar -- flag outcome ) swap lf-mvar-type drop swap lf-depends-on? ;
: gl-free-of ( goal fvar -- outcome )
  over gl-view over gl-others-dep gl-none dup ok? if drop gl-target-dep gl-none
  else nip nip then ;
: gl-has? ( goal fvar -- flag ) swap gl-view swap lf-view-find dup if nip then ;
: gl-clearable ( goal fvar -- outcome )
  over gl-open? 0= if 2drop outcome-invalid exit then
  2dup gl-has? if gl-free-of else 2drop outcome-invalid then ;
: gl-cleared ( goal fvar -- goal' outcome )
  over gl-view swap lf-view-erase ok-then? if gl-replace else nip no-result then ;
: lf-goal-clear ( goal fvar -- goal' outcome )
  2dup gl-clearable dup ok? if drop gl-cleared else nip nip no-result then ;

\ Renaming (MVarId.rename).
: gl-renamed ( goal fvar name -- goal' outcome )
  >r over gl-view swap r> lf-view-rename ok-then? if gl-replace else nip no-result then ;
: lf-goal-rename ( goal fvar name -- goal' outcome )
  rot dup gl-open? if -rot gl-renamed else drop 2drop -1 outcome-invalid then ;

\ ---- The proof state.
: lf-pst-root ( -- goal ) pst pst-root @ ;
: gl-set ( list -- ) pst tuck pst-goals ! lf-runs-epoch swap pst-epoch ! ;
: lf-pst-reset ( -- ) 0 gl-set -1 pst pst-root ! ;
: lf-goals ( -- list )
  pst dup pst-epoch @ lf-runs-epoch = if pst-goals @ else drop 0 then ;
: lf-goals! ( list -- outcome )
  dup lf-run-valid? if gl-set outcome-ok else drop-invalid then ;
: lf-pst-open ( goal -- outcome )
  dup lf-mvar-live? 0= if drop-invalid exit then
  0 over lf-run-push ok-then? if gl-set pst pst-root ! outcome-ok else nip then ;

\ The goals not assigned, in order (a new run).
: gl-keep ( list goal -- list' outcome )
  dup lf-goal-assigned? if drop outcome-ok else lf-run-push then ;
: gl-kept ( new list i -- new' list outcome )
  over swap lf-run@ rot swap gl-keep >r swap r> ;
: gl-unsolved ( list -- list' outcome )
  0 swap dup lf-run-count 0 ?do
    i gl-kept ok-then? 0= if nip no-result unloop exit then loop
  drop outcome-ok ;
: lf-goals-unsolved ( -- list outcome )
  lf-goals gl-unsolved ok-then? if dup gl-set outcome-ok else no-result then ;
\ The place of the first goal not assigned, or the count.
: gl-open-at? ( list i -- flag ) lf-run@ lf-goal-assigned? 0= ;
: gl-first-open ( list -- k )
  dup lf-run-count 0 ?do dup i gl-open-at? if drop i unloop exit then loop lf-run-count ;
: gl-main ( list -- goal outcome )
  dup lf-run-count 0= if drop -1 outcome-invalid exit then
  dup gl-set 0 lf-run@ outcome-ok ;
: lf-main-goal ( -- goal outcome )
  lf-goals dup gl-first-open lf-run-after ok-then? if gl-main else no-result then ;
: gl-tail ( -- list outcome )
  lf-goals dup lf-run-count 0= if drop -1 outcome-invalid else 1 lf-run-after then ;
: gl-set-ok ( list outcome -- outcome ) ok-then? if gl-set outcome-ok then ;
: lf-replace-main ( list -- outcome )
  gl-tail ok-then? if lf-run-cat gl-set-ok else nip then ;
: lf-goals-append ( list -- outcome ) lf-goals swap lf-run-cat gl-set-ok ;

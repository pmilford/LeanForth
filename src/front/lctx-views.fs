\ Local declarations and local contexts of the front end (plan FE1g-1;
\ docs/design/FE1G_TACTICS.md §4.1), after Lean's LocalDecl and
\ LocalContext (Lean/LocalContext.lean). Every metavariable has its own
\ local context (Lean's MetavarDecl.lctx; mvars.fs), so that tactics may
\ clear or rename a hypothesis in one goal and leave the others as they
\ are, and mkLambdaFVars, the goal display and the assignment check
\ (checkAssignment) read the context of the goal at hand.
\ A local (Lean's LocalDecl) is a record of lv-locals that never changes:
\ a live free variable (core/local-context.fs keeps its type, its value
\ for a let and whether that value is hidden, Lean's nondep), its user
\ name (a name ID, 0 the anonymous name), its flags and, for a local
\ instance, its class name (Lean's LocalInstance; 0 for none). Flags: the
\ binder kind (present/binder-table.fs, lf-binder-*), Lean's
\ LocalDeclKind (lf-local-impl-detail, lf-local-aux-decl, or neither for
\ the default) and lf-local-inaccessible for a name made without the
\ user's (Lean gives it macro scopes and shows it as name✝; this keeps
\ the name with the scopes erased and the flag, FE1G_TACTICS.md §2.3).
\ - lf-local-new ( fvar name flags -- local outcome ); lf-local-fvar,
\   lf-local-name, lf-local-flags, lf-local-binder, lf-local-class
\   ( local -- x ), lf-local-inaccessible?, lf-local-detail? (Lean's
\   isImplementationDetail: not of the default kind) ( local -- flag );
\   lf-local-renamed ( local name -- local' outcome ) (setUserName: the
\   new name is the user's, accessible); lf-local-instance ( local class
\   -- local' outcome ); lf-local-valid? ( local -- flag ).
\ A view (Lean's LocalContext) is a run of locals (runs.fs), oldest first,
\ each free variable at most once; lf-view-empty is the empty context:
\ - lf-view-push ( view local -- view' outcome ): mkLocalDecl, the local
\   last (invalid when the view holds its free variable already);
\ - lf-view-erase ( view fvar -- view' outcome ): erase (no change when
\   the view does not hold it);
\ - lf-view-rename ( view fvar name -- view' outcome ): setUserName in
\   place (invalid when the view does not hold it);
\ - lf-view-find ( view fvar -- i true | false ): its place (contains);
\   lf-view-named ( view name -- i true | false ): the newest accessible
\   local of that name (findFromUserName?);
\ - lf-view-sub-prefix? ( view1 view2 -- flag ): isSubPrefixOf, view1's
\   free variables found in view2 in the same order (others between);
\   lf-view-sub-prefix-except? ( view1 view2 addr n -- flag ): the same
\   with exceptFVars, the n free variables in the cells at addr, which
\   view1's locals may hold without view2 holding them (checkAssignment's
\   pattern variables); a negative n, or a view that names none, is false;
\ - lf-view-count ( view -- n ), lf-view-local ( view i -- local )
\   (unchecked: a valid view, 0 <= i < n), lf-view-valid? ( view -- flag ).
\ Local instances (Lean's MetavarDecl.localInstances) are the view's
\ locals with a class, in order. lf-views-reset ( -- ) empties all,
\ with lf-mctx-reset; a local or view means nothing afterwards.
\ Outcomes: ok; invalid for a free variable that is not live, a name ID
\ that names no name, flags outside the ones above, a handle that names
\ no local or view; full when the heap refuses. A failure makes nothing
\ reachable. Untrusted: whatever a context says, the kernel's check of
\ the finished term decides.
\ State: the slab lv-locals and the record lv (the exceptions of the
\ comparison under way, as mvars.fs keeps an occurs check's target), and
\ the runs of runs.fs, in the checker context (ADR 0009).

require ../lib/lib.fs
require ../core/names.fs
require ../core/name-equal.fs
require ../core/local-context.fs
require ../present/binder-table.fs
require ./runs.fs

begin-structure /loc
  field: loc-fvar      \ the free variable
  field: loc-name      \ its user name, a name ID (0: anonymous)
  field: loc-flags     \ binder kind, kind of declaration, inaccessible
  field: loc-class     \ a local instance's class name, or 0
end-structure
/loc context-slab: lv-locals
begin-structure /lv
  field: lv-except     \ the free variables a comparison skips: their cells
  field: lv-except#    \ and how many
end-structure
/lv context-record: lv
: lf-views-reset ( -- ) lv-locals slab-clear lf-runs-reset ;

3 constant lf-local-binder-mask      \ the binder kind, lf-binder-*
4 constant lf-local-impl-detail      \ Lean's LocalDeclKind.implDetail
8 constant lf-local-aux-decl         \ LocalDeclKind.auxDecl
12 constant lf-local-kind-mask
16 constant lf-local-inaccessible    \ a name the user did not give
31 constant lf-local-flags-mask

\ Reading a local. Unchecked but for lf-local-valid?.
: lv-loc ( local -- addr ) lv-locals slab-at ;
: lf-local-valid? ( local -- flag ) lv-locals slab-valid? ;
: lf-local-fvar ( local -- fvar ) lv-loc loc-fvar @ ;
: lf-local-name ( local -- name ) lv-loc loc-name @ ;
: lf-local-flags ( local -- flags ) lv-loc loc-flags @ ;
: lf-local-class ( local -- class ) lv-loc loc-class @ ;
: lf-local-binder ( local -- kind ) lf-local-flags lf-local-binder-mask and ;
: lf-local-inaccessible? ( local -- flag ) lf-local-flags lf-local-inaccessible and 0<> ;
: lf-local-detail? ( local -- flag ) lf-local-flags lf-local-kind-mask and 0<> ;

\ Making one: a live free variable, a name ID or 0, flags of one kind at
\ most; a record filled field by field (four cells: a record's filler).
: lf-user-name? ( name -- flag ) dup 0= swap lf-name-valid? or ;
: lv-kind-one? ( flags -- flag ) lf-local-kind-mask and lf-local-kind-mask <> ;
: lv-flags? ( flags -- flag )
  dup lf-local-flags-mask invert and 0= swap lv-kind-one? and ;
: lv-fill ( fvar name flags addr -- )
  tuck loc-flags ! tuck loc-name ! tuck loc-fvar ! 0 swap loc-class ! ;
: lv-made ( fvar name flags -- local outcome )
  1 lv-locals slab-claim ok-then? 0= if nip nip nip no-result exit then
  dup >r lv-loc lv-fill r> outcome-ok ;
: lv-bad ( fvar name flags -- -1 outcome ) 2drop drop -1 outcome-invalid ;
: lf-local-new ( fvar name flags -- local outcome )
  2dup lv-flags? swap lf-user-name? and 0= if lv-bad exit then
  rot dup lf-fvar-live? 0= if -rot lv-bad exit then -rot lv-made ;

\ Changed copies: a new record, the old one as it was.
: lv-copy ( local -- local' outcome )
  1 lv-locals slab-claim ok-then? if swap lv-loc over lv-loc /loc move outcome-ok
  else nip no-result then ;
: lv-accessible ( addr -- )
  dup loc-flags @ lf-local-inaccessible invert and swap loc-flags ! ;
: lv-name! ( name local -- ) lv-loc tuck loc-name ! lv-accessible ;
: lv-renamable? ( local name -- local name flag )
  2dup lf-user-name? swap lf-local-valid? and ;
: lf-local-renamed ( local name -- local' outcome )
  lv-renamable? 0= if 2drop -1 outcome-invalid exit then
  swap lv-copy ok-then? if tuck lv-name! outcome-ok else nip no-result then ;
: lv-class? ( local class -- local class flag )
  2dup dup 0<> swap lf-name-valid? and swap lf-local-valid? and ;
: lf-local-instance ( local class -- local' outcome )
  lv-class? 0= if 2drop -1 outcome-invalid exit then
  swap lv-copy ok-then? if tuck lv-loc loc-class ! outcome-ok else nip no-result then ;

\ ---- Views: runs of locals, oldest first.
0 constant lf-view-empty
: lf-view-valid? ( view -- flag ) lf-run-valid? ;
: lf-view-count ( view -- n ) lf-run-count ;
: lf-view-local ( view i -- local ) lf-run@ ;
: lv-fvar-at ( view i -- fvar ) lf-view-local lf-local-fvar ;
: lv-holds? ( view fvar i -- view fvar flag ) >r over r> lv-fvar-at over = ;
: lf-view-find ( view fvar -- i true | false )
  over lf-view-valid? 0= if 2drop false exit then
  over lf-view-count 0 ?do i lv-holds? if 2drop i true unloop exit then loop 2drop false ;
: lf-view-push ( view local -- view' outcome )
  dup lf-local-valid? 0= if 2drop -1 outcome-invalid exit then
  2dup lf-local-fvar lf-view-find if drop 2drop -1 outcome-invalid exit then lf-run-push ;

\ The newest accessible local of a name (an inaccessible name has macro
\ scopes in Lean, so it never equals a name the user writes).
: lv-name-is? ( name local -- flag )
  dup lf-local-inaccessible? if 2drop false else lf-local-name lf-name-same? then ;
: lv-named? ( view name i -- view name i flag )
  >r over r@ lf-view-local over swap lv-name-is? r> swap ;
: lf-view-named ( view name -- i true | false )
  over lf-view-valid? over lf-user-name? and 0= if 2drop false exit then
  over lf-view-count begin dup while 1- lv-named? if nip nip true exit then repeat
  drop 2drop false ;

\ Erasing and renaming: the locals before place i, the changed one if
\ any, and the locals after it.
: lv-rest ( run1 view i -- view' outcome )
  1+ lf-run-after ok-then? if lf-run-cat else nip no-result then ;
: lv-without ( view i -- view' outcome )
  2dup lf-run-take ok-then? if -rot lv-rest else nip nip no-result then ;
: lf-view-erase ( view fvar -- view' outcome )
  over lf-view-valid? 0= if 2drop -1 outcome-invalid exit then
  over swap lf-view-find if lv-without else outcome-ok then ;
: lv-front ( view i local -- view i run outcome )
  >r 2dup lf-run-take ok-then? if r> lf-run-push else r> drop no-result then ;
: lv-replaced ( view i local -- view' outcome )
  lv-front ok-then? if -rot lv-rest else nip nip no-result then ;
: lv-renamed-at ( view i name -- view' outcome )
  >r 2dup lf-view-local r> lf-local-renamed ok-then?
  if lv-replaced else nip nip no-result then ;
: lf-view-rename ( view fvar name -- view' outcome )
  >r over swap lf-view-find if r> lv-renamed-at else r> 2drop -1 outcome-invalid then ;

\ Lean's isSubPrefixOf: walking view2, each of view1's free variables in
\ turn is found (k of them so far), view1's exceptions passed over.
: lv-except! ( addr n -- ) lv tuck lv-except# ! lv-except ! ;
: lv-skip? ( fvar -- flag )
  lv lv-except @ lv lv-except# @ cells over + swap
  ?do dup i @ = if drop true unloop exit then cell +loop drop false ;
: lv-more? ( view1 k -- flag ) swap lf-view-count < ;
: lv-skipped ( view1 k -- view1 k' )
  begin 2dup lv-more? while 2dup lv-fvar-at lv-skip? 0= if exit then 1+ repeat ;
: lv-advance ( view1 k fvar -- view1 k' )
  >r lv-skipped 2dup lv-more? if 2dup lv-fvar-at r@ = if 1+ then then r> drop ;
: lv-scan ( view1 k view2 -- view1 k' )
  dup lf-view-count 0 ?do dup i lv-fvar-at swap >r lv-advance r> loop drop ;
: lv-sub? ( view1 view2 -- flag )
  2dup lf-view-valid? swap lf-view-valid? and 0= if 2drop false exit then
  0 swap lv-scan lv-skipped swap lf-view-count = ;
: lf-view-sub-prefix? ( view1 view2 -- flag ) 0 0 lv-except! lv-sub? ;
: lf-view-sub-prefix-except? ( view1 view2 addr n -- flag )
  dup 0< if 2drop 2drop false exit then lv-except! lv-sub? ;

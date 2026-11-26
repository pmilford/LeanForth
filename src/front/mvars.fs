\ The metavariable context of the front end (ADR 0021 D2, D13; plan task
\ FE1b), after Lean's MetavarContext (Lean/MetavarContext.lean). A term
\ metavariable ?m is a hole with a kind, a depth, the local context it
\ sees, a type and, once known, an assignment; a level metavariable has a
\ depth and an assignment. Both are leaves of the term and level stores
\ (core/mvar-leaves.fs), the leaf's number being its record here and its
\ epoch this context's, so the leaf is the metavariable's handle. Like
\ every term index, a leaf means nothing after the term store is emptied:
\ lf-mctx-reset goes with every reset of the stores (a new declaration).
\ - Kinds, as Lean's MetavarKind: natural (unification may assign it),
\   synthetic (instances and postponed terms; their own procedure assigns
\   them) and synthetic opaque (goals; only tactics assign them).
\ - Depth: Lean's mctx.depth and mctx.levelAssignDepth (lf-mctx-depth,
\   lf-mctx-level-depth), entered one level deeper by a depth scope (see
\   Scopes); lf-mvar-assignable? holds for a natural or synthetic
\   metavariable of the current depth, a level metavariable is assignable
\   when made at levelAssignDepth or deeper (Lean's isLevelMVarAssignable).
\ - Each metavariable has its own local context (Lean's MetavarDecl.lctx,
\   plan FE1g-1): a view (lctx-views.fs) of free variables with their user
\   names and binder kinds, the one current when it was made (lf-mctx-view,
\   Lean's Meta context lctx, which the caller extends as withLocalDecl
\   does) or one given (lf-mvar-new-at, mkFreshExprMVarAt). Its local
\   instances are the view's locals with a class. A caller that makes a
\   free variable (entering a binder) must push its local onto the
\   current view (lf-view-push, lf-mctx-view!) for metavariables made
\   then to see it: one made with core/local-context.fs alone is in no
\   view. lf-mvar-sees? asks whether a free variable is in a
\   metavariable's view (Lean's lctx.contains, for checkAssignment). A
\   view never changes: a tactic that clears or renames a hypothesis
\   makes a new goal (front/goals.fs).
\ - A tag (Lean's MetavarDecl.userName, a goal's case name: zero, succ),
\   anonymous (0) when made; lf-mvar-tag! sets it, lf-mvar-kind! changes
\   the kind (Lean's setTag, setKind), both noted under a mark.
\ - The instance-typed flag (Lean's mctx.instanceTypedMVars,
\   MetavarContext.lean:383, 467): false when made; lf-mvar-mark-inst
\   ( mvar -- outcome ) sets it (markInstanceTyped, which synthesis's
\   subgoals call, SynthInstance.lean:358), noted under a mark like a
\   kind; lf-mvar-inst? ( mvar -- flag ) reads it (isInstanceTyped),
\   false for a metavariable that is not live.
\ - lf-mvar-assign checks that the leaf is live (a stale leaf, of an
\   earlier context or an emptied one, is refused), that the metavariable
\   has no assignment yet, plain or delayed, and the occurs check: the
\   value, with every assignment followed, must not contain it. Like Lean's
\   assign it checks neither the value's type nor its free variables; the
\   unifier does (plan FE1c).
\ - Delayed assignments, Lean's DelayedMetavarAssignment (intro under
\   binders, plan FE1g): lf-delay-fvar appends a live free variable and
\   lf-mvar-delay gives a free ?m the last n appended and a pending
\   metavariable: ?m applied to those free variables stands for the pending
\   one's value with them abstracted.
\ - lf-instantiate-mvars replaces every assigned metavariable, term or
\   level, by its value, itself instantiated, as Lean's instantiateMVars,
\   on the heap stacks of dag-walk.fs: a node met twice is made once,
\   binders keep their names and kinds (present/binder-table.fs), a Sort
\   over a level metavariable gets the level's value, a constant whose
\   universe arguments hold one gets a new reference with the levels'
\   images (level-map.fs), and a node that changes nothing stays the same
\   node. As Lean's C++ instantiate_mvars: ?f a1 .. an with ?f assigned
\   is beta-reduced at the head (betaRev); ?d a1 .. an with a delayed
\   assignment of k free variables, n >= max(k, 1), once its pending
\   metavariable's value is assigned and holds no metavariable, is
\   fun x1 .. xk => value beta-reduced against all n arguments (an
\   unassigned one stays, and the export writer refuses the hole); see
\   "Terms" below. Three cases answer unsupported, never another term:
\   Lean's second instantiation of an assigned head's beta result (where
\   a ready delayed metavariable lands at a head), an argument with loose
\   bound variables, and a let that betaRev would zeta-reduce.
\ Outcomes: ok; invalid for a stale or unknown leaf, an assigned one, an
\ occurs-check failure or a cycle; full when a store or the heap has no
\ room; unsupported as above. Untrusted: whatever the context says, only
\ the kernel's check of the finished term decides anything.
\ - Scopes, one undo trail (S1 §3; Lean's persistent MetavarContext):
\   lf-mctx-mark opens a scope (Lean's saveState, checkpointDefEq,
\   commitWhen); lf-mctx-rollback undoes every change made since, an
\   assignment (plain, level or delayed), a tag or a kind; lf-mctx-commit
\   keeps them. lf-mctx-snapshot ( -- snap outcome ) takes the state inside
\   an open scope (getMCtx) and lf-mctx-switch ( snap -- outcome ) goes to
\   it (setMCtx, withMCtx), from any state of the same scope.
\   lf-mctx-depth{ ( levels? -- scope outcome ) opens a scope one depth
\   deeper (withNewMCtxDepth allowLevelAssignments); }lf-mctx-depth
\   ( scope -- outcome ) rolls everything back and restores both depths.
\   Scopes nest; only the latest open one closes, by its own word (any
\   other is refused, invalid). See Scopes below.
\ - lf-depends-on? ( term fvar -- flag outcome ): Lean's exprDependsOn,
\   whether the term, its metavariables instantiated, holds the free
\   variable or an unassigned metavariable whose context holds it.
\ Words: lf-mctx-reset, lf-mctx-depth, lf-mctx-level-depth, mctx-epoch@
\ ( -- n );
\ lf-mctx-view ( -- view ), lf-mctx-view! ( view -- ); lf-locals-mark
\ ( -- view mark ), lf-locals-back ( view mark -- ): a scope of locals held
\ across steps that return in between (defeq.fs's binders, simp/main.fs's
\ binder visits): the view and the term mark (lf-lctx-drop's) taken, then
\ both put back, every local made since dropped;
\ lf-mctx-mark ( -- mark outcome ), lf-mctx-rollback ( mark -- outcome ),
\ lf-mctx-rollback-to ( mark -- outcome ) (every newer scope too),
\ lf-mctx-commit ( mark -- outcome ), lf-mctx-marks ( -- n ), lf-mctx-latest
\ ( -- mark ), lf-mctx-snapshot, lf-mctx-switch, lf-mctx-depth{,
\ }lf-mctx-depth, lf-mvar-depth ( mvar -- depth true | false );
\ lf-mvar-new ( type kind -- mvar outcome ), lf-mvar-new-at
\ ( type kind view -- mvar outcome ), lf-mvar-count ( -- n ), lf-mvar-at
\ ( n -- mvar ) (the n-th made), lf-mvar-named ( name -- mvar true | false
\ ) (findUserName?), lf-mvar-live?,
\ lf-mvar-type,
\ lf-mvar-kind, lf-mvar-value, lf-mvar-view, lf-mvar-tag ( mvar -- x true
\ | false ), lf-mvar-sees? ( mvar fvar -- flag ), lf-mvar-tag! ( mvar name
\ -- outcome ), lf-mvar-kind! ( mvar kind -- outcome ), lf-mvar-assignable?,
\ lf-mvar-assign ( mvar value -- outcome ), lf-delay-fvar ( fvar --
\ outcome ), lf-mvar-delay ( mvar pending n -- outcome ), lf-mvar-delayed
\ ( mvar -- pending addr n true | false ), lf-mvar-open? ( t -- flag ),
\ lf-level-mvar-new ( -- level
\ outcome ), lf-meta-const-fresh ( d -- term outcome )
\ (mkConstWithFreshMVarLevels), lf-level-mvar-live?, lf-level-mvar-value,
\ lf-level-mvar-depth ( level -- depth ), lf-level-mvar-assign
\ ( level value -- outcome ), lf-mvar-occurs? ( mvar term -- flag outcome ),
\ lf-level-mvar-occurs?, lf-level-assignable-mvar? ( level -- flag
\ outcome ), lf-level-stale-mvar?, lf-level-instantiate-mvars ( level -- level'
\ outcome ), lf-instantiate-mvars ( term -- term' outcome ),
\ lf-mvar-type-instantiated ( mvar -- type outcome ), lf-depends-on?.
\ State: the record mctx (the current view, three walk records of
\ dag-walk.fs and the spine table, heap blocks that live only while a walk
\ runs), the stores mv-exprs, mv-levels and mv-fvars and the slabs
\ mv-trail, mv-marks, mv-snaps, mv-redos and mv-args, in the checker
\ context (ADR 0009); the
\ views' state is lctx-views.fs's, emptied with lf-mctx-reset. Loads in
\ decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/find.fs
require ../core/terms.fs
require ../core/levels.fs
require ../core/local-context.fs
require ../core/generation-handles.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/tagged-sort-boundary.fs
require ../core/mvar-leaves.fs
require ../present/binder-table.fs
require ./dag-walk.fs
require ../core/let-terms.fs
require ./level-map.fs
require ./instantiate.fs
require ./meta-spine.fs
require ./lctx-views.fs

0 constant mv-natural
1 constant mv-synthetic
2 constant mv-opaque
1 31 lshift 1- constant mv-epoch-mask

begin-structure /mvd
  field: mvd-kind
  field: mvd-depth        \ the context's depth when it was made
  field: mvd-view         \ its local context, a view (lctx-views.fs)
  field: mvd-tag          \ its user name, a goal's tag (0: anonymous)
  field: mvd-type         \ its type, a term
  field: mvd-leaf         \ its leaf
  field: mvd-value        \ its assignment, a term, or -1
  field: mvd-pending      \ a delayed assignment's pending metavariable, or -1
  field: mvd-fvars        \ and the first of its free variables in mv-fvars
  field: mvd-fvars#       \ and how many
  field: mvd-inst         \ true: instance-typed (Lean's instanceTypedMVars)
end-structure
begin-structure /mvl
  field: mvl-depth
  field: mvl-leaf
  field: mvl-value        \ a level, or -1
end-structure
begin-structure /mctx
  field: mctx-epoch       \ leaves of another epoch are stale
  field: mctx-depth
  field: mctx-ldepth      \ Lean's levelAssignDepth
  field: mctx-at          \ the current state: a trail record, or -1
  field: mctx-target      \ the metavariable an occurs check seeks
  field: mctx-serial      \ the last serial given (scopes, snapshots)
  field: mctx-view        \ the current local context (Lean's Meta lctx)
  /dw +field mctx-walk    \ the term walks
  /dw +field mctx-lwalk   \ the level walks
  /dw +field mctx-hwalk   \ the search for a metavariable, inside a term walk
  field: mctx-delays      \ while terms are instantiated: a delayed step may apply
  field: mctx-spine       \ heap, while terms are instantiated: the spine table
end-structure
/mctx context-record: mctx
1 cells context-slab: mv-args     \ an application's argument images, last first
store-header context-record: mv-exprs
store-header context-record: mv-levels
store-header context-record: mv-fvars
begin-structure /mvt              \ a change in a scope (see Scopes, below)
  field: mvt-entry                \ the record's number * 8 + the field's kind
  field: mvt-old                  \ the field's value before the change
  field: mvt-new                  \ and after it
  field: mvt-parent               \ the state it changed: a record, or -1
end-structure
/mvt context-slab: mv-trail
begin-structure /mvs              \ an open scope
  field: mvs-serial
  field: mvs-kind                 \ mv-plain or mv-deep
  field: mvs-length               \ the trail's length when opened
  field: mvs-entry                \ the state when opened
  field: mvs-snaps                \ the snapshots' count when opened
  field: mvs-depth                \ the depths when opened
  field: mvs-ldepth
end-structure
/mvs context-slab: mv-marks
begin-structure /mvp              \ a snapshot
  field: mvp-serial
  field: mvp-at                   \ its state
end-structure
/mvp context-slab: mv-snaps
1 cells context-slab: mv-redos    \ a switch's records to redo, the last first

\ The stores: heap stores that grow up to the heap (plan task 6.2.0).
16 constant mv-room
: mv-make ( width store -- )
  2dup mv-room -rot 0 swap store-heap-init ok? 0= abort" mvars: no heap"
  swap store-most swap store-limit! ok? 0= abort" mvars: limit" ;
:noname ( -- )
  /mvd mv-exprs mv-make /mvl mv-levels mv-make 1 cells mv-fvars mv-make ; context-setup
:noname ( -- )
  mv-exprs store-heap-free mv-levels store-heap-free mv-fvars store-heap-free ;
  context-teardown

\ The context: emptied, with a new epoch, at depth 0, no scope open, the
\ empty local context current (every view gone).
\ The context's epoch, new at each lf-mctx-reset: a holder of results
\ about this context's terms (synth.fs's cache) can tell they are stale.
: mctx-epoch@ ( -- n ) mctx mctx-epoch @ ;
: lf-mctx-depth ( -- n ) mctx mctx-depth @ ;
: lf-mctx-level-depth ( -- n ) mctx mctx-ldepth @ ;
: mv-depths! ( depth ldepth -- ) mctx mctx-ldepth ! mctx mctx-depth ! ;
: mv-at ( -- i ) mctx mctx-at @ ;
: mv-at! ( i -- ) mctx mctx-at ! ;
: lf-mctx-marks ( -- n ) mv-marks slab-count ;
: mv-scopes-reset ( -- )
  mv-trail slab-clear mv-marks slab-clear mv-snaps slab-clear -1 mv-at! 0 0 mv-depths! ;
:noname ( -- ) -1 mv-at! ; context-setup
\ The current local context, which a new metavariable gets. Lean's
\ withLocalDecl is: make the free variable and its local, push it on
\ this view, set the result, run, set the old view back.
: lf-mctx-view ( -- view ) mctx mctx-view @ ;
: lf-mctx-view! ( view -- ) mctx mctx-view ! ;
: lf-locals-mark ( -- view mark ) lf-mctx-view lf-term-base lf-term-count @ + ;
: lf-locals-back ( view mark -- ) lf-lctx-drop lf-mctx-view! ;
\ Local k of the view in force, as a free variable.
: lf-mctx-fvar ( k -- fvar ) lf-mctx-view swap lf-view-fvar ;
: lf-mctx-reset ( -- )
  mv-exprs store-clear mv-levels store-clear mv-fvars store-clear mv-scopes-reset
  mctx-epoch@ 1+ mv-epoch-mask and mctx mctx-epoch !
  lf-views-reset lf-view-empty lf-mctx-view! ;

\ Live leaves: a term leaf is the one its record names (term leaves are
\ never shared, so a leaf of an emptied context is never a new record's);
\ a level leaf, which the level store may share by content, also carries
\ this context's epoch.
: mv-number ( leaf -- n ) lf-term-first@ ;
: mv-decl ( n -- addr ) mv-exprs store-slot ;
: mv-own? ( term -- flag )
  dup mv-number dup mv-exprs store-valid?
  if mv-decl mvd-leaf @ = else 2drop false then ;
: lf-mvar-live? ( term -- flag )
  dup lf-term-valid? if dup lf-mvar? if mv-own? exit then then drop false ;
: mv-of ( mvar -- addr true | false )
  dup lf-mvar-live? if mv-number mv-decl true else drop false then ;
: mv-field ( mvar offset -- x true | false ) swap mv-of if + @ true else drop false then ;
: lf-mvar-type ( mvar -- type true | false ) 0 mvd-type mv-field ;
: lf-mvar-kind ( mvar -- kind true | false ) 0 mvd-kind mv-field ;
: lf-mvar-view ( mvar -- view true | false ) 0 mvd-view mv-field ;
: lf-mvar-tag ( mvar -- name true | false ) 0 mvd-tag mv-field ;
: lf-mvar-depth ( mvar -- depth true | false ) 0 mvd-depth mv-field ;
: lf-mvar-value ( mvar -- value true | false )
  0 mvd-value mv-field dup if over 0< if 2drop false then then ;
\ Whether the free variable is in the metavariable's local context.
: lf-mvar-sees? ( mvar fvar -- flag )
  swap lf-mvar-view if swap lf-view-has? else drop false then ;

\ New term metavariables, in the current local context or a given one.
: mv-kind? ( kind -- flag ) mv-natural mv-opaque 1+ within ;
: mv-scope! ( addr -- )
  lf-mctx-depth over mvd-depth ! lf-mctx-view over mvd-view ! 0 over mvd-tag !
  -1 over mvd-value ! -1 swap mvd-pending ! ;
: mv-fill ( type kind leaf addr -- )
  dup /mvd erase dup mv-scope! tuck mvd-leaf ! tuck mvd-kind ! mvd-type ! ;
\ The record is claimed first and its leaf made next; a leaf the term
\ store refuses gives the record back (store-drop), so a refusal changes
\ nothing.
: mv-slot ( store -- addr index true | false )
  dup store-ready ok? 0= if drop false exit then store-new-slot ;
: mv-leafed ( type kind addr n -- mvar outcome )
  mctx-epoch@ lf-mvar-leaf 0= if drop 2drop mv-exprs store-drop -1 outcome-full exit then
  dup >r swap mv-fill r> outcome-ok ;
: mv-parts? ( type kind -- flag )
  mv-kind? swap lf-term-valid? and lf-mctx-view lf-view-valid? and ;
: lf-mvar-new ( type kind -- mvar outcome )
  2dup mv-parts? 0= if 2drop -1 outcome-invalid exit then
  mv-exprs mv-slot if mv-leafed else 2drop -1 outcome-full then ;
: lf-mvar-new-at ( type kind view -- mvar outcome )
  lf-mctx-view >r lf-mctx-view! lf-mvar-new r> lf-mctx-view! ;
\ How many term metavariables the context has made (Lean's mvarCounter:
\ a metavariable whose record number is at least an earlier count is new).
: lf-mvar-count ( -- n ) mv-exprs store-count @ ;
\ Metavariable n, below lf-mvar-count (unchecked): its record's leaf.
: lf-mvar-at ( n -- mvar ) mv-decl mvd-leaf @ ;
\ Lean's findUserName? (MetavarContext.lean, the userNames map): the
\ newest metavariable tagged name (not 0), assigned or not. Where Lean's
\ map has dropped a name a later tag replaced, this still finds the
\ older metavariable of that tag (its callers then answer unsupported).
: mv-tagged? ( name n -- name flag ) mv-decl mvd-tag @ over = ;
: lf-mvar-named ( name -- mvar true | false )
  lf-mvar-count ['] mv-tagged? find-last-index dup if swap lf-mvar-at swap then ;
: lf-mvar-assignable? ( mvar -- flag )
  mv-of 0= if false exit then
  dup mvd-kind @ mv-opaque <> swap mvd-depth @ lf-mctx-depth = and ;

\ Level metavariables: the level's second field is the epoch.
: mvl-number ( level -- n ) lf-level-slot node-first @ ;
: mvl-decl ( n -- addr ) mv-levels store-slot ;
: mvl-shape? ( level -- flag )
  dup lf-level-mvar? swap lf-level-slot node-second @ mctx-epoch@ = and ;
: mvl-own? ( level -- flag )
  dup mvl-number dup mv-levels store-valid?
  if mvl-decl mvl-leaf @ = else 2drop false then ;
: lf-level-mvar-live? ( level -- flag )
  dup lf-level-valid? if dup mvl-shape? if mvl-own? exit then then drop false ;
: lf-level-mvar-value ( level -- value true | false )
  dup lf-level-mvar-live? 0= if drop false exit then
  mvl-number mvl-decl mvl-value @ dup 0< if drop false else true then ;
\ Its depth (Lean's LMVarDecl.depth), or -1 for a level that is no live
\ metavariable.
: lf-level-mvar-depth ( level -- depth )
  dup lf-level-mvar-live? if mvl-number mvl-decl mvl-depth @ else drop -1 then ;
: mvl-fill ( leaf addr -- )
  tuck mvl-leaf ! lf-mctx-depth over mvl-depth ! -1 swap mvl-value ! ;
: mvl-leafed ( addr n -- level outcome )
  mctx-epoch@ lf-level-mvar-leaf 0= if drop mv-levels store-drop -1 outcome-full exit then
  tuck swap mvl-fill outcome-ok ;
: lf-level-mvar-new ( -- level outcome )
  mv-levels mv-slot if mvl-leafed else -1 outcome-full then ;
\ Lean's mkConstWithFreshMVarLevels: declaration d's constant at a new
\ level metavariable for each of its universe parameters (here, not in
\ meta-env.fs, which this file's walks load first).
: lf-meta-const-fresh ( d -- term outcome ) ['] lf-level-mvar-new lf-meta-const-with ;

\ ---- Walks (dag-walk.fs). A term's children are its two parts
\ (application, binders, let, projection) and, for an assigned
\ metavariable, its value; a level's are its parts (succ, max, imax) and,
\ for an assigned level metavariable, its value. An occurs check's image
\ is 1 when the node holds the target (mctx-target), else 0.
: mv-value-of ( term -- value true | false )
  dup lf-mvar-live? if lf-mvar-value else drop false then ;
: mv-term-pending ( node walk -- child true | false )
  over lf-term-binary? if dw-want-parts exit then
  swap mv-value-of if swap dw-want else drop false then ;
: mv-target ( -- addr ) mctx mctx-target ;
\ As Lean's occursCheck, a delayed metavariable leads on to its pending
\ one (and that to its value).
: mv-pending-of ( mvar -- pending true | false )
  mv-of 0= if false exit then mvd-pending @ dup 0< if drop false else true then ;
: mv-delay-leaf ( walk node -- child true | false )
  mv-pending-of if swap dw-want else drop false then ;
: mv-occurs-pending ( node walk -- child true | false )
  2dup mv-term-pending if nip nip true exit then
  over lf-mvar? if swap mv-delay-leaf else 2drop false then ;
: mv-leaf-hit ( node walk -- 0|1 )
  swap dup mv-value-of if nip swap dw-image exit then
  mv-pending-of if swap dw-image else drop 0 then ;
: mv-occurs-build ( node walk -- 0|1 )
  over mv-target @ = if 2drop 1 exit then
  over lf-term-binary? if dw-part-images or else mv-leaf-hit then ;
: lf-mvar-occurs? ( mvar term -- flag outcome )
  swap mv-target ! ['] mv-occurs-build ['] mv-occurs-pending mctx mctx-walk dw-on-terms
  dw-run swap 0<> swap ;

: mvl-first ( level -- child ) lf-level-slot node-first @ ;
: mvl-second ( level -- child ) lf-level-slot node-second @ ;
: mvl-tag ( level -- tag ) lf-level-slot node-tag @ ;
: mvl-succ? ( level -- flag ) mvl-tag lf-level-tag-succ = ;
: mvl-binary? ( level -- flag ) mvl-tag lf-level-binary-tag? ;
: mvl-value-of ( level -- value true | false )
  dup lf-level-mvar-live? if lf-level-mvar-value else drop false then ;
: mvl-pair-pending ( node walk -- child true | false )
  >r dup mvl-first swap mvl-second r> dw-want2 ;
: mvl-pending ( node walk -- child true | false )
  over mvl-binary? if mvl-pair-pending exit then
  over mvl-succ? if swap mvl-first swap dw-want exit then
  swap mvl-value-of if swap dw-want else drop false then ;
: mvl-pair-images ( node walk -- i1 i2 )
  over mvl-first over dw-image >r swap mvl-second swap dw-image r> swap ;
: mvl-walk ( build -- walk ) ['] mvl-pending mctx mctx-lwalk dw-on-levels ;
\ The level walk seeks the target, or with the target -1 an assignable
\ metavariable (Lean's isLevelMVarAssignable: live, made at the
\ context's levelAssignDepth or deeper), with -2 a stale one.
: mvl-depth-open? ( level -- flag ) lf-level-mvar-depth lf-mctx-level-depth < 0= ;
: mvl-open? ( level -- flag )
  dup lf-level-mvar-live? if mvl-depth-open? else drop false then ;
: mvl-stale? ( level -- flag )
  dup lf-level-mvar? if lf-level-mvar-live? 0= else drop false then ;
: mvl-hit? ( node -- flag )
  mv-target @ case -1 of mvl-open? endof -2 of mvl-stale? endof tuck = swap endcase ;
: mvl-occurs-build ( node walk -- 0|1 )
  over mvl-hit? if 2drop 1 exit then
  over mvl-binary? if mvl-pair-images or exit then
  over mvl-succ? if swap mvl-first swap dw-image exit then
  swap mvl-value-of if swap dw-image else drop 0 then ;
: lf-level-mvar-occurs? ( mvar level -- flag outcome )
  swap mv-target ! ['] mvl-occurs-build mvl-walk dw-run swap 0<> swap ;
\ Lean's hasAssignableLevelMVar; a stale metavariable anywhere.
: lf-level-assignable-mvar? ( level -- flag outcome ) -1 swap lf-level-mvar-occurs? ;
: lf-level-stale-mvar? ( level -- flag outcome ) -2 swap lf-level-mvar-occurs? ;

\ ---- Scopes: one undo trail shaped as a tree (S1 §3). While a scope is
\ open, each change of a record's field (an assignment, plain, level or
\ delayed, a tag, a kind) is a trail record: the entry (the record's
\ number * 8 + the field's kind), the old value, the new value and its
\ parent, the state it changed; the current state is a record (mctx-at),
\ or -1 for the state no record changed. A parent is always older than
\ its children, so two states meet at their common ancestor by climbing
\ from the newer one. A trail the heap cannot grow refuses the change,
\ full, and nothing changes.
\ A scope and a snapshot are serial numbers, 1, 2, ..., from one counter,
\ never given twice in a context (not even after lf-mctx-reset);
\ mv-marks keeps per open scope its kind (a mark, or a depth scope), the
\ trail's length, the state and the snapshots' count when it was opened,
\ and both depths. Every record made while a scope is open is newer than
\ its opening, so the states under the innermost scope are its entry and
\ the records from its length on.
\ - Rolling back the latest scope goes back to its entry, undoing the
\   records from the current state up, and drops its records; committing
\   keeps them for an outer scope. Either closes it, its snapshots become
\   stale, and when the last scope closes the trail is emptied. With no
\   switch the records form one chain: a mark is undone latest first, as
\   a LIFO trail is (defeq.fs's checkpoints, the tactics' saved states).
\ - A snapshot is the current state, taken inside an open scope. A switch
\   to it climbs from both states to their common ancestor, noting the
\   target's records on mv-redos, then undoes the current state's records
\   up to the ancestor and redoes the target's down from it: every field
\   has its value in the target state. The target must lie under the
\   innermost open scope (Lean switches only inside its synthesis
\   scope). A stale snapshot (its scope closed), 0 or one never given is
\   refused, invalid; a redo stack the heap cannot grow, full; nothing
\   changes then.
\ Any other scope (an inner one already closed, an outer one while an
\ inner is open, one from before a reset, 0, the refused one, or a scope
\ of the other kind) is refused, invalid, and nothing changes.
\ Metavariables made on another branch stay made, unassigned (Lean's
\ restored context no longer has them; no term then refers to them).
\ Postponed level constraints, part of Lean's saveState, are unsupported
\ (level-defeq.fs), so no scope keeps them.
0 constant mv-was-value
1 constant mv-was-level
2 constant mv-was-delay
3 constant mv-was-tag
4 constant mv-was-kind
5 constant mv-was-fvars
6 constant mv-was-fvars#
7 constant mv-was-inst
\ The field an entry names: the record's (of mv-levels for a level
\ assignment, else of mv-exprs) at the kind's offset.
: mv-offset ( kind -- u )
  case mv-was-value of 0 mvd-value endof  mv-was-level of 0 mvl-value endof
    mv-was-delay of 0 mvd-pending endof  mv-was-tag of 0 mvd-tag endof
    mv-was-kind of 0 mvd-kind endof  mv-was-fvars of 0 mvd-fvars endof
    mv-was-inst of 0 mvd-inst endof  0 mvd-fvars# swap endcase ;
: mv-record ( n kind -- addr ) mv-was-level = if mvl-decl else mv-decl then ;
: mv-cell ( entry -- addr ) dup 3 rshift over 7 and mv-record swap 7 and mv-offset + ;
: mv-entry ( n kind -- entry ) swap 3 lshift or ;
: mvt ( i -- addr ) mv-trail slab-at ;
: mv-parent ( i -- i' ) mvt mvt-parent @ ;
\ Redoing a record sets its field's new value and makes it the current
\ state, undoing it sets the old value and makes its parent so. A new
\ record (the current state already its number) gets its fields, its
\ parent the state before, and is redone.
: mvt-fill ( value entry parent -- )
  mv-at mvt tuck mvt-parent ! over mv-cell @ over mvt-old ! tuck mvt-entry ! mvt-new ! ;
: mv-redo ( i -- ) dup mv-at! mvt dup mvt-new @ swap mvt-entry @ mv-cell ! ;
: mv-undo ( i -- ) mvt dup mvt-old @ over mvt-entry @ mv-cell ! mvt-parent @ mv-at! ;
: mv-noted ( value entry i -- ) mv-at swap mv-at! mvt-fill mv-at mv-redo ;
\ Set the field of record n's kind to value: noted when a scope is open.
: mv-change ( value n kind -- outcome )
  mv-entry lf-mctx-marks 0= if mv-cell ! outcome-ok exit then
  1 mv-trail slab-claim ok-then? if mv-noted outcome-ok else nip nip then ;
\ Room for n changes that then cannot fail.
: mv-trail-room ( n -- outcome )
  lf-mctx-marks if mv-trail slab-room else drop outcome-ok then ;

\ The scopes.
0 constant mv-plain   1 constant mv-deep
: mv-latest ( -- addr ) lf-mctx-marks 1- mv-marks slab-at ;
: mv-latest? ( mark -- flag )
  lf-mctx-marks if mv-latest mvs-serial @ = else drop false then ;
: mv-scope? ( mark kind -- flag )
  swap mv-latest? if mv-latest mvs-kind @ = else drop false then ;
: mv-serial ( -- n ) 1 mctx mctx-serial +! mctx mctx-serial @ ;
: mv-scope-trail ( addr -- addr )
  mv-trail slab-count over mvs-length ! mv-at over mvs-entry !
  mv-snaps slab-count over mvs-snaps ! ;
: mv-scope-depths ( addr -- addr )
  lf-mctx-depth over mvs-depth ! lf-mctx-level-depth over mvs-ldepth ! ;
: mv-scope-fill ( kind addr -- serial )
  tuck mvs-kind ! mv-scope-trail mv-scope-depths mv-serial tuck swap mvs-serial ! ;
: mv-open ( kind -- mark outcome )
  1 mv-marks slab-claim ok-then? 0= if nip 0 swap exit then
  mv-marks slab-at mv-scope-fill outcome-ok ;
: mv-back-to ( i -- ) begin dup mv-at <> while mv-at mv-undo repeat drop ;
: mv-undo-scope ( -- )
  mv-latest dup mvs-entry @ mv-back-to mvs-length @ mv-trail slab-cut ;
: mv-close ( -- )
  mv-latest mvs-snaps @ mv-snaps slab-cut mv-marks slab-drop
  lf-mctx-marks 0= if mv-trail slab-clear -1 mv-at! then ;
: lf-mctx-mark ( -- mark outcome ) mv-plain mv-open ;
: lf-mctx-rollback ( mark -- outcome )
  mv-plain mv-scope? 0= if outcome-invalid exit then mv-undo-scope mv-close outcome-ok ;
: lf-mctx-commit ( mark -- outcome )
  mv-plain mv-scope? 0= if outcome-invalid exit then mv-close outcome-ok ;
\ The latest open scope, or 0 (none) when none is open.
: lf-mctx-latest ( -- mark ) lf-mctx-marks if mv-latest mvs-serial @ else 0 then ;
\ Depth scopes: one depth deeper, levelAssignDepth kept with levels?
\ (Lean's allowLevelAssignments), else the new depth (Lean's incDepth).
: mv-deeper ( levels? -- )
  lf-mctx-depth 1+ tuck swap if drop lf-mctx-level-depth then mv-depths! ;
: lf-mctx-depth{ ( levels? -- scope outcome )
  mv-deep mv-open ok-then? if swap mv-deeper outcome-ok else nip 0 swap then ;
: mv-depths-back ( -- ) mv-latest dup mvs-depth @ swap mvs-ldepth @ mv-depths! ;
: }lf-mctx-depth ( scope -- outcome )
  mv-deep mv-scope? 0= if outcome-invalid exit then
  mv-undo-scope mv-depths-back mv-close outcome-ok ;
\ Back to a plain mark through every newer scope (Lean's restore of a
\ saved MetavarContext, which replaces the whole context; review C1 of
\ 2026-11-18): each newer scope, plain or deep, is undone and closed,
\ latest first, a deep one's depths given back, and then the mark's. A
\ mark that is not open, or a depth scope, is refused, invalid, and
\ nothing changes.
: mv-serial-at ( i -- serial ) mv-marks slab-at mvs-serial @ ;
: mv-serial-is? ( mark i -- mark flag ) mv-serial-at over = ;
: mv-mark-index ( mark -- i true | false ) lf-mctx-marks ['] mv-serial-is? find-index ;
: mv-plain-at? ( i -- flag ) mv-marks slab-at mvs-kind @ mv-plain = ;
: mv-drop-scope ( -- )
  mv-undo-scope mv-latest mvs-kind @ mv-deep = if mv-depths-back then mv-close ;
: lf-mctx-rollback-to ( mark -- outcome )
  mv-mark-index 0= if outcome-invalid exit then
  dup mv-plain-at? 0= if drop outcome-invalid exit then
  lf-mctx-marks swap ?do mv-drop-scope loop outcome-ok ;

\ Snapshots, kept in serial order (a scope's close drops the newest), so
\ a serial is found by halving.
: mvp ( i -- addr ) mv-snaps slab-at ;
: mvp-below? ( key i -- flag ) mvp mvp-serial @ > ;
: mv-halve ( key lo hi -- key lo' hi' )
  2dup + 2/ 3 pick over mvp-below? if >r nip r> 1+ swap else nip then ;
: mv-bisect ( key -- key i )
  0 mv-snaps slab-count begin 2dup < while mv-halve repeat drop ;
: mvp-hit? ( key i -- flag )
  dup mv-snaps slab-count < if mvp mvp-serial @ = else 2drop false then ;
: mv-snap-index ( snap -- i true | false ) mv-bisect tuck mvp-hit? dup 0= if nip then ;
: mv-snap-fill ( addr -- serial ) mv-at over mvp-at ! mv-serial tuck swap mvp-serial ! ;
: mv-snap-new ( -- snap outcome )
  1 mv-snaps slab-claim ok-then? if mvp mv-snap-fill outcome-ok else 0 swap then ;
: lf-mctx-snapshot ( -- snap outcome )
  lf-mctx-marks if mv-snap-new else 0 outcome-invalid then ;
\ A state under the innermost scope: its entry, or a record made in it.
: mv-under? ( i -- flag )
  dup mv-latest mvs-entry @ = swap mv-latest mvs-length @ < 0= or ;
: mv-snap-at ( snap -- i true | false )
  mv-snap-index 0= if false exit then mvp mvp-at @ dup mv-under? dup 0= if nip then ;
\ The switch: the common ancestor c of the current state a and the target
\ b, b's records above c on mv-redos; then down from a to c, up to b.
: mv-redo-push ( i -- outcome ) mv-redos slab-push ;
: mv-climb ( a b -- a' b' outcome )
  2dup > if swap mv-parent swap outcome-ok exit then
  dup mv-redo-push dup ok? if drop mv-parent outcome-ok then ;
: mv-climbs ( a b -- c outcome )
  begin 2dup <> while mv-climb ok-then? 0= if nip -1 swap exit then repeat
  drop outcome-ok ;
: mv-redo-pop ( -- i ) mv-redos slab-pop ;
: mv-redo-all ( -- ) begin mv-redos slab-count while mv-redo-pop mv-redo repeat ;
: mv-goto ( i -- outcome )
  mv-redos slab-clear mv-at swap mv-climbs
  ok-then? if mv-back-to mv-redo-all outcome-ok then ;
: lf-mctx-switch ( snap -- outcome )
  lf-mctx-marks 0= if drop outcome-invalid exit then
  mv-snap-at if mv-goto else outcome-invalid then ;

\ ---- Assignment: once, to a live leaf, the occurs check passed; a walk
\ that fails gives its own outcome and nothing is assigned.
: mv-occurs-outcome ( flag outcome -- outcome )
  dup ok? 0= if nip exit then swap if drop outcome-invalid then ;
: mv-unassigned? ( addr -- flag ) dup mvd-value @ 0< swap mvd-pending @ 0< and ;
: mv-free? ( mvar -- flag ) mv-of if mv-unassigned? else false then ;
: mv-sound ( mvar value -- outcome )
  dup lf-term-valid? 0= if 2drop outcome-invalid exit then
  over mv-free? 0= if 2drop outcome-invalid exit then lf-mvar-occurs? mv-occurs-outcome ;
: lf-mvar-assign ( mvar value -- outcome )
  2dup mv-sound ok-then2? 0= if exit then
  swap mv-number mv-was-value mv-change ;
: mvl-free? ( level -- flag )
  dup lf-level-mvar-live? if mvl-number mvl-decl mvl-value @ 0< else drop false then ;
: mvl-sound ( mvar value -- outcome )
  dup lf-level-valid? 0= if 2drop outcome-invalid exit then
  over mvl-free? 0= if 2drop outcome-invalid exit then
  lf-level-mvar-occurs? mv-occurs-outcome ;
: lf-level-mvar-assign ( level value -- outcome )
  2dup mvl-sound ok-then2? 0= if exit then
  swap mvl-number mv-was-level mv-change ;

\ A tag (a name ID, or 0 for none) and a kind, set on a live metavariable
\ whether assigned or not, as Lean's setTag and setKind.
: lf-mvar-tag! ( mvar name -- outcome )
  2dup lf-user-name? swap lf-mvar-live? and 0= if 2drop outcome-invalid exit then
  swap mv-number mv-was-tag mv-change ;
: lf-mvar-mark-inst ( mvar -- outcome )
  dup lf-mvar-live? 0= if drop outcome-invalid exit then
  true swap mv-number mv-was-inst mv-change ;
: lf-mvar-inst? ( mvar -- flag ) 0 mvd-inst mv-field 0= if false then ;
: lf-mvar-kind! ( mvar kind -- outcome )
  2dup mv-kind? swap lf-mvar-live? and 0= if 2drop outcome-invalid exit then
  swap mv-number mv-was-kind mv-change ;

\ Delayed assignments: lf-delay-fvar appends a live free variable;
\ lf-mvar-delay gives the free metavariable mvar the last n appended and
\ the pending metavariable: three changes (the free variables' place and
\ count, then the pending one), room for all made first.
: lf-delay-fvar ( fvar -- outcome )
  dup lf-fvar-live? 0= if drop outcome-invalid exit then
  mv-fvars mv-slot if drop ! outcome-ok else drop outcome-full then ;
: mv-fvars# ( -- n ) mv-fvars store-count @ ;
: mv-delayable? ( mvar pending n -- flag )
  0 mv-fvars# 1+ within swap lf-mvar-live? and swap mv-free? and ;
: mv-delay-ok ( mvar pending n -- mvar pending n outcome )
  >r 2dup r@ mv-delayable? r> swap if 3 mv-trail-room else outcome-invalid then ;
: mv-delay-fvars ( n i -- i )
  2dup mv-was-fvars# mv-change drop
  swap mv-fvars# swap - over mv-was-fvars mv-change drop ;
: mv-delay-set ( pending n i -- ) mv-delay-fvars mv-was-delay mv-change drop ;
: lf-mvar-delay ( mvar pending n -- outcome )
  mv-delay-ok ok-then3? 0= if exit then
  >r swap mv-number r> swap mv-delay-set outcome-ok ;
: lf-mvar-delayed ( mvar -- pending addr n true | false )
  mv-of 0= if false exit then dup mvd-pending @ dup 0< if 2drop false exit then
  swap dup mvd-fvars @ mv-fvars store-slot swap mvd-fvars# @ true ;
\ Whether mvar is a delayed-assigned metavariable (Lean's isDelayedAssigned).
: lf-mvar-delayed? ( mvar -- flag ) lf-mvar-delayed dup if nip nip nip then ;
\ A metavariable leaf neither assigned nor delayed-assigned (the ones
\ Lean's getMVarsNoDelayed keeps, elimMVar's case); any other term false.
: lf-mvar-open? ( t -- flag )
  dup lf-mvar? 0= if drop false exit then
  dup lf-mvar-delayed if 2drop 2drop false exit then lf-mvar-value dup if nip then 0= ;

\ ---- Instantiation. Levels: a part that changes is rebuilt; an assigned
\ metavariable is its value's image.
: mvl-made ( new true | false -- level ) mctx mctx-lwalk dw-made ;
: mvl-same-pair? ( i1 i2 node -- i1 i2 flag )
  >r 2dup r@ mvl-second = swap r> mvl-first = and ;
: mvl-pair-build ( node walk -- image )
  over >r mvl-pair-images r@ mvl-same-pair? if 2drop r> exit then
  r> mvl-tag lf-level-binary mvl-made ;
: mvl-succ-build ( node walk -- image )
  over mvl-first swap dw-image 2dup swap mvl-first = if drop exit then
  nip lf-level-succ mvl-made ;
: mvl-leaf-build ( node walk -- image )
  over mvl-value-of if swap dw-image nip else drop then ;
: mvl-build ( node walk -- image )
  over mvl-binary? if mvl-pair-build exit then
  over mvl-succ? if mvl-succ-build else mvl-leaf-build then ;
: lf-level-instantiate-mvars ( level -- level' outcome ) ['] mvl-build mvl-walk dw-run ;

\ Terms, as Lean's instantiateMVars (its C++ instantiate_mvars, compared
\ with pinned Lean by tests/front/check_meta.py): a binary node whose
\ parts change is rebuilt with the binder's name and kind; a Sort gets its
\ level's image; an assigned metavariable is its value's image; a
\ constant gets its levels' images. An application ?f a1 .. an whose head
\ is assigned is the value's image applied to the arguments' images and
\ beta-reduced at the head (Lean's betaRev; instantiate.fs's
\ lf-meta-head-beta). An application ?d a1 .. an whose head has a delayed
\ assignment of k free variables, with n >= max(k, 1), its pending
\ metavariable assigned and that value's image holding no metavariable,
\ is fun x1 .. xk => value beta-reduced against all n arguments the same
\ way. Any other application gets its parts' images. Not ported, answered
\ unsupported, never another term: Lean instantiates an assigned head's
\ beta result again, which may change it when f or an argument has a ready
\ delayed metavariable at its spine head; a let that betaRev would
\ zeta-reduce; an argument with loose bound variables (instantiate1 does
\ not lift them). Lean writes an instantiated assignment back into the
\ context; this does not (the terms are the same).
: mv-twalk ( -- walk ) mctx mctx-walk ;
: mv-refuse ( outcome -- ) mv-twalk dw-refuse ;
: mv-image ( node -- image ) mv-twalk dw-image ;
: mv-unported ( -- -1 ) outcome-unsupported mv-refuse -1 ;
\ (A refusal with ok changes nothing: mv-refuse also keeps a made image.)
: mv-rebuild ( node walk -- image )
  over >r dw-part-images r> lf-meta-rebuilt mv-refuse ;
: mv-node-rebuild ( node -- image ) mv-twalk mv-rebuild ;
: mv-made ( term true | false -- term ) room-result mv-refuse ;

\ Spines, walking down the first parts; delayed heads ready for their
\ step (mctx-delays: some delayed assignment's pending one is assigned).
: mv-app? ( node -- flag ) lf-term-tag@ lf-tag-app = ;
: mv-assigned? ( head -- flag ) mv-value-of dup if nip then ;
: mv-delay-rec ( head -- rec true | false )
  mv-of 0= if false exit then dup mvd-pending @ 0< if drop false exit then
  dup mvd-pending @ mv-assigned? dup 0= if nip then ;
: mv-rec-k ( rec -- k ) mvd-fvars# @ ;
: mv-rec-pending-value ( rec -- value ) mvd-pending @ lf-mvar-value drop ;
: mv-delay-for ( n head -- rec true | false )
  mv-delay-rec 0= if drop false exit then
  tuck mv-rec-k 1 max < if drop false exit then true ;
: mv-delays? ( -- flag ) mctx mctx-delays @ ;
: mv-ready-decl? ( n -- flag )
  mv-decl mvd-pending @ dup 0< if drop false else mv-assigned? then ;
: mv-any-delay ( -- flag ) false mv-exprs store-count @ 0 ?do i mv-ready-decl? or loop ;

\ The spine table (a heap block for the walk, two cells per node) keeps
\ each application's head and argument count, from its first part's, so
\ a node finds them at once. mv-spine puts the arguments' images in
\ mv-args, the last first (a_j is n - j there).
: mv-head-cell ( node -- addr ) mctx mctx-spine @ pair-at ;
: mv-count-cell ( node -- addr ) mv-head-cell cell+ ;
: mv-first-head ( node -- head ) lf-term-first@ dup mv-app? if mv-head-cell @ then ;
: mv-first-count ( node -- n )
  lf-term-first@ dup mv-app? if mv-count-cell @ 1+ else drop 1 then ;
: mv-spine-set ( node -- )
  dup mv-first-head over mv-head-cell ! dup mv-first-count swap mv-count-cell ! ;

\ The walk's children: an application whose head is ready for its
\ delayed step (found from its first part's spine cells, built by then)
\ also has the pending one's value, unless that value is under way: the
\ value then holds this application (Lean finds it not ready, as it
\ still holds a metavariable). A search for a metavariable goes through
\ parts only.
: mv-app-delay ( node -- rec true | false )
  dup mv-first-count swap mv-first-head mv-delay-for ;
: mv-delay-child ( node -- value true | false )
  mv-delays? 0= if drop false exit then
  mv-app-delay if mv-rec-pending-value true else false then ;
: mv-fresh ( walk child -- child true | false )
  tuck swap dw-new? if true else drop false then ;
: mv-app-pending ( node walk -- child true | false )
  swap mv-delay-child if mv-fresh else drop false then ;
: mv-inst-pending ( node walk -- child true | false )
  2dup mv-term-pending if nip nip true exit then
  over mv-app? if mv-app-pending else 2drop false then ;
: mv-hole-build ( node walk -- 0|1 )
  over lf-term-binary? if dw-part-images or else drop lf-mvar? 1 and then ;
: mv-hole-walk ( term build -- flag outcome )
  ['] dw-want-binary mctx mctx-hwalk dw-on-terms dw-run swap 0<> swap ;
: mv-holes? ( term -- flag outcome ) ['] mv-hole-build mv-hole-walk ;

\ mv-spine puts an application's argument images in mv-args, the last
\ first (a_j is n - j there).
: mv-args# ( -- n ) mv-args slab-count ;
: mv-nth ( j -- image ) mv-args# swap - mv-args slab-at @ ;
: mv-arg-put ( image -- )
  1 mv-args slab-claim dup ok? if drop mv-args slab-at ! else mv-refuse 2drop then ;
: mv-spine ( node -- head )
  mv-args slab-clear begin dup mv-app? while dup lf-term-second@ mv-image mv-arg-put
  lf-term-first@ repeat ;
\ f applied to a_s+1 .. a_n (the arguments mv-args holds).
: mv-apply ( f s -- f' ) mv-args# swap ?do i 1+ mv-nth lf-term-app mv-made loop ;

\ betaRev's way through f with n arguments: its lambdas take them all, a
\ let comes first (zeta, not ported), or its lambdas run out first.
0 constant mv-all-taken
1 constant mv-zeta-met
2 constant mv-lams-run-out
: mv-lam? ( term -- flag ) lf-term-tag@ lf-tag-lam = ;
: mv-lams ( f n -- f' left )
  begin dup 0> while over mv-lam? 0= if exit then 1- swap lf-term-second@ swap repeat ;
: mv-after-lams ( f n -- code )
  mv-lams if lf-let? if mv-zeta-met else mv-lams-run-out then
  else drop mv-all-taken then ;
\ Lean's second pass over an assigned head's beta result changes it only
\ where a ready delayed metavariable is the spine head of f or of an
\ argument (it gains arguments there): not ported.
: mv-lands? ( term -- flag )
  mv-delays? if lf-meta-app-head mv-delay-rec dup if nip then else drop false then ;
: mv-args-land? ( -- flag ) false mv-args# 0 ?do i mv-args slab-at @ mv-lands? or loop ;
: mv-headed ( term -- image ) lf-meta-head-beta mv-refuse ;
: mv-beta-all ( node f -- image )
  swap mv-spine drop dup mv-lands? mv-args-land? or if drop mv-unported exit then
  0 mv-apply mv-headed ;
: mv-zeta ( node f -- image ) 2drop mv-unported ;
\ With more arguments than f's lambdas the node is its first part's image
\ (already reduced) applied to the last argument's.
: mv-run-out ( node f -- image )
  drop dup lf-term-first@ mv-image mv-lands?
  if drop mv-unported else mv-node-rebuild then ;
: mv-beta-at ( node head n -- image )
  swap mv-image tuck swap mv-after-lams case mv-all-taken of mv-beta-all endof
    mv-zeta-met of mv-zeta endof  mv-lams-run-out of mv-run-out endof endcase ;

\ The delayed step: F = fun x1 .. xk => value (the value's image with the
\ free variables abstracted, under k lambdas typed as ?d) beta-reduced
\ against all n arguments, as Lean does, with no second pass.
: mv-rec-fvars ( rec -- addr ) mvd-fvars @ mv-fvars store-slot ;
: mv-rec-abstract ( value rec -- e )
  dup mv-rec-fvars swap mv-rec-k lf-meta-abstract mv-refuse ;
: mv-lam-over ( body type -- lam ) swap lf-term-lam mv-made ;
: mv-lams-over ( e type k -- F ) 0 ?do tuck mv-lam-over swap loop drop ;
: mv-rec-fun ( value rec -- F )
  tuck mv-rec-abstract swap dup mvd-type @ swap mv-rec-k mv-lams-over ;
: mv-solid ( term -- term flag )
  dup mv-holes? dup ok? if drop 0= else mv-refuse drop false then ;
: mv-delay-beta ( node F -- image )
  swap mv-spine drop dup mv-args# mv-after-lams mv-zeta-met =
  if drop mv-unported exit then
  0 mv-apply mv-headed ;
\ ?d applied to #(k-1) .. #0, the variables of the lambdas around it in
\ order (an intro's or an alternative's fun x1 .. xk => ?d x1 .. xk): the
\ value abstracted is the image, as Lean's instantiateRevRange gives it
\ (each argument, lifted under the value's binders, is the variable
\ abstracted there), with no beta step and so no lifting (branch
\ s2-tactics: induction's cases hold binders around their hypotheses).
: mv-arg-at? ( j -- flag ) dup mv-nth swap mv-args# swap - lf-term-bvar-is? ;
: mv-own-bvars? ( k -- flag )
  mv-args# <> if false exit then true mv-args# 1+ 1 ?do i mv-arg-at? and loop ;
: mv-in-place? ( node rec -- node rec flag )
  over mv-spine drop dup mv-rec-k mv-own-bvars? ;
: mv-placed ( node rec -- image )
  dup mv-rec-pending-value mv-image mv-solid
  if swap mv-rec-abstract nip else 2drop mv-node-rebuild then ;
: mv-delay-step ( node rec -- image )
  mv-in-place? if mv-placed exit then
  dup mv-rec-pending-value mv-image mv-solid
  if swap mv-rec-fun mv-delay-beta else 2drop mv-node-rebuild then ;
: mv-delay-ready ( n head -- rec true | false )
  mv-delay-for 0= if false exit then
  dup mv-rec-pending-value mv-twalk dw-done? dup 0= if nip then ;
: mv-delay-at ( node head n -- image )
  swap mv-delay-ready if mv-delay-step else mv-node-rebuild then ;

: mv-app-build ( node walk -- image )
  drop dup mv-spine-set dup mv-head-cell @ over mv-count-cell @ over mv-assigned?
  if mv-beta-at else mv-delay-at then ;
: mv-pair-build ( node walk -- image ) over mv-app? if mv-app-build else mv-rebuild then ;
\ A Sort's level and a constant's universe arguments get their images
\ (level-map.fs rebuilds the node when one changes).
: mv-level-image ( level -- level' )
  lf-level-instantiate-mvars dup ok? if drop else mv-refuse then ;
: mv-sort-build ( node -- image ) ['] mv-level-image lf-meta-sort-remap mv-refuse ;
: mv-const-build ( node -- image ) ['] mv-level-image lf-meta-const-remap mv-refuse ;
: mv-leaf-build ( node walk -- image )
  over mv-value-of if swap dw-image nip else drop then ;
: mv-leaf-kind ( node walk -- image )
  over lf-term-tag@ case lf-tag-symbolic-sort of drop mv-sort-build endof
    lf-tag-constant of drop mv-const-build endof drop mv-leaf-build 0 endcase ;
: mv-build ( node walk -- image )
  over lf-term-binary? if mv-pair-build else mv-leaf-kind then ;
: mv-spine-block ( -- flag )
  lf-term-base lf-term-count @ + 2* cells 1 max allocate
  if drop false exit then mctx mctx-spine ! true ;
: mv-inst-run ( term -- term' outcome )
  mv-any-delay mctx mctx-delays !
  ['] mv-build ['] mv-inst-pending mv-twalk dw-on-terms dw-run ;
: lf-instantiate-mvars ( term -- term' outcome )
  mv-spine-block 0= if drop -1 outcome-full exit then
  mv-inst-run mctx mctx-spine heap-release ;
\ A metavariable's type, instantiated (Lean's instantiateMVars
\ (<- mvarId.getType)); invalid for one that is not live.
: lf-mvar-type-instantiated ( mvar -- type outcome )
  lf-mvar-type 0= if -1 outcome-invalid exit then lf-instantiate-mvars ;

\ ---- Dependencies, Lean's exprDependsOn (MetavarContext.lean, DependsOn):
\ the term is instantiated first (Lean visits an assigned metavariable's
\ value and instantiates an application whose head is one, which comes to
\ the same nodes); then it depends on fvar when it holds fvar, or a
\ metavariable left in it (unassigned, or delayed and not ready) whose
\ local context holds fvar: Lean's "may" dependency, as a value assigned
\ later could use fvar. The search walks parts only (mctx-hwalk, free
\ once the instantiation is done). An instantiation's failure is the
\ answer's outcome.
: mv-dep-hit? ( node -- flag )
  dup mv-target @ = if drop true exit then
  dup lf-mvar? if mv-target @ lf-mvar-sees? else drop false then ;
: mv-dep-build ( node walk -- 0|1 )
  over mv-dep-hit? if 2drop 1 exit then
  over lf-term-binary? if dw-part-images or else 2drop 0 then ;
: mv-dep-walk ( term -- flag outcome ) ['] mv-dep-build mv-hole-walk ;
: lf-depends-on? ( term fvar -- flag outcome )
  swap lf-instantiate-mvars ok-then? 0= if nip false swap exit then
  swap mv-target ! mv-dep-walk ;
base !   \ the BASE this file was loaded with

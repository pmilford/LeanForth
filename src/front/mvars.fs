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
\ - Depth: Lean's mctx.depth. lf-mctx-deeper and lf-mctx-shallower enter
\   and leave a level, as Lean's withNewMCtxDepth; lf-mvar-assignable?
\   holds for a natural or synthetic metavariable of the current depth.
\ - The local context a metavariable sees is the free variables of the
\   checker context's local context (core/local-context.fs) that existed
\   when it was made: their count, as the local context only grows while
\   a declaration is elaborated.
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
\ - Marks (Lean's checkpointDefEq): lf-mctx-mark opens one; lf-mctx-rollback
\   undoes every assignment made since, plain, level or delayed;
\   lf-mctx-commit keeps them. Marks nest; only the latest open mark may
\   be rolled back or committed (any other is refused, invalid).
\ Words: lf-mctx-reset, lf-mctx-deeper, lf-mctx-shallower, lf-mctx-depth;
\ lf-mctx-mark ( -- mark outcome ), lf-mctx-rollback ( mark -- outcome ),
\ lf-mctx-commit ( mark -- outcome ), lf-mctx-marks ( -- n ); lf-mvar-new
\ ( type kind -- mvar outcome ), lf-mvar-live?, lf-mvar-type,
\ lf-mvar-kind, lf-mvar-value, lf-mvar-lctx, lf-mvar-assignable?,
\ lf-mvar-assign ( mvar value -- outcome ), lf-delay-fvar ( fvar --
\ outcome ), lf-mvar-delay ( mvar pending n -- outcome ), lf-mvar-delayed
\ ( mvar -- pending addr n true | false ), lf-level-mvar-new ( -- level
\ outcome ), lf-level-mvar-live?, lf-level-mvar-value, lf-level-mvar-depth
\ ( level -- depth ), lf-level-mvar-assign
\ ( level value -- outcome ), lf-mvar-occurs? ( mvar term -- flag outcome ),
\ lf-level-mvar-occurs?, lf-level-assignable-mvar? ( level -- flag
\ outcome ), lf-level-stale-mvar?, lf-level-instantiate-mvars ( level -- level'
\ outcome ), lf-instantiate-mvars ( term -- term' outcome ).
\ State: the record mctx (with three walk records of dag-walk.fs and the
\ spine table, heap blocks that live only while a walk runs), the stores
\ mv-exprs, mv-levels and mv-fvars and the slabs mv-trail, mv-marks and
\ mv-args, in the checker context (ADR 0009).

require ../lib/lib.fs
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

0 constant mv-natural
1 constant mv-synthetic
2 constant mv-opaque
1 31 lshift 1- constant mv-epoch-mask

begin-structure /mvd
  field: mvd-kind
  field: mvd-depth        \ the context's depth when it was made
  field: mvd-lctx         \ free variables of the local context it sees
  field: mvd-type         \ its type, a term
  field: mvd-leaf         \ its leaf
  field: mvd-value        \ its assignment, a term, or -1
  field: mvd-pending      \ a delayed assignment's pending metavariable, or -1
  field: mvd-fvars        \ and the first of its free variables in mv-fvars
  field: mvd-fvars#       \ and how many
end-structure
begin-structure /mvl
  field: mvl-depth
  field: mvl-leaf
  field: mvl-value        \ a level, or -1
end-structure
begin-structure /mctx
  field: mctx-epoch       \ leaves of another epoch are stale
  field: mctx-depth
  field: mctx-target      \ the metavariable an occurs check seeks
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
1 cells context-slab: mv-trail    \ assignments under a mark: number * 4 + kind
1 cells context-slab: mv-marks    \ per open mark, the trail's length when made

\ The stores: heap stores that grow up to the heap (plan task 6.2.0).
16 constant mv-room
: mv-limit ( width -- n ) cell+ max-n store-header - swap / ;
: mv-make ( width store -- )
  2dup mv-room -rot 0 swap store-heap-init ok? 0= abort" mvars: no heap"
  swap mv-limit swap store-limit! ok? 0= abort" mvars: limit" ;
:noname ( -- )
  /mvd mv-exprs mv-make /mvl mv-levels mv-make 1 cells mv-fvars mv-make ; context-setup
:noname ( -- )
  mv-exprs store-heap-free mv-levels store-heap-free mv-fvars store-heap-free ;
  context-teardown

\ The context: emptied, with a new epoch, at depth 0, no mark open.
: mctx-epoch@ ( -- n ) mctx mctx-epoch @ ;
: lf-mctx-depth ( -- n ) mctx mctx-depth @ ;
: lf-mctx-deeper ( -- ) 1 mctx mctx-depth +! ;
: lf-mctx-shallower ( -- ) lf-mctx-depth 1- 0 max mctx mctx-depth ! ;
: lf-mctx-marks ( -- n ) mv-marks slab-count ;
: lf-mctx-reset ( -- )
  mv-exprs store-clear mv-levels store-clear mv-fvars store-clear mv-trail slab-clear
  mv-marks slab-clear mctx-epoch@ 1+ mv-epoch-mask and mctx mctx-epoch !
  0 mctx mctx-depth ! ;

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
: lf-mvar-lctx ( mvar -- n true | false ) 0 mvd-lctx mv-field ;
: lf-mvar-value ( mvar -- value true | false )
  0 mvd-value mv-field dup if over 0< if 2drop false then then ;

\ New term metavariables.
: mv-kind? ( kind -- flag ) mv-natural mv-opaque 1+ within ;
: mv-scope! ( addr -- )
  lf-mctx-depth over mvd-depth ! lf-lctx-count @ over mvd-lctx !
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
: lf-mvar-new ( type kind -- mvar outcome )
  over lf-term-valid? over mv-kind? and 0= if 2drop -1 outcome-invalid exit then
  mv-exprs mv-slot if mv-leafed else 2drop -1 outcome-full then ;
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

\ ---- Walks (dag-walk.fs). A term's children are its two parts
\ (application, binders, let, projection) and, for an assigned
\ metavariable, its value; a level's are its parts (succ, max, imax) and,
\ for an assigned level metavariable, its value. An occurs check's image
\ is 1 when the node holds the target (mctx-target), else 0.
: mv-undone ( child walk -- child true | false )
  over swap dw-done? if drop false else true then ;
: mv-binary? ( term -- flag ) lf-term-tag@ lf-term-binary-tag? ;
: mv-value-of ( term -- value true | false )
  dup lf-mvar-live? if lf-mvar-value else drop false then ;
: mv-pair-pending ( node walk -- child true | false )
  over lf-term-first@ over mv-undone if nip nip true exit then
  swap lf-term-second@ swap mv-undone ;
: mv-term-pending ( node walk -- child true | false )
  over mv-binary? if mv-pair-pending exit then
  swap mv-value-of if swap mv-undone else drop false then ;
: mv-pair-images ( node walk -- i1 i2 )
  over lf-term-first@ over dw-image >r swap lf-term-second@ swap dw-image r> swap ;
: mv-walk ( build pending walk -- walk )
  tuck dw-pending ! tuck dw-build ! lf-term-base lf-term-count @ + over dw-size ! ;
: mv-term-walk ( build -- walk ) ['] mv-term-pending mctx mctx-walk mv-walk ;
: mv-target ( -- addr ) mctx mctx-target ;
: mv-occurs-build ( node walk -- 0|1 )
  over mv-target @ = if 2drop 1 exit then
  over mv-binary? if mv-pair-images or exit then
  swap mv-value-of if swap dw-image else drop 0 then ;
: lf-mvar-occurs? ( mvar term -- flag outcome )
  swap mv-target ! ['] mv-occurs-build mv-term-walk dw-run swap 0<> swap ;

: mvl-first ( level -- child ) lf-level-slot node-first @ ;
: mvl-second ( level -- child ) lf-level-slot node-second @ ;
: mvl-tag ( level -- tag ) lf-level-slot node-tag @ ;
: mvl-succ? ( level -- flag ) mvl-tag lf-level-tag-succ = ;
: mvl-binary? ( level -- flag ) mvl-tag lf-level-binary-tag? ;
: mvl-value-of ( level -- value true | false )
  dup lf-level-mvar-live? if lf-level-mvar-value else drop false then ;
: mvl-pair-pending ( node walk -- child true | false )
  over mvl-first over mv-undone if nip nip true exit then
  swap mvl-second swap mv-undone ;
: mvl-pending ( node walk -- child true | false )
  over mvl-binary? if mvl-pair-pending exit then
  over mvl-succ? if swap mvl-first swap mv-undone exit then
  swap mvl-value-of if swap mv-undone else drop false then ;
: mvl-pair-images ( node walk -- i1 i2 )
  over mvl-first over dw-image >r swap mvl-second swap dw-image r> swap ;
: mvl-walk ( build -- walk )
  mctx mctx-lwalk tuck dw-build ! ['] mvl-pending over dw-pending !
  lf-level-count @ over dw-size ! ;
\ The level walk seeks the target, or with the target -1 an assignable
\ metavariable (Lean's isLevelMVarAssignable: live, made at the
\ context's depth or deeper), with -2 a stale one.
: mvl-open? ( level -- flag )
  dup lf-level-mvar-live? if lf-level-mvar-depth lf-mctx-depth < 0= else drop false then ;
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

\ ---- Marks, for Lean's checkpointDefEq (it saves the metavariable
\ context and restores it when the comparison fails): while a mark is
\ open each assignment, plain, level or delayed, is noted on the trail
\ mv-trail (its record's number * 4 + its kind) before it is stored; a
\ trail the heap cannot grow refuses the assignment (full). A mark is its
\ depth among the open marks (1, 2, ...); mv-marks keeps, per open mark,
\ the trail's length when it was made. Rolling back the latest open mark
\ undoes the assignments noted after it, latest first; committing it
\ keeps them, for an outer mark to undo; either closes it, and when the
\ last mark closes the trail is emptied. Any other mark (an inner mark
\ already closed, an outer one while an inner is open, a stale one) is
\ refused, invalid, and nothing changes. Metavariables made after a mark
\ stay made, unassigned (Lean's restored context no longer has them; no
\ term then refers to them).
0 constant mv-was-value
1 constant mv-was-level
2 constant mv-was-delay
: mv-note ( n kind -- outcome )
  lf-mctx-marks 0= if 2drop outcome-ok exit then swap 2 lshift or
  1 mv-trail slab-claim dup ok? if drop mv-trail slab-at ! outcome-ok else nip nip then ;
: mv-store ( value addr n kind -- outcome )
  mv-note dup ok? if drop ! outcome-ok else nip nip then ;
: mv-undo-cell ( entry -- addr )
  dup 2 rshift swap 3 and case mv-was-value of mv-decl mvd-value endof
    mv-was-level of mvl-decl mvl-value endof  swap mv-decl mvd-pending swap endcase ;
: mv-trail-top ( -- entry ) mv-trail dup slab-count 1- swap slab-at @ ;
: mv-undo ( -- ) mv-trail-top mv-undo-cell -1 swap ! -1 mv-trail slab-commit ;
: mv-undo-to ( length -- ) begin dup mv-trail slab-count < while mv-undo repeat drop ;
: mv-latest? ( mark -- flag ) dup 0> swap lf-mctx-marks = and ;
: mv-mark-length ( -- length ) lf-mctx-marks 1- mv-marks slab-at @ ;
: mv-unmark ( -- ) -1 mv-marks slab-commit lf-mctx-marks 0= if mv-trail slab-clear then ;
: lf-mctx-mark ( -- mark outcome )
  1 mv-marks slab-claim dup ok? 0= if nip 0 swap exit then
  drop mv-trail slab-count swap mv-marks slab-at ! lf-mctx-marks outcome-ok ;
: lf-mctx-rollback ( mark -- outcome )
  mv-latest? 0= if outcome-invalid exit then
  mv-mark-length mv-undo-to mv-unmark outcome-ok ;
: lf-mctx-commit ( mark -- outcome )
  mv-latest? 0= if outcome-invalid exit then mv-unmark outcome-ok ;

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
  2dup mv-sound dup ok? 0= if nip nip exit then drop
  swap mv-number dup mv-decl mvd-value swap mv-was-value mv-store ;
: mvl-free? ( level -- flag )
  dup lf-level-mvar-live? if mvl-number mvl-decl mvl-value @ 0< else drop false then ;
: mvl-sound ( mvar value -- outcome )
  dup lf-level-valid? 0= if 2drop outcome-invalid exit then
  over mvl-free? 0= if 2drop outcome-invalid exit then
  lf-level-mvar-occurs? mv-occurs-outcome ;
: lf-level-mvar-assign ( level value -- outcome )
  2dup mvl-sound dup ok? 0= if nip nip exit then drop
  swap mvl-number dup mvl-decl mvl-value swap mv-was-level mv-store ;

\ Delayed assignments: lf-delay-fvar appends a live free variable;
\ lf-mvar-delay gives the free metavariable mvar the last n appended and
\ the pending metavariable.
: lf-delay-fvar ( fvar -- outcome )
  dup lf-fvar-live? 0= if drop outcome-invalid exit then
  mv-fvars mv-slot if drop ! outcome-ok else drop outcome-full then ;
: mv-fvars# ( -- n ) mv-fvars store-count @ ;
: mv-delayable? ( mvar pending n -- flag )
  0 mv-fvars# 1+ within swap lf-mvar-live? and swap mv-free? and ;
: mv-delay! ( pending n addr -- )
  tuck mvd-fvars# ! mv-fvars# over mvd-fvars# @ - over mvd-fvars ! mvd-pending ! ;
: lf-mvar-delay ( mvar pending n -- outcome )
  >r 2dup r@ mv-delayable? 0= if r> drop 2drop outcome-invalid exit then
  swap mv-number dup mv-was-delay mv-note dup ok? 0= if nip nip r> drop exit then
  drop r> swap mv-decl mv-delay! outcome-ok ;
: lf-mvar-delayed ( mvar -- pending addr n true | false )
  mv-of 0= if false exit then dup mvd-pending @ dup 0< if 2drop false exit then
  swap dup mvd-fvars @ mv-fvars store-slot swap mvd-fvars# @ true ;

\ ---- Instantiation. Levels: a part that changes is rebuilt; an assigned
\ metavariable is its value's image.
: mvl-refuse ( outcome -- ) mctx mctx-lwalk dw-refuse ;
: mvl-made ( new true | false -- level ) 0= if outcome-full mvl-refuse 0 then ;
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
\ beta result again, which changes it when f or an argument has a ready
\ delayed metavariable at its spine head; a let that betaRev would
\ zeta-reduce; an argument with loose bound variables (instantiate1 does
\ not lift them). Lean writes an instantiated assignment back into the
\ context; this does not (the terms are the same).
: mv-twalk ( -- walk ) mctx mctx-walk ;
: mv-refuse ( outcome -- ) mv-twalk dw-refuse ;
: mv-image ( node -- image ) mv-twalk dw-image ;
: mv-unported ( -- -1 ) outcome-unsupported mv-refuse -1 ;
: mv-named ( new old -- new ) lf-pres-binder@ if 2>r dup 2r> lf-pres-binder! drop then ;
: mv-same-pair? ( i1 i2 node -- i1 i2 flag )
  >r 2dup r@ lf-term-second@ = swap r> lf-term-first@ = and ;
: mv-rebuild ( node walk -- image )
  over >r mv-pair-images r@ mv-same-pair? if 2drop r> exit then
  r@ lf-term-tag@ lf-term-binary if r> mv-named exit then r> outcome-full mv-refuse ;
: mv-node-rebuild ( node -- image ) mv-twalk mv-rebuild ;
: mv-remapped ( image outcome -- image ) dup ok? if drop else mv-refuse then ;
: mv-made ( term true | false -- term ) 0= if outcome-full mv-refuse -1 then ;

\ Spines, walking down the first parts; delayed heads ready for their
\ step (mctx-delays: some delayed assignment's pending one is assigned).
: mv-app? ( node -- flag ) lf-term-tag@ lf-tag-app = ;
: mv-spine-head ( term -- head ) begin dup mv-app? while lf-term-first@ repeat ;
: mv-spine-n ( term -- n )
  0 swap begin dup mv-app? while lf-term-first@ swap 1+ swap repeat drop ;
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

\ The walk's children: an application whose head is ready for its
\ delayed step also has the pending one's value; a search for a
\ metavariable goes through parts only.
: mv-app-delay ( node -- rec true | false )
  dup mv-spine-n swap mv-spine-head mv-delay-for ;
: mv-delay-child ( node -- value true | false )
  mv-delays? 0= if drop false exit then
  mv-app-delay if mv-rec-pending-value true else false then ;
: mv-app-pending ( node walk -- child true | false )
  swap mv-delay-child if swap mv-undone else drop false then ;
: mv-inst-pending ( node walk -- child true | false )
  2dup mv-term-pending if nip nip true exit then
  over mv-app? if mv-app-pending else 2drop false then ;
: mv-hole-pending ( node walk -- child true | false )
  over mv-binary? if mv-pair-pending else 2drop false then ;
: mv-hole-build ( node walk -- 0|1 )
  over mv-binary? if mv-pair-images or else drop lf-mvar? 1 and then ;
: mv-holes? ( term -- flag outcome )
  ['] mv-hole-build ['] mv-hole-pending mctx mctx-hwalk mv-walk dw-run swap 0<> swap ;

\ The spine table (a heap block for the walk, two cells per node) keeps
\ each application's head and argument count, from its first part's, so
\ a node finds them at once. mv-spine puts the arguments' images in
\ mv-args, the last first (a_j is n - j there).
: mv-head-cell ( node -- addr ) 2* cells mctx mctx-spine @ + ;
: mv-count-cell ( node -- addr ) mv-head-cell cell+ ;
: mv-first-head ( node -- head ) lf-term-first@ dup mv-app? if mv-head-cell @ then ;
: mv-first-count ( node -- n )
  lf-term-first@ dup mv-app? if mv-count-cell @ 1+ else drop 1 then ;
: mv-spine-set ( node -- )
  dup mv-first-head over mv-head-cell ! dup mv-first-count swap mv-count-cell ! ;
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
  mv-delays? if mv-spine-head mv-delay-rec dup if nip then else drop false then ;
: mv-args-land? ( -- flag ) false mv-args# 0 ?do i mv-args slab-at @ mv-lands? or loop ;
: mv-headed ( term -- image ) lf-meta-head-beta mv-remapped ;
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
  dup mv-rec-fvars swap mv-rec-k lf-meta-abstract mv-remapped ;
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
: mv-delay-step ( node rec -- image )
  dup mv-rec-pending-value mv-image mv-solid
  if swap mv-rec-fun mv-delay-beta else 2drop mv-node-rebuild then ;
: mv-delay-at ( node head n -- image )
  swap mv-delay-for if mv-delay-step else mv-node-rebuild then ;

: mv-app-build ( node walk -- image )
  drop dup mv-spine-set dup mv-head-cell @ over mv-count-cell @ over mv-assigned?
  if mv-beta-at else mv-delay-at then ;
: mv-pair-build ( node walk -- image ) over mv-app? if mv-app-build else mv-rebuild then ;
\ A Sort's level and a constant's universe arguments get their images
\ (level-map.fs rebuilds the node when one changes).
: mv-level-image ( level -- level' )
  lf-level-instantiate-mvars dup ok? if drop else mv-refuse then ;
: mv-sort-build ( node -- image ) ['] mv-level-image lf-meta-sort-remap mv-remapped ;
: mv-const-build ( node -- image ) ['] mv-level-image lf-meta-const-remap mv-remapped ;
: mv-leaf-build ( node walk -- image )
  over mv-value-of if swap dw-image nip else drop then ;
: mv-leaf-kind ( node walk -- image )
  over lf-term-tag@ case lf-tag-symbolic-sort of drop mv-sort-build endof
    lf-tag-constant of drop mv-const-build endof drop mv-leaf-build 0 endcase ;
: mv-build ( node walk -- image )
  over mv-binary? if mv-pair-build else mv-leaf-kind then ;
: mv-spine-block ( -- flag )
  lf-term-base lf-term-count @ + 2* cells 1 max allocate
  if drop false exit then mctx mctx-spine ! true ;
: mv-inst-run ( term -- term' outcome )
  mv-any-delay mctx mctx-delays !
  ['] mv-build ['] mv-inst-pending mv-twalk mv-walk dw-run ;
: lf-instantiate-mvars ( term -- term' outcome )
  mv-spine-block 0= if drop -1 outcome-full exit then
  mv-inst-run mctx mctx-spine heap-release ;

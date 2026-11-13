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
\   images, and a node that changes nothing stays the same node. Two steps
\   of Lean's need the instantiation of bound variables (plan FE1c) and
\   answer unsupported until then, never another term: the beta step for
\   ?f a when ?f's value is a lambda, and putting in a delayed assignment's
\   value once its pending metavariable is assigned (an unassigned one
\   stays, as in Lean, and the export writer refuses the hole).
\ Outcomes: ok; invalid for a stale or unknown leaf, an assigned one, an
\ occurs-check failure or a cycle; full when a store or the heap has no
\ room; unsupported as above. Untrusted: whatever the context says, only
\ the kernel's check of the finished term decides anything.
\ Words: lf-mctx-reset, lf-mctx-deeper, lf-mctx-shallower, lf-mctx-depth;
\ lf-mvar-new ( type kind -- mvar outcome ), lf-mvar-live?, lf-mvar-type,
\ lf-mvar-kind, lf-mvar-value, lf-mvar-lctx, lf-mvar-assignable?,
\ lf-mvar-assign ( mvar value -- outcome ), lf-delay-fvar ( fvar --
\ outcome ), lf-mvar-delay ( mvar pending n -- outcome ), lf-mvar-delayed
\ ( mvar -- pending addr n true | false ), lf-level-mvar-new ( -- level
\ outcome ), lf-level-mvar-live?, lf-level-mvar-value, lf-level-mvar-assign
\ ( level value -- outcome ), lf-mvar-occurs? ( mvar term -- flag outcome ),
\ lf-level-mvar-occurs?, lf-level-instantiate-mvars ( level -- level'
\ outcome ), lf-instantiate-mvars ( term -- term' outcome ).
\ State: the record mctx (with the two walk records of dag-walk.fs, whose
\ heap blocks live only while a walk runs) and the stores mv-exprs,
\ mv-levels and mv-fvars, in the checker context (ADR 0009).

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
  field: mctx-pairs       \ heap, while a constant is rebuilt: its new level pairs
  /dw +field mctx-walk    \ the term walks
  /dw +field mctx-lwalk   \ the level walks
end-structure
/mctx context-record: mctx
store-header context-record: mv-exprs
store-header context-record: mv-levels
store-header context-record: mv-fvars

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

\ The context: emptied, with a new epoch, at depth 0.
: mctx-epoch@ ( -- n ) mctx mctx-epoch @ ;
: lf-mctx-depth ( -- n ) mctx mctx-depth @ ;
: lf-mctx-deeper ( -- ) 1 mctx mctx-depth +! ;
: lf-mctx-shallower ( -- ) lf-mctx-depth 1- 0 max mctx mctx-depth ! ;
: lf-mctx-reset ( -- )
  mv-exprs store-clear mv-levels store-clear mv-fvars store-clear
  mctx-epoch@ 1+ mv-epoch-mask and mctx mctx-epoch ! 0 mctx mctx-depth ! ;

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
: mv-term-walk ( build -- walk )
  mctx mctx-walk tuck dw-build ! ['] mv-term-pending over dw-pending !
  lf-term-base lf-term-count @ + over dw-size ! ;
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
: mvl-occurs-build ( node walk -- 0|1 )
  over mv-target @ = if 2drop 1 exit then
  over mvl-binary? if mvl-pair-images or exit then
  over mvl-succ? if swap mvl-first swap dw-image exit then
  swap mvl-value-of if swap dw-image else drop 0 then ;
: lf-level-mvar-occurs? ( mvar level -- flag outcome )
  swap mv-target ! ['] mvl-occurs-build mvl-walk dw-run swap 0<> swap ;

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
  swap mv-number mv-decl mvd-value ! outcome-ok ;
: mvl-free? ( level -- flag )
  dup lf-level-mvar-live? if mvl-number mvl-decl mvl-value @ 0< else drop false then ;
: mvl-sound ( mvar value -- outcome )
  dup lf-level-valid? 0= if 2drop outcome-invalid exit then
  over mvl-free? 0= if 2drop outcome-invalid exit then
  lf-level-mvar-occurs? mv-occurs-outcome ;
: lf-level-mvar-assign ( level value -- outcome )
  2dup mvl-sound dup ok? 0= if nip nip exit then drop
  swap mvl-number mvl-decl mvl-value ! outcome-ok ;

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
  r> rot mv-number mv-decl mv-delay! outcome-ok ;
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

\ Terms: a binary node whose parts change is rebuilt with the binder's
\ name and kind; a Sort gets its level's image; an assigned metavariable
\ is its value's image; a constant gets its levels' images.
: mv-refuse ( outcome -- ) mctx mctx-walk dw-refuse ;
: mv-named ( new old -- new ) lf-pres-binder@ if 2>r dup 2r> lf-pres-binder! drop then ;
: mv-same-pair? ( i1 i2 node -- i1 i2 flag )
  >r 2dup r@ lf-term-second@ = swap r> lf-term-first@ = and ;
\ Lean's instantiateMVars beta-reduces ?f a when ?f's value is a lambda,
\ and puts a delayed assignment's value in once its pending metavariable
\ is assigned; both need the front end's instantiation of bound variables
\ (plan FE1c) and answer unsupported until then, never another term.
: mv-lambda? ( term -- flag ) lf-term-tag@ lf-tag-lam = ;
: mv-beta? ( node walk -- flag )
  over lf-term-tag@ lf-tag-app = 0= if 2drop false exit then
  swap lf-term-first@ dup mv-value-of
  if drop swap dw-image mv-lambda? else 2drop false then ;
: mv-ready? ( pending -- flag ) lf-mvar-value dup if nip then ;
: mv-delayed-ready? ( term -- flag ) lf-mvar-delayed if 2drop mv-ready? else false then ;
: mv-rebuild ( node walk -- image )
  over >r mv-pair-images r@ mv-same-pair? if 2drop r> exit then
  r@ lf-term-tag@ lf-term-binary if r> mv-named exit then r> outcome-full mv-refuse ;
: mv-pair-build ( node walk -- image )
  2dup mv-beta? if drop outcome-unsupported mv-refuse else mv-rebuild then ;
\ A level's identity, or 0 for no level (lf-hterm-sort and lf-cref-new
\ then refuse it).
: mv-identity ( level -- identity ) lf-level-identity 0= if 0 then ;
: mv-sort-new ( level -- image )
  dup mv-identity lf-hterm-sort if drop else outcome-full mv-refuse -1 then ;
: mv-sort-level ( node -- node level' true | node false )
  dup lf-term-first@ lf-level-instantiate-mvars dup ok? if drop true exit then
  mv-refuse drop false ;
: mv-sort-build ( node -- image )
  mv-sort-level 0= if exit then 2dup swap lf-term-first@ = if drop exit then
  nip mv-sort-new ;
\ A constant whose universe arguments change gets a reference to the same
\ name with each argument's image, built in a heap block of (level,
\ identity) pairs freed at once (core/constant-references.fs).
: mv-level-image ( level -- level' )
  lf-level-instantiate-mvars dup ok? if drop else mv-refuse then ;
: mv-cref ( term -- slot ) lf-term-first@ lf-cref-slot ;
: mv-moves? ( flag addr i -- flag' ) lf-cref-pair@ drop dup mv-level-image <> or ;
: mv-cref-moves? ( term -- flag )
  mv-cref lf-cref-pairs false swap 0 ?do over i mv-moves? loop nip ;
: mv-pairs-at ( i -- addr ) 2* cells mctx mctx-pairs @ + ;
: mv-pair! ( level addr -- ) >r dup mv-identity swap r> 2! ;
: mv-image-pairs ( addr count -- )
  0 ?do dup i lf-cref-pair@ drop mv-level-image i mv-pairs-at mv-pair! loop drop ;
: mv-block ( count -- flag )
  2* cells 1 max allocate if drop false exit then mctx mctx-pairs ! true ;
: mv-ref-new ( slot -- term true | false )
  dup lf-cref-name@ rot lf-cref-pairs nip mctx mctx-pairs @ swap lf-cref-new
  if lf-cterm-new if drop true exit then then false ;
: mv-const-new ( node -- image )
  dup mv-cref lf-cref-pairs dup mv-block 0= if 2drop outcome-full mv-refuse exit then
  mv-image-pairs dup mv-cref mv-ref-new mctx mctx-pairs heap-release
  if nip else outcome-full mv-refuse then ;
: mv-const-build ( node -- image ) dup mv-cref-moves? if mv-const-new then ;
: mv-leaf-build ( node walk -- image )
  over mv-delayed-ready? if drop outcome-unsupported mv-refuse exit then
  over mv-value-of if swap dw-image nip else drop then ;
: mv-leaf-kind ( node walk -- image )
  over lf-term-tag@ case lf-tag-symbolic-sort of drop mv-sort-build endof
    lf-tag-constant of drop mv-const-build endof drop mv-leaf-build 0 endcase ;
: mv-build ( node walk -- image )
  over mv-binary? if mv-pair-build else mv-leaf-kind then ;
: lf-instantiate-mvars ( term -- term' outcome ) ['] mv-build mv-term-walk dw-run ;

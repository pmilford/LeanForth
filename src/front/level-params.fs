\ Universe-parameter instantiation of the front end (plan FE1c; ADR 0021
\ D6), ports of Lean 4.35.0's Level.instantiateParams (Lean/Level.lean:
\ substParams with getParamSubst) and Expr.instantiateLevelParams
\ (Lean/Util/InstantiateLevelParams.lean), which put a constant's
\ universe arguments into its type or value (delta, inferType).
\ - lf-meta-level-params ( level names levels n -- level' outcome ): the
\   parameter names[i] becomes levels[i] (the first equal name, as
\   getParamSubst), for n names and levels in cells at the two addresses.
\   A level without parameters is kept, so is one whose parameter is not
\   named; k successors of a named parameter become k successors of its
\   level. Lean rebuilds a max or imax over parameters with mkLevelMax'
\   and mkLevelIMax', which simplify (Level.updateMax!): not ported yet,
\   so such a level answers unsupported, never another level.
\ - lf-meta-instantiate-level-params ( term names levels n -- term'
\   outcome ): every Sort's level and every constant's universe arguments
\   in term, as above; a node whose data word shows no parameter (Lean's
\   hasLevelParam test) is kept, so is a node whose parts do not change;
\   a constant gets a new reference with its levels' images (as
\   mvars.fs's instantiation makes one), a binder keeps its name and kind.
\ The term walk is dag-walk.fs's (a memo per node, heap stacks: no depth
\ needs the host's stacks, plan task 6.2.0); a level is a chain of
\ successors over a base, walked in a loop.
\ Outcomes: ok; invalid for a negative count or a term or level not in
\ the store; unsupported as above; full when a store or the heap has no
\ room. Untrusted front-end code.
\ Words: lf-meta-level-params, lf-meta-instantiate-level-params.
\ State: the record lp-state (the substitution, the walk, the heap block
\ of level pairs while a constant is rebuilt), a member of the checker
\ context (ADR 0009).

require ../lib/lib.fs
require ../core/terms.fs
require ../core/levels.fs
require ../core/generation-handles.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/tagged-sort-boundary.fs
require ../present/binder-table.fs
require ./dag-walk.fs
require ./level-defeq.fs

begin-structure /lp
  field: lp-names-at     \ address of the parameter names' cells
  field: lp-levels-at    \ address of their levels' cells
  field: lp-n            \ how many
  field: lp-pairs        \ heap, while a constant is rebuilt: its level pairs
  /dw +field lp-dw       \ the term walk
end-structure
/lp context-record: lp-state

\ The substitution: Lean's getParamSubst, the first equal name.
: lp-count ( -- n ) lp-state lp-n @ ;
: lp-name ( i -- name ) cells lp-state lp-names-at @ + @ ;
: lp-arg ( i -- level ) cells lp-state lp-levels-at @ + @ ;
: lp-index ( name -- i true | false )
  lp-count 0 ?do dup i lp-name = if drop i true unloop exit then loop drop false ;
: lp-set ( names levels n -- ) lp-state tuck lp-n ! tuck lp-levels-at ! lp-names-at ! ;

\ Levels: k successors over a base; a named parameter's image.
: lp-param? ( level -- flag ) lf-level-tag@ lf-level-tag-param = ;
: lp-mapped ( base -- level true | false )
  lf-level-first@ lp-index if lp-arg true else false then ;
: lp-succs ( level k -- level' true | false )
  0 ?do lf-level-succ 0= if false unloop exit then loop true ;
: lp-shift ( level image k -- level' outcome )
  lp-succs if nip outcome-ok else drop -1 outcome-full then ;
: lp-level ( level -- level' outcome )
  dup lf-level-params? 0= if outcome-ok exit then
  dup ld-offset swap dup lp-param? 0= if 2drop drop -1 outcome-unsupported exit then
  lp-mapped if swap lp-shift else drop outcome-ok then ;
: lp-count-ok? ( n -- flag ) 0< 0= ;
: lf-meta-level-params ( level names levels n -- level' outcome )
  dup lp-count-ok? 0= if 2drop 2drop -1 outcome-invalid exit then lp-set
  dup lf-level-root? if lp-level else drop -1 outcome-invalid then ;

\ The term walk: a node's children are its parts, unless its data word
\ shows no parameter.
: lp-refuse ( outcome -- ) lp-state lp-dw dw-refuse ;
: lp-binary? ( node -- flag ) lf-term-tag@ lf-term-binary-tag? ;
: lp-fixed? ( node -- flag ) lf-term-data@ if lf-data-params? 0= else false then ;
: lp-undone ( child walk -- child true | false )
  over swap dw-done? if drop false else true then ;
: lp-parts-pending ( node walk -- child true | false )
  over lf-term-first@ over lp-undone if nip nip true exit then
  swap lf-term-second@ swap lp-undone ;
: lp-pending ( node walk -- child true | false )
  over dup lp-fixed? swap lp-binary? 0= or if 2drop false else lp-parts-pending then ;

\ Images of a binary node: rebuilt, with its binder's name, when a part
\ changes.
: lp-images ( node walk -- i1 i2 )
  over lf-term-first@ over dw-image >r swap lf-term-second@ swap dw-image r> swap ;
: lp-same? ( i1 i2 node -- i1 i2 flag )
  >r 2dup r@ lf-term-second@ = swap r> lf-term-first@ = and ;
: lp-named ( new old -- new ) lf-pres-binder@ if 2>r dup 2r> lf-pres-binder! drop then ;
: lp-rebuild ( i1 i2 node -- image )
  dup >r lf-term-tag@ lf-term-binary if r> lp-named exit then
  r> drop outcome-full lp-refuse -1 ;
: lp-pair-build ( node walk -- image )
  over >r lp-images r@ lp-same? if 2drop r> exit then r> lp-rebuild ;

\ A Sort over a level that changes gets a new leaf.
: lp-image ( level -- level' ) lp-level dup ok? if drop else lp-refuse then ;
: lp-identity ( level -- identity ) lf-level-identity 0= if 0 then ;
: lp-sort-new ( level -- image )
  dup lp-identity lf-hterm-sort if drop else outcome-full lp-refuse -1 then ;
: lp-sort-build ( node -- image )
  dup lf-term-first@ lp-image 2dup swap lf-term-first@ =
  if drop else nip lp-sort-new then ;

\ A constant whose universe arguments change gets a reference to the same
\ name with each argument's image, built in a heap block of (level,
\ identity) pairs freed at once (core/constant-references.fs).
: lp-cref ( term -- slot ) lf-term-first@ lf-cref-slot ;
: lp-moves? ( flag addr i -- flag' ) lf-cref-pair@ drop dup lp-image <> or ;
: lp-cref-moves? ( term -- flag )
  lp-cref lf-cref-pairs false swap 0 ?do over i lp-moves? loop nip ;
: lp-pairs-at ( i -- addr ) 2* cells lp-state lp-pairs @ + ;
: lp-pair! ( level addr -- ) >r dup lp-identity swap r> 2! ;
: lp-image-pairs ( addr count -- )
  0 ?do dup i lf-cref-pair@ drop lp-image i lp-pairs-at lp-pair! loop drop ;
: lp-block ( count -- flag )
  2* cells 1 max allocate if drop false exit then lp-state lp-pairs ! true ;
: lp-ref-new ( slot -- term true | false )
  dup lf-cref-name@ rot lf-cref-pairs nip lp-state lp-pairs @ swap lf-cref-new
  if lf-cterm-new if drop true exit then then false ;
: lp-const-new ( node -- image )
  dup lp-cref lf-cref-pairs dup lp-block 0=
  if 2drop outcome-full lp-refuse exit then
  lp-image-pairs dup lp-cref lp-ref-new lp-state lp-pairs heap-release
  if nip else outcome-full lp-refuse then ;
: lp-const-build ( node -- image ) dup lp-cref-moves? if lp-const-new then ;

: lp-leaf-build ( node -- image )
  dup lf-term-tag@ case lf-tag-symbolic-sort of lp-sort-build endof
    lf-tag-constant of lp-const-build endof endcase ;
: lp-build ( node walk -- image )
  over lp-fixed? if drop exit then
  over lp-binary? if lp-pair-build else drop lp-leaf-build then ;
: lp-walk ( -- walk )
  lp-state lp-dw ['] lp-build over dw-build ! ['] lp-pending over dw-pending !
  lf-term-base lf-term-count @ + over dw-size ! ;
: lf-meta-instantiate-level-params ( term names levels n -- term' outcome )
  dup lp-count-ok? 0= if 2drop 2drop -1 outcome-invalid exit then lp-set
  dup lf-term-root? if lp-walk dw-run else drop -1 outcome-invalid then ;

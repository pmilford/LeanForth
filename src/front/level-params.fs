\ Universe-parameter instantiation of the front end (plan FE1c; ADR 0021
\ D6), ports of Lean 4.35.0's Level.instantiateParams (Lean/Level.lean:
\ substParams with getParamSubst) and Expr.instantiateLevelParams
\ (Lean/Util/InstantiateLevelParams.lean), which put a constant's
\ universe arguments into its type or value (delta, inferType).
\ - lf-meta-level-params ( level names levels n -- level' outcome ): the
\   parameter names[i] becomes levels[i] (the first equal name, as
\   getParamSubst), for n names and levels in cells at the two addresses.
\   A level without parameters is kept, so is one whose parameter is not
\   named; a successor whose part changes is a new successor; a max or
\   imax over a parameter is rebuilt as Lean's updateMax! and updateIMax!
\   do: with mkLevelMax' or mkLevelIMax' when a part changes, else
\   simplified by simpLevelMax' or simpLevelIMax' (level-simp.fs).
\ - lf-meta-instantiate-level-params ( term names levels n -- term'
\   outcome ): every Sort's level and every constant's universe arguments
\   in term, as above; a node whose data word shows no parameter (Lean's
\   hasLevelParam test) is kept, so is a node whose parts do not change;
\   a constant gets a new reference with its levels' images (level-map.fs,
\   shared with mvars.fs's instantiation), a binder keeps its name and kind;
\   with n = 0 the term is returned as it is, as Lean does for empty lists.
\ Both walks are dag-walk.fs's, one over levels and one over terms (a
\ memo per node, heap stacks: no depth needs the host's stacks, plan task
\ 6.2.0); the level walk runs inside the term walk's builds.
\ Outcomes: ok; invalid for a negative count or a term or level not in
\ the store; full when a store or the heap has no room. Untrusted
\ front-end code.
\ Words: lf-meta-level-params, lf-meta-instantiate-level-params.
\ State: the record lp-state (the substitution and the walks), a member of
\ the checker context (ADR 0009).

require ../lib/lib.fs
require ../core/terms.fs
require ../core/levels.fs
require ../core/generation-handles.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/tagged-sort-boundary.fs
require ../present/binder-table.fs
require ./dag-walk.fs
require ./level-simp.fs
require ./level-map.fs

begin-structure /lp
  field: lp-names-at     \ address of the parameter names' cells
  field: lp-levels-at    \ address of their levels' cells
  field: lp-n            \ how many
  /dw +field lp-dw       \ the term walk
  /dw +field lp-ldw      \ the level walk
end-structure
/lp context-record: lp-state

\ The substitution: Lean's getParamSubst, the first equal name.
: lp-count ( -- n ) lp-state lp-n @ ;
: lp-name ( i -- name ) cells lp-state lp-names-at @ + @ ;
: lp-arg ( i -- level ) cells lp-state lp-levels-at @ + @ ;
: lp-index ( name -- i true | false )
  lp-count 0 ?do dup i lp-name = if drop i true unloop exit then loop drop false ;
: lp-set ( names levels n -- ) lp-state tuck lp-n ! tuck lp-levels-at ! lp-names-at ! ;

\ Levels: Lean's substParams. A level's parts are visited when it holds
\ a parameter (hasParam); a named parameter is its level.
: lp-undone ( child walk -- child true | false )
  over swap dw-done? if drop false else true then ;
: lp-arity ( level -- n )
  dup ls-succ? if drop 1 else ls-tag lf-level-binary-tag? 2 and then ;
: lp-second-pending ( node walk n -- child true | false )
  1 = if 2drop false else swap lf-level-second@ swap lp-undone then ;
: lp-open-arity ( level -- n ) dup lf-level-params? swap lp-arity and ;
: lp-l-pending ( node walk -- child true | false )
  over lp-open-arity ?dup 0= if 2drop false exit then
  >r over lf-level-first@ over lp-undone if nip nip r> drop true exit then
  r> lp-second-pending ;
: lp-lrefuse ( outcome -- ) lp-state lp-ldw dw-refuse ;
: lp-l-result ( w outcome -- w ) dup ok? if drop else lp-lrefuse then ;
: lp-l-images ( node walk -- i1 i2 )
  over lf-level-first@ over dw-image -rot swap lf-level-second@ swap dw-image ;
: lp-l-same? ( i1 i2 node -- i1 i2 flag )
  >r 2dup r@ lf-level-second@ = swap r> lf-level-first@ = and ;
: lp-l-parts ( node walk -- i1 i2 node kept? ) over >r lp-l-images r@ lp-l-same? r> swap ;
: lp-l-max ( node walk -- image )
  lp-l-parts if lm-simp-max else drop lf-meta-max then lp-l-result ;
: lp-l-imax ( node walk -- image )
  lp-l-parts if lm-simp-imax else drop lf-meta-imax then lp-l-result ;
: lp-l-succ ( node walk -- image )
  over lf-level-first@ swap dw-image 2dup swap lf-level-first@ = if drop exit then
  nip lf-level-succ lm-made lp-l-result ;
: lp-mapped ( param -- level true | false )
  lf-level-first@ lp-index if lp-arg true else false then ;
: lp-l-param ( node -- image ) dup lp-mapped if nip then ;
: lp-l-build ( node walk -- image )
  over lf-level-params? 0= if drop exit then
  over ls-tag case lf-level-tag-param of drop lp-l-param endof
    lf-level-tag-succ of lp-l-succ endof  lf-level-tag-max of lp-l-max endof
    lf-level-tag-imax of lp-l-imax endof  >r drop r> endcase ;
: lp-lwalk ( -- walk )
  lp-state lp-ldw ['] lp-l-build over dw-build ! ['] lp-l-pending over dw-pending !
  lf-level-count @ over dw-size ! ;
: lp-level ( level -- level' outcome )
  dup lf-level-params? if lp-lwalk dw-run else outcome-ok then ;
: lp-count-ok? ( n -- flag ) 0< 0= ;
: lf-meta-level-params ( level names levels n -- level' outcome )
  dup lp-count-ok? 0= if 2drop 2drop -1 outcome-invalid exit then lp-set
  dup lf-level-root? if lp-level else drop -1 outcome-invalid then ;

\ The term walk: a node's children are its parts, unless its data word
\ shows no parameter.
: lp-refuse ( outcome -- ) lp-state lp-dw dw-refuse ;
: lp-binary? ( node -- flag ) lf-term-tag@ lf-term-binary-tag? ;
: lp-fixed? ( node -- flag ) lf-term-data@ if lf-data-params? 0= else false then ;
: lp-parts-pending ( node walk -- child true | false )
  over lf-term-first@ over lp-undone if nip nip true exit then
  swap lf-term-second@ swap lp-undone ;
: lp-pending ( node walk -- child true | false )
  over dup lp-fixed? swap lp-binary? 0= or if 2drop false else lp-parts-pending then ;

\ Images of a binary node: rebuilt, with its binder's name, when a part
\ changes.
: lp-images ( node walk -- i1 i2 )
  over lf-term-first@ over dw-image -rot swap lf-term-second@ swap dw-image ;
: lp-same? ( i1 i2 node -- i1 i2 flag )
  >r 2dup r@ lf-term-second@ = swap r> lf-term-first@ = and ;
: lp-named ( new old -- new ) lf-pres-binder@ if 2>r dup 2r> lf-pres-binder! drop then ;
: lp-rebuild ( i1 i2 node -- image )
  dup >r lf-term-tag@ lf-term-binary if r> lp-named exit then
  r> drop outcome-full lp-refuse -1 ;
: lp-parts ( node walk -- i1 i2 node kept? ) over >r lp-images r@ lp-same? r> swap ;
: lp-pair-build ( node walk -- image ) lp-parts if nip nip else lp-rebuild then ;

\ A Sort's level and a constant's universe arguments get their images
\ (level-map.fs rebuilds the node when one changes).
: lp-image ( level -- level' ) lp-level dup ok? if drop else lp-refuse then ;
: lp-remapped ( image outcome -- image ) dup ok? if drop else lp-refuse then ;
: lp-sort-build ( node -- image ) ['] lp-image lf-meta-sort-remap lp-remapped ;
: lp-const-build ( node -- image ) ['] lp-image lf-meta-const-remap lp-remapped ;

: lp-leaf-build ( node -- image )
  dup lf-term-tag@ case lf-tag-symbolic-sort of lp-sort-build endof
    lf-tag-constant of lp-const-build endof endcase ;
: lp-build ( node walk -- image )
  over lp-fixed? if drop exit then
  over lp-binary? if lp-pair-build else drop lp-leaf-build then ;
: lp-walk ( -- walk )
  lp-state lp-dw ['] lp-build over dw-build ! ['] lp-pending over dw-pending !
  lf-term-base lf-term-count @ + over dw-size ! ;
\ No names: the term as it is (Lean's test of empty lists; the Level
\ version has none and simplifies even then).
: lp-run ( term -- term' outcome ) lp-count if lp-walk dw-run else outcome-ok then ;
: lf-meta-instantiate-level-params ( term names levels n -- term' outcome )
  dup lp-count-ok? 0= if 2drop 2drop -1 outcome-invalid exit then lp-set
  dup lf-term-root? if lp-run else drop -1 outcome-invalid then ;

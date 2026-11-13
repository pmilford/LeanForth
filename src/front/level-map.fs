\ Rebuilding a Sort or a constant over new universe levels, shared by the
\ front end's term walks (plan FE1c; review of fe1c, Q5): mvars.fs's
\ instantiateMVars and level-params.fs's instantiateLevelParams, which
\ update a Sort's level and a constant's universe arguments as Lean's
\ Expr.updateSort! and updateConst! do.
\ - lf-meta-sort-remap ( node xt -- image outcome ): node is a Sort and
\   xt ( level -- level' ) gives the image of its level: the same node
\   when that is the same level, else a new Sort.
\ - lf-meta-const-remap ( node xt -- image outcome ): node is a constant:
\   the same node when no universe argument's image differs, else a
\   reference to the same name with each argument's image, built in a
\   heap block of (level, identity) pairs freed at once
\   (core/constant-references.fs).
\ xt reports its own failures (it refuses its own walk) and its image is
\ used as it is. Outcomes: ok; full when the term or reference store or
\ the heap has no room, the image then -1. Untrusted front-end code.
\ Words: lf-meta-sort-remap, lf-meta-const-remap.
\ State: the record lmap (xt, and the pairs block while a constant is
\ rebuilt), a member of the checker context (ADR 0009); one rebuild at a
\ time (no xt rebuilds a term).

require ../lib/lib.fs
require ../core/terms.fs
require ../core/levels.fs
require ../core/generation-handles.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/tagged-sort-boundary.fs

begin-structure /lmap
  field: lmap-xt        \ the level image ( level -- level' )
  field: lmap-pairs     \ heap, while a constant is rebuilt: its level pairs
end-structure
/lmap context-record: lmap

: lmap-image ( level -- level' ) lmap lmap-xt @ execute ;
\ A level's identity, or 0 for no level (lf-hterm-sort and lf-cref-new
\ then refuse it).
: lmap-identity ( level -- identity ) lf-level-identity 0= if 0 then ;
: lmap-sort-new ( level -- image outcome )
  dup lmap-identity lf-hterm-sort if drop outcome-ok else -1 outcome-full then ;
: lf-meta-sort-remap ( node xt -- image outcome )
  lmap lmap-xt ! dup lf-term-first@ dup lmap-image tuck =
  if drop outcome-ok else nip lmap-sort-new then ;

: lmap-cref ( term -- slot ) lf-term-first@ lf-cref-slot ;
: lmap-moves? ( flag addr i -- flag' ) lf-cref-pair@ drop dup lmap-image <> or ;
: lmap-moved? ( term -- flag )
  lmap-cref lf-cref-pairs false swap 0 ?do over i lmap-moves? loop nip ;
: lmap-at ( i -- addr ) 2* cells lmap lmap-pairs @ + ;
: lmap-pair! ( level addr -- ) >r dup lmap-identity swap r> 2! ;
: lmap-fill ( addr count -- )
  0 ?do dup i lf-cref-pair@ drop lmap-image i lmap-at lmap-pair! loop drop ;
: lmap-block ( count -- flag )
  2* cells 1 max allocate if drop false exit then lmap lmap-pairs ! true ;
: lmap-ref-new ( slot -- term true | false )
  dup lf-cref-name@ rot lf-cref-pairs nip lmap lmap-pairs @ swap lf-cref-new
  if lf-cterm-new if drop true exit then then false ;
: lmap-const-new ( node -- image outcome )
  dup lmap-cref lf-cref-pairs dup lmap-block 0= if 2drop drop -1 outcome-full exit then
  lmap-fill lmap-cref lmap-ref-new lmap lmap-pairs heap-release
  if outcome-ok else -1 outcome-full then ;
: lf-meta-const-remap ( node xt -- image outcome )
  lmap lmap-xt ! dup lmap-moved? if lmap-const-new else outcome-ok then ;

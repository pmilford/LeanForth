\ Untrusted, bounded constant-reference data, not a declaration environment.
\ Load names.fs, levels.fs and generation-handles.fs first. No type inference,
\ level scope check, declaration acceptance or theorem acceptance is performed.
\ Handles and generations are forgeable, instance-local diagnostics, not
\ capabilities or serialized data. Single-threaded; exclude raw mutation.
\ Input arrays must be aligned, readable and disjoint from this module's data.
\ Name handles are (index generation); levels are (index identity). Name table
\ reset invalidates names; its contract excludes rollback/raw mutation.

32 constant lf-cref-capacity
8 constant lf-cref-argument-capacity
\ Slot: identity, name index, name generation, argument count, level pairs.
4 lf-cref-argument-capacity 2 * + constant lf-cref-slot-cells
create lf-cref-storage lf-cref-capacity lf-cref-slot-cells * cells allot
variable lf-cref-count
variable lf-cref-serial
variable lf-cref-name
variable lf-cref-generation
variable lf-cref-input
variable lf-cref-length

: lf-cref-slot ( index -- addr ) lf-cref-slot-cells * cells lf-cref-storage + ;
: lf-cref-arg ( slot index -- addr ) 2 * 4 + cells + ;
: lf-cref-state-valid? ( -- flag )
  lf-cref-count @ dup 0< 0= swap lf-cref-capacity <= and
  lf-cref-serial @ 0< 0= and ;

\ Invalidate every reference. Allocation serial is deliberately not rewound.
: lf-cref-reset ( -- ) 0 lf-cref-count ! ;

\ A live name pair binds the index to the current name-table generation.
: lf-cref-name-valid? ( index generation -- flag )
  lf-name-generation @ = swap lf-name-valid? and lf-name-storage-valid? and ;

\ Validate the reference and all captured dependencies on every access.
: lf-cref-valid? ( index identity -- flag )
  lf-cref-state-valid? 0= if 2drop false exit then
  over dup 0< swap lf-cref-count @ >= or if 2drop false exit then
  swap lf-cref-slot swap over @ <> if drop false exit then
  dup cell+ @ over 2 cells + @ lf-cref-name-valid? 0= if drop false exit then
  dup 3 cells + @ dup 0< over lf-cref-argument-capacity > or if
    2drop false exit
  then
  0 ?do
    dup i lf-cref-arg dup @ swap cell+ @ lf-hlevel-valid? 0= if
      drop false unloop exit
    then
  loop drop true ;

\ Construct from name pair and an ordered array of level pairs. Empty arrays
\ are not dereferenced. Invalid handles, bounds or exhaustion return false;
\ no slot or serial is changed on failure. Caller supplies readable memory.
: lf-cref-new ( name generation addr count -- index identity true | false )
  lf-cref-length ! lf-cref-input ! lf-cref-generation ! lf-cref-name !
  lf-cref-state-valid? 0= if false exit then
  lf-cref-length @ dup 0< swap lf-cref-argument-capacity > or if false exit then
  lf-cref-name @ lf-cref-generation @ lf-cref-name-valid? 0= if false exit then
  lf-cref-count @ lf-cref-capacity >= lf-cref-serial @ -1 1 rshift = or if false exit then
  lf-cref-length @ 0 ?do
    lf-cref-input @ i 2 * cells + dup @ swap cell+ @ lf-hlevel-valid? 0= if
      false unloop exit
    then
  loop
  1 lf-cref-serial +!
  lf-cref-count @ lf-cref-slot >r
  lf-cref-serial @ r@ ! lf-cref-name @ r@ cell+ !
  lf-cref-generation @ r@ 2 cells + ! lf-cref-length @ r@ 3 cells + !
  lf-cref-length @ 0<> if
    lf-cref-input @ r@ 4 cells + lf-cref-length @ 2 * cells move
  then
  r> drop lf-cref-count @ 1 lf-cref-count +! lf-cref-serial @ true ;

\ Read name and number of ordered levels from a live reference.
: lf-cref-read ( index identity -- name generation count true | false )
  2dup lf-cref-valid? 0= if 2drop false exit then
  drop lf-cref-slot dup cell+ @ over 2 cells + @ rot 3 cells + @ true ;

\ Read a level pair by zero-based position; stale or out-of-range fails.
: lf-cref-level ( index identity position -- index identity true | false )
  >r 2dup lf-cref-valid? 0= if 2drop r> drop false exit then
  drop lf-cref-slot r> dup 0< if 2drop false exit then
  dup 2 pick 3 cells + @ >= if 2drop false exit then
  lf-cref-arg dup @ swap cell+ @ true ;

0 lf-cref-count ! 0 lf-cref-serial !

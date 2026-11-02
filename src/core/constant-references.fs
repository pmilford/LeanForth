\ Constant references: a constant's name plus an ordered list of universe
\ level arguments, as they appear in a term. Untrusted bounded data, not a
\ declaration environment. No type inference, level scope check,
\ declaration acceptance or theorem acceptance is performed. Requires
\ names.fs, levels.fs and generation-handles.fs.
\ A name is a pair (index generation); a level is a pair (index identity);
\ a reference is a pair (index identity). Every access revalidates the name
\ and all level pairs, so a reset of the name table or a rolled-back level
\ makes the reference stale. Handles are forgeable, instance-local
\ diagnostics, not capabilities. State: one bounded store of reference
\ records; single-threaded; callers exclude raw mutation, and input arrays
\ must be aligned, readable and disjoint from this module's data.

32 constant lf-cref-capacity
8 constant lf-cref-argument-capacity

\ One reference. The layout is relied on by kernel modules and tests that
\ address records by cell offset: identity, name, name generation, argument
\ count, then up to 8 (index identity) level pairs.
begin-structure /lf-ref
  field: lf-ref-identity
  field: lf-ref-name
  field: lf-ref-generation
  field: lf-ref-arity
  lf-cref-argument-capacity 2* cells +field lf-ref-levels
end-structure
/lf-ref 1 cells / constant lf-cref-slot-cells

lf-cref-capacity /lf-ref 0 store: lf-crefs

\ The store's fields under their established names (kernel modules roll
\ back lf-cref-count; tests corrupt the count and serial).
: lf-cref-count ( -- addr ) lf-crefs store-count ;
: lf-cref-serial ( -- addr ) lf-crefs store-serial ;
: lf-cref-storage ( -- addr ) lf-crefs store-records ;
\ Unchecked addresses: a record, and its level pair at a valid position.
: lf-cref-slot ( index -- addr ) lf-crefs store-slot ;
: lf-cref-arg ( slot position -- addr ) 2* cells swap lf-ref-levels + ;

\ A valid store also needs a nonnegative serial.
: lf-cref-state-valid? ( -- flag )
  lf-crefs store-count-valid? lf-cref-serial @ 0< 0= and ;
\ Invalidate every reference. The serial is deliberately not rewound.
: lf-cref-reset ( -- ) 0 lf-cref-count ! ;

\ A live name pair binds the index to the current name-table generation.
: lf-cref-name-valid? ( index generation -- flag )
  lf-name-generation @ = swap lf-name-valid? and lf-name-storage-valid? and ;
\ count level pairs at addr are all live; at most the argument capacity.
: lf-cref-arity? ( count -- flag ) lf-cref-argument-capacity upto? ;
: lf-cref-pair@ ( addr i -- index identity ) 2* cells + 2@ swap ;
: lf-cref-levels-valid? ( addr count -- flag )
  0 ?do dup i lf-cref-pair@ lf-hlevel-valid? 0= if drop false unloop exit then
  loop drop true ;
: lf-cref-input-ok? ( addr count -- flag )
  dup lf-cref-arity? if lf-cref-levels-valid? else 2drop false then ;

\ A reference is valid when the store is, the index is allocated, the
\ identity matches, and its name and every level pair are still live.
: lf-cref-index? ( index -- flag ) 0 lf-cref-count @ within lf-cref-state-valid? and ;
: lf-cref-name-ok? ( slot -- flag ) dup lf-ref-name @ swap lf-ref-generation @ lf-cref-name-valid? ;
: lf-cref-args-ok? ( slot -- flag ) dup lf-ref-levels swap lf-ref-arity @ lf-cref-input-ok? ;
: lf-cref-valid? ( index identity -- flag )
  over lf-cref-index? 0= if 2drop false exit then
  swap lf-cref-slot tuck lf-ref-identity @ <> if drop false exit then
  dup lf-cref-name-ok? if lf-cref-args-ok? else drop false then ;

\ Construct from a name pair and an array of count level pairs; an empty
\ array is not read. Invalid handles, bounds or exhaustion return false and
\ change nothing.
: lf-cref-levels! ( addr count slot -- ) 2dup lf-ref-arity ! lf-ref-levels swap 2* cells move ;
: lf-cref-name! ( name generation slot -- ) tuck lf-ref-generation ! lf-ref-name ! ;
: lf-cref-stamp ( slot -- identity ) lf-cref-serial @ tuck swap lf-ref-identity ! ;
\ Unchecked: the caller has validated the input and that the store is open.
: lf-cref-store ( name generation addr count -- index identity )
  lf-crefs store-new-slot drop >r >r r@ lf-cref-levels! r@ lf-cref-name!
  r> lf-cref-stamp r> swap ;
: lf-cref-new ( name generation addr count -- index identity true | false )
  2over lf-cref-name-valid? >r 2dup lf-cref-input-ok? r> and
  lf-cref-state-valid? and lf-crefs store-open? and
  if lf-cref-store true else 2drop 2drop false then ;

\ Name, generation and number of levels of a live reference.
: lf-cref-read ( index identity -- name generation count true | false )
  2dup lf-cref-valid? 0= if 2drop false exit then
  drop lf-cref-slot dup lf-ref-name @ over lf-ref-generation @ rot lf-ref-arity @ true ;

\ The level pairs of a live reference, validated once: their address and
\ count. The pairs stay valid only while nothing is reset or rolled back.
: lf-cref-levels ( index identity -- addr count true | false )
  2dup lf-cref-valid? 0= if 2drop false exit then
  drop lf-cref-slot dup lf-ref-levels swap lf-ref-arity @ true ;

\ Level pair at a zero-based position; stale or out-of-range fails.
: lf-cref-level ( index identity position -- index identity true | false )
  >r 2dup lf-cref-valid? 0= if 2drop r> drop false exit then
  drop lf-cref-slot r> 2dup swap lf-ref-arity @ 0 swap within
  if lf-cref-arg 2@ swap true else 2drop false then ;

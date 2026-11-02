\ Constant references: a constant's name plus an ordered list of universe
\ level arguments, as they appear in a term. Untrusted bounded data, not a
\ declaration environment. No type inference, level scope check,
\ declaration acceptance or theorem acceptance is performed. Requires
\ names.fs, levels.fs and generation-handles.fs.
\ A name is a pair (index generation); a level is a pair (index identity);
\ a reference is a pair (index identity). Every lookup revalidates the name
\ and all level pairs, so a reset of the name table or a rolled-back level
\ makes the reference stale. Handles are forgeable, instance-local
\ diagnostics, not capabilities. State: one bounded store of reference
\ records; single-threaded; callers exclude raw mutation, and input arrays
\ must be aligned, readable and disjoint from this module's data.

32 constant lf-cref-capacity
8 constant lf-cref-argument-capacity

\ One reference record. Kernel modules and tests still address records by
\ cell offset, so the layout is fixed for now: identity, name, name
\ generation, argument count, then up to 8 (index identity) level pairs.
begin-structure /lf-crec
  field: lf-crec-identity
  field: lf-crec-name
  field: lf-crec-generation
  field: lf-crec-arity
  lf-cref-argument-capacity 2* cells +field lf-crec-levels
end-structure
/lf-crec 1 cells / constant lf-cref-slot-cells

lf-cref-capacity /lf-crec 0 store: lf-crefs

\ The store's fields under their established names (kernel modules roll
\ back lf-cref-count; tests corrupt the count and serial).
: lf-cref-count ( -- addr ) lf-crefs store-count ;
: lf-cref-serial ( -- addr ) lf-crefs store-serial ;
: lf-cref-storage ( -- addr ) lf-crefs store-records ;

\ Unchecked access: a record, a level pair in an array, and a record's
\ name and level array.
: lf-cref-slot ( index -- slot ) lf-crefs store-slot ;
: lf-cref-pair ( addr i -- addr' ) 2* cells + ;
: lf-cref-pair@ ( addr i -- index identity ) lf-cref-pair 2@ swap ;
: lf-cref-arg ( slot position -- addr ) swap lf-crec-levels swap lf-cref-pair ;
: lf-cref-name@ ( slot -- name generation ) dup lf-crec-name @ swap lf-crec-generation @ ;
: lf-cref-pairs ( slot -- addr count ) dup lf-crec-levels swap lf-crec-arity @ ;

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
: lf-cref-levels-valid? ( addr count -- flag )
  0 ?do dup i lf-cref-pair@ lf-hlevel-valid? 0= if drop false unloop exit then
  loop drop true ;
: lf-cref-input-ok? ( addr count -- flag )
  dup lf-cref-arity? if lf-cref-levels-valid? else 2drop false then ;

\ A reference is valid when the store is, the index is allocated, the
\ identity matches, and its name and every level pair are still live.
: lf-cref-index? ( index -- flag ) 0 lf-cref-count @ within lf-cref-state-valid? and ;
: lf-cref-name-ok? ( slot -- flag ) lf-cref-name@ lf-cref-name-valid? ;
: lf-cref-args-ok? ( slot -- flag ) lf-cref-pairs lf-cref-input-ok? ;
: lf-cref-valid? ( index identity -- flag )
  over lf-cref-index? 0= if 2drop false exit then
  swap lf-cref-slot tuck lf-crec-identity @ <> if drop false exit then
  dup lf-cref-name-ok? if lf-cref-args-ok? else drop false then ;
: lf-cref-record ( index identity -- slot true | false )
  2dup lf-cref-valid? if drop lf-cref-slot true else 2drop false then ;

\ Construct from a name pair and an array of count level pairs. The array
\ is read only once the name and store are known good, and an empty array
\ is not read. Invalid handles, bounds or exhaustion return false and
\ change nothing.
: lf-cref-levels! ( addr count slot -- ) 2dup lf-crec-arity ! lf-crec-levels swap 2* cells move ;
: lf-cref-name! ( name generation slot -- ) tuck lf-crec-generation ! lf-crec-name ! ;
: lf-cref-stamp ( slot -- identity ) lf-cref-serial @ tuck swap lf-crec-identity ! ;
\ Unchecked input; refuses only when the store has no free record.
: lf-cref-store ( name generation addr count -- index identity true | false )
  lf-crefs store-new-slot 0= if 2drop 2drop false exit then
  >r >r r@ lf-cref-levels! r@ lf-cref-name! r> lf-cref-stamp r> swap true ;
: lf-cref-source? ( name generation -- flag ) lf-cref-name-valid? lf-cref-state-valid? and ;
: lf-cref-new ( name generation addr count -- index identity true | false )
  2over lf-cref-source? if 2dup lf-cref-input-ok? else false then
  if lf-cref-store else 2drop 2drop false then ;

\ Name, generation and number of levels of a live reference.
: lf-cref-read ( index identity -- name generation count true | false )
  lf-cref-record if dup lf-cref-name@ rot lf-crec-arity @ true else false then ;

\ The level pairs of a live reference, validated once: their address and
\ count. The address is read-only module data, valid until a reference,
\ level or name reset or rollback; never pass it back to lf-cref-new.
: lf-cref-levels ( index identity -- addr count true | false )
  lf-cref-record if lf-cref-pairs true else false then ;

\ Level pair at a zero-based position; stale or out-of-range fails.
: lf-cref-pair? ( addr count position -- index identity true | false )
  tuck 0 rot within if lf-cref-pair@ true else 2drop false then ;
: lf-cref-level ( index identity position -- index identity true | false )
  >r lf-cref-levels if r> lf-cref-pair? else r> drop false then ;

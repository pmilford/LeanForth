\ Constant references: a constant's name plus an ordered list of universe
\ level arguments, as they appear in a term. Untrusted bounded data, not a
\ declaration environment. No type inference, level scope check, declaration
\ acceptance or theorem acceptance is performed. A name is a pair (index
\ generation); a level is a pair (index identity); a reference is a pair
\ (index identity). Every lookup revalidates the name and all level pairs,
\ so a reset of the name table or a rolled-back level makes the reference
\ stale. Handles are forgeable, instance-local diagnostics, not
\ capabilities.
\ Universe arguments are variable-length (ADR 0016 C2, plan 6.2.0): a
\ record holds their number and the offset of its (index identity) pairs
\ in a pool, where each record's pairs follow the previous record's, so a
\ rollback of the records gives their pairs back too. At most
\ lf-cref-argument-capacity arguments per reference (Mathlib's largest
\ constant has 30); the records grow up to a capacity that is a setting
\ of each context, as for terms (terms.fs), starting at lf-cref-default.
\ State: the reference records, a heap store whose header lf-crefs is a
\ member of the checker context (lib/context.fs), and the pairs pool, a
\ heap slab whose record lf-cref-pool is another; both are freed by their
\ teardown words. Single-threaded within one context; callers exclude raw
\ mutation, and input arrays must be aligned, readable and disjoint from
\ this module's data.

require ../lib/lib.fs
require ../lib/slab.fs
require ./diagnostics.fs
require ./generation-handles.fs
require ./names.fs

32 constant lf-cref-default
64 constant lf-cref-argument-capacity

\ One reference record. Tests still address records by cell offset, so the
\ layout is fixed: identity, name, name generation, argument count, then
\ the offset of its pairs in the pool, in pairs.
begin-structure /lf-crec
  field: lf-crec-identity
  field: lf-crec-name
  field: lf-crec-generation
  field: lf-crec-arity
  field: lf-crec-offset
end-structure
/lf-crec 1 cells / constant lf-cref-slot-cells

store-header context-record: lf-crefs
: lf-crefs-make ( -- )
  lf-cref-default /lf-crec 0 lf-crefs store-heap-init ok? 0= abort" references: no heap" ;
' lf-crefs-make context-setup
:noname ( -- ) lf-crefs store-heap-free ; context-teardown
: lf-cref-capacity ( -- n ) lf-crefs store-limit @ ;
: lf-cref-capacity! ( n -- outcome ) lf-crefs store-limit! ;

\ The pairs pool: a slab of pairs, its count unused (the records say how
\ much is in use).
2 cells constant /lf-cref-pair
/slab context-record: lf-cref-pool
\ It starts with room for 8 pairs per record, the old fixed layout, so
\ references within that size never grow it; the test hook of lib/store.fs
\ is asked before that first reserve too.
: lf-cref-pool-made ( outcome -- ) ok? 0= abort" references: pool" ;
: lf-cref-pool-first ( -- outcome )
  lf-crefs store-grow-refused? if outcome-full exit then
  lf-cref-default 8 * lf-cref-pool column-reserve ;
: lf-cref-pool-make ( -- )
  /lf-cref-pair max-n /lf-cref-pair / lf-cref-pool slab-init lf-cref-pool-made
  lf-cref-pool-first lf-cref-pool-made ;
' lf-cref-pool-make context-setup
:noname ( -- ) lf-cref-pool slab-free ; context-teardown

\ The store's fields under their established names (kernel modules roll
\ back lf-cref-count; tests corrupt the count and serial).
: lf-cref-count ( -- addr ) lf-crefs store-count ;
: lf-cref-serial ( -- addr ) lf-crefs store-serial ;
: lf-cref-storage ( -- addr ) lf-crefs store-records ;

\ Unchecked access: a record, a level pair in an array, and a record's
\ name and level array (valid until the next reference is made).
: lf-cref-slot ( index -- slot ) lf-crefs store-slot ;
: lf-cref-pair ( addr i -- addr' ) 2* cells + ;
: lf-cref-pair@ ( addr i -- index identity ) lf-cref-pair 2@ swap ;
: lf-cref-name@ ( slot -- name generation ) dup lf-crec-name @ swap lf-crec-generation @ ;
: lf-cref-pairs ( slot -- addr count )
  dup lf-crec-offset @ lf-cref-pool slab-at swap lf-crec-arity @ ;

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
\ A record's pairs lie within the pool (a corrupted offset is refused
\ before anything is read).
: lf-cref-span? ( slot -- flag )
  dup lf-crec-offset @ swap lf-crec-arity @ over + 0 lf-cref-pool slab-capacity between?
  swap 0< 0= and ;
: lf-cref-args-ok? ( slot -- flag )
  dup lf-cref-span? if lf-cref-pairs lf-cref-input-ok? else drop false then ;
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
: lf-cref-levels! ( addr count offset slot -- )
  tuck lf-crec-offset ! 2dup lf-crec-arity ! lf-cref-pairs drop swap 2* cells move ;
: lf-cref-name! ( name generation slot -- ) tuck lf-crec-generation ! lf-crec-name ! ;
: lf-cref-stamp ( slot -- identity ) lf-cref-serial @ tuck swap lf-crec-identity ! ;
\ Unchecked input; refuses only when the store has no free record or its
\ serial is spent, or the pool has no room for the pairs (a top outside
\ the pool, from a corrupted record, too), which is recorded as a
\ diagnostic.
: lf-cref-site ( -- site ) c" constant-references lf-cref-new" ;
: lf-cref-refused ( -- false )
  lf-crefs lf-cref-site lf-diag-references-full lf-diag-store false ;
\ Where the next record's pairs start: after the last record's.
: lf-cref-end ( slot -- offset ) dup lf-crec-offset @ swap lf-crec-arity @ + ;
: lf-cref-top ( -- offset )
  lf-cref-count @ ?dup if 1- lf-cref-slot lf-cref-end else 0 then ;
: lf-cref-pool-refused ( -- false )
  lf-cref-top lf-cref-pool slab-capacity lf-cref-site lf-diag-references-full lf-diag-note
  false ;
\ Room in the pool up to end pairs (the test hook of lib/store.fs is asked
\ before it grows).
: lf-cref-pool-room ( end -- outcome )
  dup lf-cref-pool slab-capacity > 0= if drop outcome-ok exit then
  lf-crefs store-grow-refused? if drop outcome-full exit then
  lf-cref-pool column-reserve ;
: lf-cref-room? ( count -- offset true | false )
  lf-cref-top dup 0 lf-cref-pool slab-capacity between? 0= if 2drop false exit then
  tuck + lf-cref-pool-room ok? if true else drop false then ;
: lf-cref-store ( name generation addr count -- index identity true | false )
  dup lf-cref-room? 0= if 2drop 2drop lf-cref-pool-refused exit then
  lf-crefs store-ready drop
  lf-crefs store-new-slot 0= if drop 2drop 2drop lf-cref-refused exit then
  >r >r r@ lf-cref-levels! r@ lf-cref-name! r> lf-cref-stamp r> swap true ;
: lf-cref-source? ( name generation -- flag ) lf-cref-name-valid? lf-cref-state-valid? and ;
: lf-cref-new ( name generation addr count -- index identity true | false )
  2over lf-cref-source? if 2dup lf-cref-input-ok? else false then
  if lf-cref-store else 2drop 2drop false then ;

\ Name, generation and number of levels of a live reference.
: lf-cref-read ( index identity -- name generation count true | false )
  lf-cref-record if dup lf-cref-name@ rot lf-crec-arity @ true else false then ;

\ The level pairs of a live reference, validated once: their address and
\ count. The address is read-only module data in the pool, valid until a
\ reference, level or name reset or rollback, and until the next reference
\ is made (the pool may move); never pass it back to lf-cref-new.
: lf-cref-levels ( index identity -- addr count true | false )
  lf-cref-record if lf-cref-pairs true else false then ;

\ Level pair at a zero-based position; stale or out-of-range fails.
: lf-cref-pair? ( addr count position -- index identity true | false )
  tuck 0 rot within if lf-cref-pair@ true else 2drop false then ;
: lf-cref-level ( index identity position -- index identity true | false )
  >r lf-cref-levels if r> lf-cref-pair? else r> drop false then ;

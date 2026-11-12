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
\ rollback of the records gives their pairs back too. A reference may have
\ any number of arguments (plan task 6.2.0; Mathlib's largest constant has
\ 30): the pool grows, and one it cannot grow is full. lf-cref-argument-
\ capacity, 64, is no limit: only the number run records 0.1 report. The
\ records grow up to a capacity that is a setting
\ of each context, as for terms (terms.fs), starting at lf-cref-default.
\ Interning (ADR 0016 C2, C4; compact-store plan step S4): a reference is
\ a constant's name with its interned universe list, so lf-cref-new gives
\ back the live record with the same name, generation and level pairs
\ when there is one (found through a hash table of the context, a hash
\ only a hint, an entry equal only when its allocated record is, field by
\ field), else it makes one and enters it. With levels hash-consed
\ (levels.fs), equal constants are one reference, and their term nodes
\ one node (constant-term-boundary.fs). Interning follows the context's
\ switch for terms (lf-term-sharing?). A rollback (lf-cref-rollback, which
\ the joint scratch marks use) takes the given-back records' entries out
\ by Knuth's Algorithm R; a reset empties the table.
\ State: the reference records, a heap store whose header lf-crefs is a
\ member of the checker context (lib/context.fs), the pairs pool, a
\ heap slab whose record lf-cref-pool is another, and the interning table
\ lf-cref-table with its candidate lf-cref-key; all are freed by their
\ teardown words. A worker of a parallel check reads the input's
\ references of the context that fed them (lf-cref-under, copies of
\ headers that own nothing; shared input, ADR 0016 S8) and keeps only its
\ own. Single-threaded within one context; callers exclude raw
\ mutation, and input arrays must be aligned, readable and disjoint from
\ this module's data.

require ../lib/lib.fs
require ../lib/store-columns.fs
require ../lib/slab.fs
require ../lib/hash32.fs
require ../lib/htab.fs
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
\ the store back through scratch marks, core/scratch-marks.fs; tests
\ corrupt the count and serial).
: lf-cref-count ( -- addr ) lf-crefs store-count ;
: lf-cref-serial ( -- addr ) lf-crefs store-serial ;
: lf-cref-storage ( -- addr ) lf-crefs store-records ;

\ The source's references (shared input, ADR 0016 S8): a context made to
\ share another context's fed input (import/feed.fs's lf-feed-shared,
\ lf-cref-borrow below) reads that context's references, numbers below
\ lf-cref-base, in place through copies of its store's, pool's and
\ table's headers (the table's frozen, so a find there writes nothing),
\ and keeps in its own store only the references its checks make,
\ numbered from lf-cref-base on, their pairs in its own pool at offsets
\ from lf-cref-under-top on. Its own table holds only its own. So each
\ reference is found where a context holding the whole input finds it,
\ under the same number. The source must outlive this context and make no
\ reference while it reads; nothing of it is written or freed here. With
\ none (lf-cref-base 0, every context but such a worker) each word below
\ works as before.
begin-structure /lf-cunder
  store-header +field lf-cunder-store   \ the source's records, read in place
  /slab +field lf-cunder-pool           \ the source's pairs
  /htab +field lf-cunder-table          \ the source's table, frozen
  field: lf-cunder-base                 \ its references: numbers below are its
  field: lf-cunder-top                  \ the pairs they use
end-structure
/lf-cunder context-record: lf-cref-under
: lf-cref-base ( -- n ) lf-cref-under lf-cunder-base @ ;
: lf-cref-under-top ( -- n ) lf-cref-under lf-cunder-top @ ;
: lf-cref-under? ( index -- flag ) lf-cref-base u< ;

\ Unchecked access: a record, a level pair in an array, and a record's
\ name and level array (valid until the next reference is made).
: lf-cref-slot ( index -- slot )
  dup lf-cref-under? if lf-cref-under lf-cunder-store store-slot exit then
  lf-cref-base - lf-crefs store-slot ;
: lf-cref-pair ( addr i -- addr' ) 2* cells + ;
: lf-cref-pair@ ( addr i -- index identity ) lf-cref-pair 2@ swap ;
: lf-cref-name@ ( slot -- name generation ) dup lf-crec-name @ swap lf-crec-generation @ ;
: lf-cref-pool-at ( offset -- addr )
  dup lf-cref-under-top u< if lf-cref-under lf-cunder-pool slab-at exit then
  lf-cref-under-top - lf-cref-pool slab-at ;
: lf-cref-pairs ( slot -- addr count )
  dup lf-crec-offset @ lf-cref-pool-at swap lf-crec-arity @ ;
\ Whether index is an allocated reference: the source's below the base.
: lf-cref-at? ( index -- flag )
  dup lf-cref-under? if drop true else lf-cref-base - lf-crefs store-at? then ;
\ Every reference, the source's and this context's.
: lf-cref-total ( -- n ) lf-cref-count @ lf-cref-base + ;

\ A valid store also needs a nonnegative serial.
: lf-cref-state-valid? ( -- flag )
  lf-crefs store-count-valid? lf-cref-serial @ 0< 0= and ;

\ ---------------------------------------------------------------------------
\ The interning table (see the header). A record's hash: its name,
\ generation and arity, and its levels' indices; a record whose pairs lie
\ outside the pool (corrupted) hashes without them, a hint only.
/htab context-record: lf-cref-table
4 cells context-record: lf-cref-key   \ the reference sought: name generation addr count
\ The offsets of the pool an offset lies in: the source's pairs (below
\ lf-cref-under-top), or this context's pool after them.
: lf-cref-span-of ( offset -- lo hi )
  lf-cref-under-top tuck u< if 0 swap exit then dup lf-cref-pool slab-capacity + ;
\ lo <= offset and lo <= end <= hi.
: lf-cref-within? ( offset end lo hi -- flag )
  >r rot over < 0= -rot r> between? and ;
: lf-cref-span? ( slot -- flag )
  dup lf-crec-offset @ swap lf-crec-arity @ over + over lf-cref-span-of lf-cref-within? ;
: lf-cref-hash-levels ( h addr count -- h' )
  0 ?do dup i lf-cref-pair@ drop rot swap hash-step swap loop drop ;
: lf-cref-hash ( name generation addr count -- h )
  2swap swap hash-fmix swap hash-step over hash-step -rot lf-cref-hash-levels ;
: lf-cref-fields ( slot -- name generation addr count )
  dup lf-cref-name@ rot dup lf-cref-span? if lf-cref-pairs else drop 0 0 then ;
: lf-cref-rehash ( n htab -- h ) drop lf-cref-slot lf-cref-fields lf-cref-hash ;
\ Whether allocated record n has the name, generation, arity and level
\ pairs sought.
: lf-cref-head= ( slot key -- flag )
  2dup @ swap lf-crec-name @ = >r 2dup cell+ @ swap lf-crec-generation @ = r> and
  >r 3 cells + @ swap lf-crec-arity @ = r> and ;
: lf-cref-pairs= ( addr addr' count -- flag ) 2* cells tuck compare 0= ;
: lf-cref-same ( n key htab -- flag )
  drop over lf-cref-at? 0= if 2drop false exit then
  swap lf-cref-slot swap 2dup lf-cref-head= 0= if 2drop false exit then
  over lf-cref-span? 0= if 2drop false exit then
  swap lf-cref-pairs rot 2 cells + @ swap lf-cref-pairs= ;
create lf-cref-hooks /htab-hooks allot
' lf-cref-rehash ' lf-cref-same lf-cref-hooks htab-hooks!
: lf-cref-table-make ( -- ) 4 lf-cref-hooks lf-cref-table htab-init drop ;
' lf-cref-table-make context-setup
:noname ( -- ) lf-cref-table htab-free ; context-teardown
1024 constant lf-cref-table-small
: lf-cref-table-empty ( -- )
  lf-cref-table dup htab-live? if dup htab-slots lf-cref-table-small <= else false then
  if htab-clear else htab-free lf-cref-table-make then ;
: lf-cref-key! ( name generation addr count -- )
  lf-cref-key 3 cells + ! lf-cref-key 2 cells + ! lf-cref-key cell+ ! lf-cref-key ! ;
: lf-cref-sought ( name generation addr count htab -- n true | i false )
  >r 2over 2over lf-cref-hash >r lf-cref-key! lf-cref-key r> r> htab-find ;
: lf-cref-find ( name generation addr count -- n true | i false )
  lf-cref-table lf-cref-sought ;
\ The source's reference equal to the one sought, if this context reads
\ one (see lf-cref-under above).
: lf-cref-under-find ( name generation addr count -- n true | false )
  lf-cref-base 0= if 2drop 2drop false exit then
  lf-cref-under lf-cunder-table lf-cref-sought dup 0= if nip then ;
\ Take record index out of the table, if it is there, and every record
\ from count up to the store's count (counts of this context's store).
: lf-cref-forget ( index -- )
  dup lf-cref-slot lf-cref-fields lf-cref-hash lf-cref-table htab-remove drop ;
: lf-cref-unlist ( count -- )
  lf-cref-table htab-live? 0= if drop exit then
  lf-cref-total swap lf-cref-base + ?do i lf-cref-forget loop ;

\ Invalidate every reference and advance the store's generation, as a
\ term or level reset does (saturating to poisoned, lib/store.fs), so
\ whatever was derived from the old references sees the reset (the audit
\ memo, constant-term-boundary.fs). The serial is deliberately not rewound.
\ The interning table is emptied, and the source's references, if this
\ context read them, are no longer read.
: lf-cref-unborrow ( -- ) lf-cref-under /lf-cunder erase ;
: lf-cref-reset ( -- )
  lf-cref-unborrow 0 lf-cref-count ! lf-crefs store-epoch+ lf-cref-table-empty ;
\ Roll the store back to a mark of it (lib/store.fs's store-mark): ok,
\ the records made since and their table entries given back; or invalid
\ with nothing changed for a mark that store-rollback refuses.
: lf-cref-rollback ( mark -- outcome )
  dup lf-crefs store-mark-valid? if dup mark-count @ lf-cref-unlist then
  lf-crefs store-rollback ;

\ A live name pair binds the index to the current name-table generation.
: lf-cref-name-valid? ( index generation -- flag )
  lf-name-generation @ = swap lf-name-valid? and lf-name-storage-valid? and ;
\ count level pairs at addr are all live; count is not negative.
: lf-cref-arity? ( count -- flag ) 0< 0= ;
: lf-cref-levels-valid? ( addr count -- flag )
  0 ?do dup i lf-cref-pair@ lf-hlevel-valid? 0= if drop false unloop exit then
  loop drop true ;
: lf-cref-input-ok? ( addr count -- flag )
  dup lf-cref-arity? if lf-cref-levels-valid? else 2drop false then ;

\ A reference is valid when the store is, the index is allocated, the
\ identity matches, and its name and every level pair are still live.
: lf-cref-index? ( index -- flag ) 0 lf-cref-total within lf-cref-state-valid? and ;
: lf-cref-name-ok? ( slot -- flag ) lf-cref-name@ lf-cref-name-valid? ;
\ A record's pairs lie within the pool (lf-cref-span?, above: a corrupted
\ offset is refused before anything is read).
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
  lf-cref-count @ ?dup if 1- lf-cref-base + lf-cref-slot lf-cref-end
  else lf-cref-under-top then ;
: lf-cref-pool-refused ( -- false )
  lf-cref-top lf-cref-pool slab-capacity lf-cref-site lf-diag-references-full lf-diag-note
  false ;
\ Room in this context's pool up to offset end (the test hook of
\ lib/store.fs is asked before it grows).
: lf-cref-pool-room ( end -- outcome )
  lf-cref-under-top - dup lf-cref-pool slab-capacity > 0= if drop outcome-ok exit then
  lf-crefs store-grow-refused? if drop outcome-full exit then
  lf-cref-pool column-reserve ;
: lf-cref-room? ( count -- offset true | false )
  lf-cref-top dup lf-cref-under-top dup lf-cref-pool slab-capacity + between?
  0= if 2drop false exit then
  tuck + lf-cref-pool-room ok? if true else drop false then ;
\ A new record of this context's store: its number counts the source's.
: lf-cref-store ( name generation addr count -- index identity true | false )
  dup lf-cref-room? 0= if 2drop 2drop lf-cref-pool-refused exit then
  lf-crefs store-ready drop
  lf-crefs store-new-slot 0= if drop 2drop 2drop lf-cref-refused exit then
  >r >r r@ lf-cref-levels! r@ lf-cref-name! r> lf-cref-stamp r> lf-cref-base + swap true ;
: lf-cref-source? ( name generation -- flag ) lf-cref-name-valid? lf-cref-state-valid? and ;
\ Interned (see the header): the equal live record, given only where a
\ new record would be allowed (store-open? after growth, as for terms),
\ or a new record entered at the empty slot the find gave. A table that
\ cannot grow only costs sharing.
: lf-cref-found ( n -- index identity true | false )
  lf-crefs store-ready drop lf-crefs store-open?
  if dup lf-cref-slot lf-crec-identity @ true else drop lf-cref-refused then ;
: lf-cref-enter ( index identity true i | false i -- index identity true | false )
  swap if >r over r> lf-cref-table htab-put true else drop false then ;
: lf-cref-intern ( name generation addr count -- index identity true | false )
  lf-cref-table htab-ready ok? 0= if lf-cref-store exit then
  2over 2over lf-cref-under-find if >r 2drop 2drop r> lf-cref-found exit then
  2over 2over lf-cref-find if >r 2drop 2drop r> lf-cref-found exit then
  >r lf-cref-store r> lf-cref-enter ;
: lf-cref-make ( name generation addr count -- index identity true | false )
  lf-term-sharing? if lf-cref-intern else lf-cref-store then ;
: lf-cref-new ( name generation addr count -- index identity true | false )
  2over lf-cref-source? if 2dup lf-cref-input-ok? else false then
  if lf-cref-make else 2drop 2drop false then ;

\ The identity of the record at an index, or 0 when the index is not
\ allocated (identities start at 1). A constant node holds only its
\ reference's index (constant-term-boundary.fs; compact-store plan step
\ S4): readers of an audited node take the record's identity here.
: lf-cref-current ( index -- identity )
  dup lf-cref-at? if lf-cref-slot lf-crec-identity @ else drop 0 then ;

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

\ Read the references of the source context (see lf-cref-under above),
\ made by its feed: copies of its headers, the table's frozen, and this
\ context's serial raised to the source's, so that no identity repeats
\ across the two. ok; invalid, nothing changed, when this context made a
\ reference since its reset or reads a source already, or the source is
\ this context or reads one itself.
: lf-cref-under-end ( -- offset )
  lf-cref-base ?dup if 1- lf-cref-slot lf-cref-end else 0 then ;
: lf-cref-copy ( source -- )
  >r lf-crefs r@ lf-member-in lf-cref-under lf-cunder-store store-header move
  lf-cref-pool r@ lf-member-in lf-cref-under lf-cunder-pool /slab move
  lf-cref-table r@ lf-member-in lf-cref-under lf-cunder-table /htab move
  lf-cref-under lf-cunder-table htab-freeze
  lf-cref-serial r> lf-member-in @ lf-cref-serial @ max lf-cref-serial !
  lf-cref-under lf-cunder-store store-count @ lf-cref-under lf-cunder-base !
  lf-cref-under-end lf-cref-under lf-cunder-top ! ;
: lf-cref-lendable? ( source -- flag )
  dup lf-context @ <> swap lf-cref-under swap lf-member-in lf-cunder-base @ 0= and
  lf-cref-count @ 0= and lf-cref-base 0= and ;
: lf-cref-borrow ( source -- outcome )
  dup lf-cref-lendable? if lf-cref-copy outcome-ok else drop outcome-invalid then ;

\ What a worker reading this context's references depends on: the
\ addresses of its store's records and pool and the size of its table
\ (a table grows only into a new block) and the count. When a pass makes
\ references here after workers began to read (cli/check-run.fs: the
\ import pass of a run against a snapshot), they may have moved, and the
\ workers must be made again before they read.
4 constant lf-cref-lent#
: lf-cref-lending ( -- records pool slots count )
  lf-crefs store-records 0 lf-cref-pool slab-at lf-cref-table htab-slots lf-cref-count @ ;

\ The input's references for its fingerprint (core/input.fs): the
\ source's store and count when this context reads one, else the count
\ and store given (this context's, below its input mark); and the pairs
\ they use, from the start of their pool.
: lf-cref-input-of ( count store -- count' store' )
  lf-cref-base if 2drop lf-cref-base lf-cref-under lf-cunder-store then ;
: lf-cref-input-pairs ( -- addr n )
  lf-cref-base if 0 lf-cref-under lf-cunder-pool slab-at lf-cref-under-top
  else 0 lf-cref-pool slab-at lf-cref-top then ;

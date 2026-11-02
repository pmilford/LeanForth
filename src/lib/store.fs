\ Bounded record stores: the shared storage pattern of the term, level and
\ name tables. A store holds up to capacity records of width address units,
\ an allocation count, a reset generation, and for each record an identity
\ that never repeats. Requires: portability.fs, bounds.fs.
\
\ The checked words (store-count-valid?, store-valid?, store-new and those
\ built on it, store-identity@) validate before forming any address: the
\ shape is sound and sealed, base <= count <= capacity, and generation >= 0.
\ Words marked "unchecked" trust their caller. Base is the number of
\ permanent records a reset keeps (0, or 1 for a table with a fixed record
\ 0); a base-1 store is invalid until its first store-clear. A negative
\ generation means the store is poisoned, because its generation or its
\ identity serial ran out; every check then fails until the program
\ restarts. Identities come from a serial that only grows and never wraps;
\ a reset does not rewind it.
\
\ The shape (capacity, width, base) is fixed and checked when the store is
\ defined, and sealed: corrupting any one shape field breaks the seal, and
\ every check then fails.
\
\ Untrusted. One store is single-threaded: callers must not change it
\ during a call. Separate stores are independent. The layout (header,
\ capacity identity cells, then the records) is host-specific and must
\ never be serialized directly.

begin-structure store-header
  field: store-capacity     \ maximum number of records
  field: store-width        \ address units per record, positive and aligned
  field: store-base         \ records a reset keeps
  field: store-seal         \ check value of the three shape fields
  field: store-count        \ records allocated
  field: store-generation   \ reset epoch; negative when poisoned
  field: store-serial       \ last identity issued
end-structure

: store-identities ( store -- addr ) store-header + ;
: store-records ( store -- addr ) dup store-identities swap store-capacity @ cells + ;
\ Unchecked: addresses for an already validated index.
: store-slot ( index store -- addr ) tuck store-width @ * swap store-records + ;
: store-identity ( index store -- addr ) store-identities swap cells + ;

\ Shape and seal.
: store-shape@ ( store -- capacity width base )
  dup store-capacity @ over store-width @ rot store-base @ ;
: >store-seal ( capacity width base -- x ) xor xor invert ;
: store-width? ( width -- flag ) dup 0> swap dup aligned = and ;
: store-sealed? ( store -- flag ) dup store-shape@ >store-seal swap store-seal @ = ;
: store-shape? ( store -- flag )
  dup store-base @ over store-capacity @ upto? over store-width @ store-width? and
  swap store-sealed? and ;

\ Defining word: name ( -- store ), with zeroed counters and records. A bad
\ shape (negative capacity, base above capacity, width not a positive
\ aligned size) aborts the definition.
: store-zeroed, ( u -- addr ) here swap dup allot over swap erase ;
: store-bytes ( store -- u ) dup store-capacity @ swap store-width @ cell+ * ;
: store-shape! ( capacity width base store -- )
  >r r@ store-base ! r@ store-width ! r> store-capacity ! ;
: store-seal! ( store -- ) dup store-shape@ >store-seal swap store-seal ! ;
: store: ( capacity width base "name" -- )
  create store-header store-zeroed, >r r@ store-shape! r@ store-seal!
  r@ store-shape? 0= abort" store: bad shape" r> store-bytes store-zeroed, drop ;

\ Validity checks; none of them reads a record.
: store-live? ( store -- flag ) dup store-generation @ 0< 0= swap store-shape? and ;
: store-bounds ( store -- base capacity ) dup store-base @ swap store-capacity @ ;
: store-count-valid? ( store -- flag )
  dup store-live? swap dup store-count @ swap store-bounds between? and ;
: store-valid? ( index store -- flag )
  dup store-count-valid? if store-count @ 0 swap within else 2drop false then ;
: store-pair-valid? ( left right store -- flag ) tuck store-valid? >r store-valid? r> and ;

\ Allocation. store-new fails, changing nothing, on an invalid store, a full
\ store or a spent serial.
: store-room? ( store -- flag ) dup store-count @ swap store-capacity @ < ;
: store-spent? ( store -- flag ) store-serial @ max-n = ;
: store-open? ( store -- flag )
  dup store-count-valid? over store-room? and swap store-spent? 0= and ;
\ Unchecked: the caller has established store-open?. The count advances
\ before the caller writes the record, so a failure between the two must
\ roll the count back.
: store-serial+ ( store -- serial ) store-serial 1 over +! @ ;
: store-stamp ( store -- ) dup store-serial+ over store-count @ rot store-identity ! ;
: store-claim ( store -- index ) dup store-stamp dup store-count @ 1 rot store-count +! ;
: store-new ( store -- index true | false ) dup store-open? if store-claim true else drop false then ;
: store-new-slot ( store -- addr index true | false )
  dup store-new if tuck swap store-slot swap true else drop false then ;
: store-identity@ ( index store -- identity true | false )
  2dup store-valid? if store-identity @ true else 2drop false then ;

\ Reset. The generation grows by one per reset, saturates to -1 (poisoned)
\ instead of wrapping, and once negative stays unchanged.
: epoch+ ( generation -- generation' ) dup 0< if exit then dup max-n = if drop -1 else 1+ then ;
: store-epoch+ ( store -- ) store-generation dup @ epoch+ swap ! ;
: store-clear ( store -- ) dup store-base @ over store-count ! store-epoch+ ;
: store-poison ( store -- ) 0 over store-count ! -1 swap store-generation ! ;

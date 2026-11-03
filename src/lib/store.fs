\ Bounded record stores: the shared storage pattern of the term, level and
\ name tables. A store holds up to capacity records of width address units,
\ an allocation count, a reset generation, and for each record an identity
\ that never repeats.
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
\ made, and sealed: corrupting any one shape field breaks the seal, and
\ every check then fails. A store is made in the dictionary by store:, or
\ at run time in store-size bytes of memory the caller provides (from
\ ALLOCATE or inside a larger record) by store-init; both give the same
\ layout and behaviour.
\
\ Untrusted. One store is single-threaded: callers must not change it
\ during a call. Separate stores are independent. The layout (header,
\ capacity identity cells, then the records) is host-specific and must
\ never be serialized directly.

require ./bounds.fs
require ./outcome.fs
require ./portability.fs

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

\ Planning a store: its size in address units, and whether a shape is
\ sound. A sound shape has 0 <= base <= capacity, a positive aligned width,
\ and a size that fits in a cell. store-size of an unsound shape means
\ nothing.
: store-size ( capacity width -- u ) cell+ * store-header + ;
\ Unchecked: width is positive.
: store-fits? ( capacity width -- flag ) cell+ max-n store-header - swap / upto? ;
: store-plan? ( capacity width base -- flag )
  over store-width? 0= if drop 2drop false exit then
  >r 2dup store-fits? -rot drop r> swap upto? and ;

\ Making a store. store-init formats store-size bytes at store as an empty
\ store, or for an unsound shape gives false and writes nothing; a base-1
\ store is still invalid until its first store-clear. store: defines
\ name ( -- store ) in the dictionary and aborts on an unsound shape.
: store-zeroed, ( u -- addr ) here swap dup allot over swap erase ;
: store-bytes ( store -- u ) dup store-capacity @ swap store-width @ cell+ * ;
: store-shape! ( capacity width base store -- )
  >r r@ store-base ! r@ store-width ! r> store-capacity ! ;
: store-seal! ( store -- ) dup store-shape@ >store-seal swap store-seal ! ;
\ Unchecked: the shape fields are set; zero everything after them.
: store-end ( store -- addr ) dup store-shape@ drop store-size + ;
: store-zero ( store -- ) dup store-end swap store-count tuck - erase ;
: store-format ( capacity width base store -- )
  dup >r store-shape! r@ store-seal! r> store-zero ;
: store-init ( capacity width base store -- flag )
  >r 2>r dup 2r@ store-plan? 2r> rot
  if r> store-format true else 2drop drop r> drop false then ;
: store-allot ( capacity width -- addr ) store-size here swap allot ;
: store: ( capacity width base "name" -- )
  >r 2dup r@ store-plan? 0= abort" store: bad shape"
  create 2dup store-allot r> swap store-init drop ;

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

\ Marks (plan task 1.1.3). store-mark records where a store's allocation
\ stands, in a /store-mark record the caller provides; store-rollback
\ later gives back every record allocated since, by restoring the count.
\ Identities and the serial are never rewound. A rollback is refused,
\ with invalid and nothing changed, for a mark of another store, from
\ another generation (a reset since), above the current count, or whose
\ records have been rolled back and allocated again since (a rollback to
\ an earlier mark went below it): records below a mark's count must be
\ older than the mark, and the record at its count newer. Within one
\ generation identities grow with the index, so two identities show it.
\ A mark of an invalid store names no store and is always refused. Marks
\ are not capabilities: a forged record that passes these checks is
\ accepted. Like the store, a mark is host-specific memory.
begin-structure /store-mark
  field: mark-store         \ the store marked; 0 when marking failed
  field: mark-generation    \ its generation then
  field: mark-serial        \ its identity serial then
  field: mark-count         \ its count then
end-structure

: mark-set ( store mark -- )
  2dup mark-store ! over store-generation @ over mark-generation !
  over store-serial @ over mark-serial ! swap store-count @ swap mark-count ! ;
\ Record a valid store's allocation point: ok; or invalid, with a mark
\ that every rollback refuses.
: store-mark ( mark store -- outcome )
  dup store-count-valid? if swap mark-set outcome-ok else drop /store-mark erase
  outcome-invalid then ;

\ Checks of a mark against a store; mark-older? and mark-newer? read one
\ identity each, only once the others have passed.
: mark-this? ( mark store -- flag )
  2dup swap mark-store @ = >r dup store-count-valid? >r
  store-generation @ swap mark-generation @ = r> r> and and ;
: mark-count? ( mark store -- flag )
  >r mark-count @ r@ store-base @ r> store-count @ between? ;
: mark-serial? ( mark store -- flag ) store-serial @ swap mark-serial @ swap upto? ;
: mark-shape? ( mark store -- flag )
  2dup mark-this? if 2dup mark-count? -rot mark-serial? and else 2drop false then ;
\ Unchecked: the identity of the record at the mark's count plus offset,
\ and the mark's serial.
: mark-identity ( mark store offset -- identity serial )
  rot dup >r mark-count @ + swap store-identity @ r> mark-serial @ ;
: mark-at-base? ( mark store -- flag ) store-base @ swap mark-count @ = ;
: mark-at-top? ( mark store -- flag ) store-count @ swap mark-count @ = ;
: mark-older? ( mark store -- flag )
  2dup mark-at-base? if 2drop true exit then -1 mark-identity <= ;
: mark-newer? ( mark store -- flag )
  2dup mark-at-top? if 2drop true exit then 0 mark-identity > ;
\ Whether store-rollback would accept the mark now.
: store-mark-valid? ( mark store -- flag )
  2dup mark-shape? if 2dup mark-older? -rot mark-newer? and else 2drop false then ;
\ Roll the store back to the mark: ok, or invalid with nothing changed.
: store-rollback ( mark store -- outcome )
  2dup store-mark-valid? if swap mark-count @ swap store-count ! outcome-ok
  else 2drop outcome-invalid then ;

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
\ The shape (capacity, width, base, the block and the limit) is fixed and
\ checked when the store is made, and sealed: corrupting any one shape
\ field breaks the seal, and every check then fails. A store is made in
\ the dictionary by store:, or at run time in store-size bytes of memory
\ the caller provides (from ALLOCATE or inside a larger record) by
\ store-init; both give the same layout and behaviour: the header, then
\ the block of capacity identity cells and the records.
\
\ Heap stores (plan task 1.1.5; ADR 0016 C5). store-heap-init makes a
\ store whose header lives in the caller's memory (store-header bytes,
\ such as a checker-context member) and whose block is ALLOCATEd, so that
\ it can grow: store-grow doubles the block, up to the store's limit,
\ when every record is in use. The header never moves, so marks stay
\ valid while the block grows; the block may move, so an address from
\ store-slot is valid only until the next store-grow (keep indices, never
\ addresses, across it). Growth that the limit or the heap refuses
\ changes nothing and gives full (ADR 0008). store-limit! sets the limit
\ (shrinking the block when it holds more), store-heap-free frees the
\ block. Every other word works alike on both kinds. Example:
\   create big store-header allot
\   4 /node 0 big store-heap-init drop   1000 big store-limit! drop
\   big store-grow drop    \ ok, still 4 records: a store grows only when every record
\                          \ is in use; then it gains 16 (4 -> 20)
\   big store-heap-free
\
\ Untrusted. One store is single-threaded: callers must not change it
\ during a call. Separate stores are independent. The layout (header,
\ capacity identity cells, then the records) is host-specific and must
\ never be serialized directly.

require ./bounds.fs
require ./outcome.fs
require ./portability.fs
require ./module.fs

\ The words of this file are public, in the compilation word list current
\ when it loads, except the helpers of making and moving a heap store's
\ block, which are private (ADR 0010): between module-open and
\ module-close the previous word list stays on the stack, and each part
\ names where its words go.
lf-lib-private module-open
dup set-current

begin-structure store-header
  field: store-capacity     \ maximum number of records
  field: store-width        \ address units per record, positive and aligned
  field: store-base         \ records a reset keeps
  field: store-seal         \ check value of the three shape fields
  field: store-count        \ records allocated
  field: store-generation   \ reset epoch; negative when poisoned
  field: store-serial       \ last identity issued
  field: store-block        \ a heap store's block, or 0 for a block right after
                            \ the header (so a store made in place has the same
                            \ bytes wherever it is, and a heap store's header
                            \ may move, as a context member does, while its
                            \ block stays)
  field: store-limit        \ most records: the capacity, or a heap store's limit
end-structure

\ The block of a store made in place: right after its header.
: store-inline ( store -- addr ) store-header + ;
: store-identities ( store -- addr )
  dup store-block @ ?dup if nip exit then store-header + ;
: store-records ( store -- addr ) dup store-identities swap store-capacity @ cells + ;
\ Unchecked: addresses for an already validated index.
: store-slot ( index store -- addr ) tuck store-width @ * swap store-records + ;
: store-identity ( index store -- addr ) store-identities swap cells + ;

\ Shape and seal.
: store-shape@ ( store -- capacity width base )
  dup store-capacity @ over store-width @ rot store-base @ ;
: >store-seal ( capacity width base -- x ) xor xor invert ;
\ The seal covers the block and the limit too. These words run on every
\ checked access (store-count-valid? below), so they are straight-line
\ code without branches.
: store-check ( store -- x )
  dup store-capacity @ over store-width @ xor over store-base @ xor invert
  over store-block @ xor swap store-limit @ xor ;
: store-width? ( width -- flag ) dup 0> swap dup aligned = and ;
: store-sealed? ( store -- flag ) dup store-check swap store-seal @ = ;
\ 0 <= x <= y, signed, as upto? (bounds.fs).
: store-upto? ( x y -- flag ) dup 0< 0= -rot u> 0= and ;
: store-limit? ( store -- flag ) dup store-capacity @ swap store-limit @ store-upto? ;
: store-ranges? ( store -- flag )
  dup store-base @ over store-capacity @ store-upto? swap store-limit? and ;
: store-shape? ( store -- flag )
  dup store-sealed? over store-width @ store-width? and swap store-ranges? and ;

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
: store-seal! ( store -- ) dup store-check swap store-seal ! ;
\ Unchecked: the shape fields are set. Zero the counters, put the block (0
\ for the one right after the header) and the limit (the capacity), seal,
\ and zero the block.
lf-lib-private set-current
: store-counters-zero ( store -- )
  0 over store-count ! 0 over store-generation ! 0 swap store-serial ! ;
: store-place ( block store -- )
  tuck store-block ! dup store-capacity @ over store-limit ! store-seal! ;
dup set-current
: store-zero ( store -- ) dup store-identities swap store-bytes erase ;
: store-format ( capacity width base store -- )
  dup >r store-shape! r@ store-counters-zero 0 r@ store-place r> store-zero ;
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
\ The check every checked access makes: store-live? and base <= count <=
\ capacity, written out in one word because it runs so often.
: store-count-valid? ( store -- flag )
  >r r@ store-check r@ store-seal @ = r@ store-generation @ 0< 0= and
  r@ store-width @ store-width? and r@ store-base @ r@ store-capacity @ store-upto? and
  r@ store-capacity @ r@ store-limit @ store-upto? and
  r@ store-count @ r@ store-base @ r> store-capacity @ between? and ;
: store-valid? ( index store -- flag )
  dup store-count-valid? if store-count @ 0 swap within else 2drop false then ;
\ One check of the store for both indices.
: store-in-count? ( index count -- flag ) 0 swap within ;
\ The read check of a store whose header was checked at the root of the
\ pass (store-count-valid?): index < count <= capacity, unsigned, from
\ two header fields, without the seal, shape or generation. A count
\ corrupted beyond the capacity (or negative) still refuses every index,
\ so a read stays inside the block; any other corruption is caught only
\ by the root's check. Used by the term and level stores' reads
\ (compact-store plan step S2; ADR 0016 C8).
: store-at? ( index store -- flag )
  dup store-capacity @ swap store-count @ tuck u< 0= -rot u< and ;
: store-pair-valid? ( left right store -- flag )
  dup store-count-valid? 0= if drop 2drop false exit then
  store-count @ tuck store-in-count? >r store-in-count? r> and ;

\ Allocation. store-new fails, changing nothing, on an invalid store, a full
\ store or a spent serial.
: store-room? ( store -- flag ) dup store-count @ swap store-capacity @ < ;
: store-spent? ( store -- flag ) store-serial @ max-n = ;

\ Allocation-failure injection (plan task 1.4.6), for tests only. A
\ program that defines store-fault-hooks before this file loads gets
\ store-refuse? ( store -- flag ), a DEFER that store-open? asks about
\ every allocation that would otherwise go ahead, in every store
\ (store-new, and the name table's store-open? then store-claim): true
\ refuses it as if the store were full, changing nothing; the word may
\ also THROW. Its default never refuses; tests/support/alloc-fail.fs
\ makes the k-th allocation fail. Without store-fault-hooks, store-open?
\ is compiled exactly as without this paragraph: no DEFER, no extra
\ call, no cost. LeanForth never interprets its input as Forth and
\ src/main.fs never defines store-fault-hooks, so no input can turn the
\ hook on or reach it.
[defined] store-fault-hooks [if]
defer store-refuse? ( store -- flag )
: store-never ( store -- false ) drop false ;
' store-never is store-refuse?
: store-open? ( store -- flag )
  dup store-count-valid? over store-room? and over store-spent? 0= and
  if store-refuse? 0= else drop false then ;
\ The hook is also asked before a heap store's block grows (store-grow).
: store-grow-refused? ( store -- flag ) store-refuse? ;
[else]
: store-open? ( store -- flag )
  dup store-count-valid? over store-room? and swap store-spent? 0= and ;
: store-grow-refused? ( store -- false ) drop false ;
[then]
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

\ Heap stores (see the header). A store is a heap store when it names a
\ block of its own; a zeroed header names none.
: store-heap? ( store -- flag ) store-block @ 0<> ;
\ ALLOCATE u zeroed address units: the address and 0, or the ior.
lf-lib-private set-current
: store-zeroed-block ( u -- addr ior )
  dup allocate ?dup if rot drop exit then tuck swap erase 0 ;
dup set-current
\ Make a heap store of capacity records in a zeroed block, its limit the
\ capacity: ok; invalid for an unsound shape or full when the heap has no
\ room, the header then zero (no check accepts it). The header must not
\ hold a block: store-heap-free first.
: store-heap-init ( capacity width base store -- outcome )
  >r 2>r dup 2r@ store-plan? 2r> rot 0= if 2drop drop r> store-header erase
    outcome-invalid exit then
  r@ store-shape! r@ store-counters-zero r@ store-bytes store-zeroed-block
  if drop r> store-header erase outcome-full exit then r> store-place outcome-ok ;
\ Free a heap store's block and zero its header; a store made in place is
\ left alone.
: store-heap-free ( store -- )
  dup store-heap? 0= if drop exit then
  dup store-identities free drop store-header erase ;
\ Moving to a new zeroed block of n records: the first min(n, capacity)
\ identities and records are copied, the old block freed. Unchecked: a
\ live heap store and n >= count.
lf-lib-private set-current
: store-kept ( n store -- m ) store-capacity @ min ;
: store-copy-ids ( new m store -- ) >r swap r> store-identities swap rot cells move ;
: store-copy-records ( new n m store -- )
  >r >r cells + r> r@ store-width @ * r> store-records -rot move ;
: store-rehome ( new n store -- )
  >r dup r@ store-kept 2 pick over r@ store-copy-ids r> store-copy-records ;
: store-install ( new n store -- )
  dup store-identities free drop tuck store-capacity ! tuck store-block ! store-seal! ;
: store-resize ( n store -- outcome )
  2dup store-width @ cell+ * store-zeroed-block if drop 2drop outcome-full exit then
  -rot >r 2dup r@ store-rehome r> store-install outcome-ok ;
dup set-current
\ The capacity growth gives: double, at least 16 more, never past the
\ limit (so it cannot overflow).
: store-doubled ( store -- n )
  dup store-capacity @ dup 16 max rot store-limit @ 2 pick - min + ;
: store-at-limit? ( store -- flag ) dup store-capacity @ swap store-limit @ = ;
\ Make room for one more record: ok when there is room, grown or not;
\ full when the store is at its limit, is not a heap store, the heap has
\ no room or the test hook refuses (nothing changed then); invalid for a
\ store whose count is not valid (store-count-valid?).
: store-below-limit? ( store -- flag ) dup store-heap? swap store-at-limit? 0= and ;
: store-growable? ( store -- flag )
  dup store-below-limit? if store-grow-refused? 0= else drop false then ;
: store-grow ( store -- outcome )
  dup store-count-valid? 0= if drop outcome-invalid exit then
  dup store-room? if drop outcome-ok exit then
  dup store-growable? if dup store-doubled swap store-resize else drop outcome-full then ;
\ The cheap form before an allocation: store-grow only when the raw count
\ has reached the capacity, else ok without any check, for callers whose
\ allocation (store-new, store-open?) checks the store anyway. Same
\ outcome of the allocation as store-grow first.
: store-filled? ( store -- flag ) dup store-count @ swap store-capacity @ < 0= ;
: store-ready ( store -- outcome ) dup store-filled? if store-grow else drop outcome-ok then ;
\ Set a live heap store's limit, at least its count and a sound size;
\ a block that holds more records shrinks to it: ok, full when that
\ shrinking finds no heap (nothing changed), invalid otherwise.
: store-limit-ok? ( limit store -- flag )
  dup store-live? over store-heap? and 0= if 2drop false exit then
  2dup store-count @ < if 2drop false exit then
  >r r@ store-width @ r> store-base @ store-plan? ;
: store-limit-set ( limit store -- ) tuck store-limit ! store-seal! ;
: store-limit! ( limit store -- outcome )
  2dup store-limit-ok? 0= if 2drop outcome-invalid exit then
  2dup store-capacity @ < if 2dup store-resize dup ok? 0= if nip nip exit then drop then
  store-limit-set outcome-ok ;

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
\ That argument assumes the count only moves by store-new, store-clear
\ and store-rollback: code that saves a count and later restores it by
\ hand (as some older modules still do for the term store) can raise it
\ over records rolled back and allocated again, and a stale mark may then
\ pass. Converting those modules to marks is a follow-up. A mark of an
\ invalid store names no store and is always refused. Marks are not
\ capabilities: a forged record that passes these checks is accepted.
\ Like the store, a mark is host-specific memory.
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

module-close

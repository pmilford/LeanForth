\ Prototype (ADR 0016, measurement code): growable heap arenas of packed 32-bit
\ fields, and open-addressing hash tables of 32-bit slots. Not a module of src/.
\ Growth is by RESIZE (doubling); a failed ALLOCATE or RESIZE throws here
\ (the design reports full instead).

begin-structure /arena
  field: arena-base      \ heap block, or 0
  field: arena-cap       \ capacity in quads (packed 32-bit fields)
  field: arena-used      \ quads in use
end-structure
: arena: ( "name" -- ) create here /arena allot /arena erase ;
: arena-init ( quads arena -- )
  >r dup u32s allocate throw r@ arena-base ! r@ arena-cap ! 0 r> arena-used ! ;
: arena-free ( arena -- ) dup arena-base @ ?dup if free throw then /arena erase ;
: arena-grow ( arena -- )
  dup arena-cap @ 2* 1024 max over arena-base @ over u32s resize throw
  rot tuck arena-base ! arena-cap ! ;
\ Claim n quads, growing as needed; gives the quad index of the first.
: arena-room ( n arena -- )
  begin 2dup arena-used @ + over arena-cap @ > while dup arena-grow repeat 2drop ;
: arena-claim ( n arena -- i ) 2dup arena-room dup arena-used @ >r arena-used +! r> ;
: arena-at ( i arena -- addr ) arena-base @ swap u32s + ;
: arena@ ( i arena -- u ) arena-at u32@ ;
: arena! ( u i arena -- ) arena-at u32! ;
: arena-push ( u arena -- ) 1 over arena-claim swap arena! ;
: arena-bytes ( arena -- au ) arena-cap @ u32s ;
: arena-used-bytes ( arena -- au ) arena-used @ u32s ;

\ Byte pools (names and literals): bytes copied with MOVE, compared with
\ COMPARE; offsets are indices.
begin-structure /pool
  field: pool-base
  field: pool-cap
  field: pool-used
end-structure
: pool: ( "name" -- ) create here /pool allot /pool erase ;
: pool-init ( au pool -- ) >r dup allocate throw r@ pool-base ! r@ pool-cap ! 0 r> pool-used ! ;
: pool-grow ( pool -- )
  dup pool-cap @ 2* over pool-base @ over resize throw rot tuck pool-base ! pool-cap ! ;
: pool-room ( u pool -- )
  begin 2dup pool-used @ + over pool-cap @ > while dup pool-grow repeat 2drop ;
: pool-text ( offset u pool -- addr u ) rot swap pool-base @ + swap ;
\ Append u bytes; gives their offset.
: pool-add ( addr u pool -- offset )
  2dup pool-room >r r@ pool-used @ r@ pool-base @ + swap dup >r move
  r> r> tuck pool-used @ swap rot pool-used +! ;

\ Portable 32-bit hashing: every product is masked to 32 bits, so 32-bit
\ and 64-bit hosts give the same values. Murmur3's finalizer constants.
$85EB 16 lshift $CA6B or constant hk1
$C2B2 16 lshift $AE35 or constant hk2
: fmix ( h -- h' )
  dup 16 rshift xor hk1 * u32-mask and dup 13 rshift xor hk2 * u32-mask and
  dup 16 rshift xor ;
: h+ ( h x -- h' ) xor fmix ;
\ FNV-1a over bytes (byte access: in the design this is lib/bytes.fs).
$811C 16 lshift $9DC5 or constant fnv-basis
$0100 16 lshift $0193 or constant fnv-prime
: bytes-hash ( addr u -- h )
  fnv-basis -rot over + swap ?do i c@ xor fnv-prime * u32-mask and loop ;

\ Open-addressing tables: slots hold a record index + 1, 0 is empty;
\ linear probing; capacity a power of two; grows at load 3/4. A table's
\ rehash word ( index -- h ) recomputes an entry's hash from its record.
begin-structure /htab
  field: htab-base
  field: htab-mask       \ slots - 1
  field: htab-count
  field: htab-probes     \ statistics: occupied slots compared
  field: htab-lookups    \ statistics: lookups
  field: htab-grows
  field: htab-rehash     \ xt ( index -- h )
end-structure
: htab: ( xt "name" -- ) create here /htab allot dup /htab erase htab-rehash ! ;
: htab-slots ( htab -- n ) htab-mask @ 1+ ;
: htab-alloc ( n -- addr ) dup u32s allocate throw tuck swap u32s erase ;
: htab-init ( log2 htab -- )
  >r 1 swap lshift dup htab-alloc r@ htab-base ! 1- r@ htab-mask ! 0 r> htab-count ! ;
: slot-at ( i htab -- addr ) htab-base @ swap u32s + ;
: htab-full? ( htab -- flag ) dup htab-count @ 1+ 4 * swap htab-slots 3 * > ;
\ First empty slot for hash h.
: htab-empty ( h htab -- addr )
  >r r@ htab-mask @ and begin dup r@ slot-at u32@ while 1+ r@ htab-mask @ and repeat
  r> slot-at ;
: rehash-slot ( u htab -- ) 2dup htab-rehash @ swap 1- swap execute swap htab-empty u32! ;
\ Double the table and re-insert every entry by its recomputed hash.
: htab-move ( old n htab -- )
  swap 0 ?do over i u32s + u32@ ?dup if over rehash-slot then loop 2drop ;
: htab-grow ( htab -- )
  >r r@ htab-base @ r@ htab-slots dup 2* dup htab-alloc r@ htab-base ! 1- r@ htab-mask !
  1 r@ htab-grows +! over swap r> htab-move free throw ;
\ Grow first when one more entry would pass load 3/4.
: htab-ready ( htab -- ) dup htab-full? if htab-grow else drop then ;
\ Count a lookup and an insertion.
: htab-looked ( htab -- ) 1 swap htab-lookups +! ;
: htab-added ( htab -- ) 1 swap htab-count +! ;
\ Find the key a comparison xt ( index -- flag ) recognises: its index, or
\ the empty slot where it belongs. Counts lookups and compared slots.
: htab-find {: h tab xt -- index true | addr false :}
  tab htab-looked h tab htab-mask @ and
  begin dup tab slot-at u32@ dup while
    1 tab htab-probes +! 1- dup xt execute if nip true exit then drop
    1+ tab htab-mask @ and
  repeat drop tab slot-at false ;

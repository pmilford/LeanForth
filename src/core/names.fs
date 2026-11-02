\ Untrusted bounded interning experiment for structured name components.
\ Names are anonymous, prefix+byte-string, or prefix+nonnegative integer.
\ Exact byte equality is used; UTF-8 validity and Lean String interpretation
\ are not checked here. The caller must provide readable input memory and
\ prevent concurrent or raw mutation. This is not a trusted name table, API,
\ declaration environment, serialization, or theorem-checking boundary.
\ All IDs become stale after reset; generation values are mutable diagnostics.

64 constant lf-name-capacity
2048 constant lf-name-byte-capacity
0 constant lf-name-tag-anon
1 constant lf-name-tag-str
2 constant lf-name-tag-num
4 constant lf-name-slot-cells
create lf-name-storage lf-name-capacity lf-name-slot-cells * cells allot
create lf-name-bytes lf-name-byte-capacity allot
create lf-name-input-copy lf-name-byte-capacity allot
variable lf-name-count
variable lf-name-used
variable lf-name-generation
variable lf-name-query-prefix
variable lf-name-query-number
variable lf-name-query-source
variable lf-name-query-length

\ Internal slot address; the caller must supply an in-range index.
: lf-name-slot ( index -- addr ) lf-name-slot-cells * cells lf-name-storage + ;
\ Read a numbered field of an already allocated slot.
: lf-name-field ( index field -- value ) cells swap lf-name-slot + @ ;

\ Reset to anonymous name zero, invalidating every prior ID. Generation
\ saturation poisons the table rather than silently wrapping an old value.
: lf-name-reset ( -- )
  0 lf-name-slot lf-name-slot-cells cells erase
  1 lf-name-count ! 0 lf-name-used !
  lf-name-generation @ dup 0< if drop exit then
  dup -1 1 rshift = if drop -1 else 1+ then lf-name-generation ! ;

\ Check count and byte bounds before deriving internal addresses.
: lf-name-state-valid? ( -- flag )
  lf-name-count @ dup 1 >= swap lf-name-capacity <= and
  lf-name-used @ dup 0< 0= swap lf-name-byte-capacity <= and and
  lf-name-generation @ 0< 0= and ;

\ Test whether an ID is currently allocated; reused stale IDs are undetectable.
: lf-name-valid? ( id -- flag )
  lf-name-state-valid? 0= if drop false exit then
  dup 0< 0= swap lf-name-count @ < and ;

\ Guard internal byte reads against corrupted tags, lengths and offsets. This
\ validates bounds and backward prefixes, not uniqueness or immutable storage.
: lf-name-storage-valid? ( -- flag )
  lf-name-state-valid? 0= if false exit then
  0 lf-name-slot dup @ over cell+ @ or
  over 2 cells + @ or swap 3 cells + @ or if false exit then
  lf-name-count @ 1 ?do
    i 1 lf-name-field dup 0< swap i >= or if false unloop exit then
    i 0 lf-name-field case
      lf-name-tag-num of
        i 2 lf-name-field 0< i 3 lf-name-field 0<> or if false unloop exit then
      endof
      lf-name-tag-str of
        i 2 lf-name-field dup 0< over lf-name-used @ > or if
          drop false unloop exit
        then
        lf-name-used @ swap -
        i 3 lf-name-field dup 0< swap rot > or if false unloop exit then
      endof
      drop false unloop exit
    endcase
  loop true ;

\ Compare a valid numeric slot with the current intern query.
: lf-name-number-match? ( index -- flag )
  dup 0 lf-name-field lf-name-tag-num =
  over 1 lf-name-field lf-name-query-prefix @ = and
  swap 2 lf-name-field lf-name-query-number @ = and ;

\ Compare a valid byte-string slot with the current intern query.
: lf-name-string-match? ( index -- flag )
  dup 0 lf-name-field lf-name-tag-str <> if drop false exit then
  dup 1 lf-name-field lf-name-query-prefix @ <> if drop false exit then
  dup 3 lf-name-field lf-name-query-length @ <> if drop false exit then
  2 lf-name-field lf-name-bytes + lf-name-query-length @
  lf-name-query-source @ lf-name-query-length @ compare 0= ;

\ Intern a numeric component. Existing identical names retain their ID, even
\ when the table is full; invalid inputs or exhaustion leave counts unchanged.
: lf-name-num ( prefix number -- id true | false )
  lf-name-storage-valid? 0= if 2drop false exit then
  dup 0< 2 pick lf-name-valid? 0= or if 2drop false exit then
  lf-name-query-number ! lf-name-query-prefix !
  lf-name-count @ 1 ?do
    i lf-name-number-match? if i true unloop exit then
  loop
  lf-name-count @ lf-name-capacity >= if false exit then
  lf-name-count @ lf-name-slot >r
  lf-name-tag-num r@ ! lf-name-query-prefix @ r@ cell+ !
  lf-name-query-number @ r@ 2 cells + ! 0 r> 3 cells + !
  lf-name-count @ 1 lf-name-count +! true ;

\ Intern a byte-string component, copying the query before modifying scratch
\ variables. Input memory must remain readable during the copy; no UTF-8 check
\ occurs. MOVE permits input to overlap either byte buffer.
: lf-name-str ( prefix addr length -- id true | false )
  lf-name-storage-valid? 0= if 2drop drop false exit then
  dup 0< over lf-name-byte-capacity > or if 2drop drop false exit then
  2 pick lf-name-valid? 0= if 2drop drop false exit then
  2dup lf-name-input-copy swap move
  lf-name-query-length ! drop
  lf-name-input-copy lf-name-query-source ! lf-name-query-prefix !
  lf-name-count @ 1 ?do
    i lf-name-string-match? if i true unloop exit then
  loop
  lf-name-count @ lf-name-capacity >= if false exit then
  lf-name-query-length @ lf-name-byte-capacity lf-name-used @ - > if false exit then
  lf-name-query-source @ lf-name-bytes lf-name-used @ + lf-name-query-length @ move
  lf-name-count @ lf-name-slot >r
  lf-name-tag-str r@ ! lf-name-query-prefix @ r@ cell+ !
  lf-name-used @ r@ 2 cells + ! lf-name-query-length @ r> 3 cells + !
  lf-name-query-length @ lf-name-used +!
  lf-name-count @ 1 lf-name-count +! true ;

0 lf-name-generation !
lf-name-reset

\ Bounded interning of Lean structured names, one component at a time. A
\ name is anonymous (ID 0), or a prefix name extended by a byte string or a
\ nonnegative number; equal components under equal prefixes get one ID.
\ Untrusted. Bytes compare exactly; UTF-8 validity and Lean String meaning
\ are not checked. Not a trusted name table, declaration environment,
\ serialization or theorem-checking boundary.
\ State: entries live in a bounded store, lf-names (lib/store.fs), whose
\ record 0 is the anonymous name; string bytes are appended to the byte
\ pool of one record, lf-name-pool. Both are members of the checker
\ context (lib/context.fs), reset by a set-up word in every context, so
\ IDs mean something only in their own context. Single-threaded within one
\ context: callers keep input memory readable and prevent raw mutation
\ during a call. A reset makes every ID stale, and a reused stale ID is
\ not detectable here.

require ../lib/lib.fs

64 constant lf-name-capacity
2048 constant lf-name-byte-capacity
0 constant lf-name-tag-anon
1 constant lf-name-tag-str
2 constant lf-name-tag-num

\ One entry: kind, prefix ID, then the number or the string's byte offset in
\ lf-name-bytes, then the string length (always 0 for a number).
begin-structure /lf-entry
  field: lf-entry-tag
  field: lf-entry-prefix
  field: lf-entry-payload
  field: lf-entry-length
end-structure
/lf-entry 1 cells / constant lf-name-slot-cells

lf-name-capacity /lf-entry 1 context-store: lf-names

\ The byte pool: bytes in use, the pool itself, and a copy of each query,
\ made first so that the query may alias any buffer of this module.
begin-structure /lf-npool
  field: lf-npool-used
  lf-name-byte-capacity +field lf-npool-bytes
  lf-name-byte-capacity +field lf-npool-input
end-structure
/lf-npool context-record: lf-name-pool
: lf-name-used ( -- addr ) lf-name-pool lf-npool-used ;
: lf-name-bytes ( -- addr ) lf-name-pool lf-npool-bytes ;
: lf-name-input-copy ( -- addr ) lf-name-pool lf-npool-input ;

\ The store's fields under their established names (tests corrupt them).
: lf-name-count ( -- addr ) lf-names store-count ;
: lf-name-generation ( -- addr ) lf-names store-generation ;
\ Entry address; the ID must already be validated.
: lf-name-slot ( id -- addr ) lf-names store-slot ;
\ Numbered field of a valid entry (0 tag, 1 prefix, 2 payload, 3 length);
\ kept for existing callers, new code uses the named fields.
: lf-name-field ( id field# -- value ) cells swap lf-name-slot + @ ;
\ Kind and prefix of a valid ID.
: lf-name-tag@ ( id -- tag ) lf-name-slot lf-entry-tag @ ;
: lf-name-prefix@ ( id -- prefix ) lf-name-slot lf-entry-prefix @ ;

\ Reset to the anonymous name alone and advance the generation; saturation
\ poisons the table rather than wrapping (see store-clear).
: lf-name-reset ( -- ) 0 lf-name-slot /lf-entry erase 0 lf-name-used ! lf-names store-clear ;

\ Count, byte use and generation are in range; checked before addressing.
: lf-name-state-valid? ( -- flag )
  lf-names store-count-valid? lf-name-used @ lf-name-byte-capacity upto? and ;
\ An ID is allocated now; a reused stale ID is undetectable.
: lf-name-valid? ( id -- flag )
  lf-name-state-valid? if lf-names store-valid? else drop false then ;

\ Full structural audit, guarding later byte reads against corrupted tags,
\ prefixes, offsets and lengths. Checks bounds and that prefixes point
\ backwards; not uniqueness or immutability.
: lf-name-span? ( offset length -- flag )
  over lf-name-used @ upto? if swap lf-name-used @ swap - upto? else 2drop false then ;
: lf-name-num-ok? ( entry -- flag ) dup lf-entry-payload @ 0< 0= swap lf-entry-length @ 0= and ;
: lf-name-str-ok? ( entry -- flag ) dup lf-entry-payload @ swap lf-entry-length @ lf-name-span? ;
: lf-name-body-ok? ( entry -- flag )
  dup lf-entry-tag @ case
    lf-name-tag-num of lf-name-num-ok? endof
    lf-name-tag-str of lf-name-str-ok? endof
    nip false swap endcase ;   \ any other kind is invalid; ENDCASE drops the tag
: lf-name-entry-ok? ( id -- flag )
  dup lf-name-slot tuck lf-entry-prefix @ 0 rot within if lf-name-body-ok? else drop false then ;
: lf-names-ok? ( -- flag )
  lf-name-count @ 1 ?do i lf-name-entry-ok? 0= if false unloop exit then loop true ;
: lf-name-storage-valid? ( -- flag )
  lf-name-state-valid? 0= if false exit then
  0 lf-name-slot lf-name-slot-cells cells-zero? lf-names-ok? and ;

\ Entry matching: same kind and prefix, then same number or same bytes. A
\ string query is the first length bytes of lf-name-input-copy.
: lf-name-head? ( prefix tag entry -- flag ) tuck lf-entry-tag @ = -rot lf-entry-prefix @ = and ;
: lf-name-num-match? ( prefix number entry -- flag )
  tuck lf-entry-payload @ = >r lf-name-tag-num swap lf-name-head? r> and ;
: lf-name-query ( length -- addr length ) lf-name-input-copy swap ;
: lf-name-bytes@ ( entry -- addr length ) dup lf-entry-payload @ lf-name-bytes + swap lf-entry-length @ ;
: lf-name-str-match? ( prefix length entry -- flag )
  >r swap lf-name-tag-str r@ lf-name-head?
  if lf-name-query r> lf-name-bytes@ compare 0= else drop r> drop false then ;

\ Linear search of entries 1 .. count-1.
: lf-name-find-num ( prefix number -- id true | false )
  lf-name-count @ 1 ?do 2dup i lf-name-slot lf-name-num-match?
    if 2drop i true unloop exit then loop 2drop false ;
: lf-name-find-str ( prefix length -- id true | false )
  lf-name-count @ 1 ?do 2dup i lf-name-slot lf-name-str-match?
    if 2drop i true unloop exit then loop 2drop false ;

\ Appending; callers have checked validity, absence and room. The store's
\ identities are issued but unused: names are compared by content.
: lf-name-room? ( -- flag ) lf-names store-open? ;
: lf-name-byte-room? ( length -- flag ) lf-name-byte-capacity lf-name-used @ - upto? ;
: lf-name-new ( prefix tag -- entry id )
  lf-names store-claim dup >r lf-name-slot tuck lf-entry-tag ! tuck lf-entry-prefix ! r> ;
: lf-name-add-num ( prefix number -- id )
  >r lf-name-tag-num lf-name-new swap r> over lf-entry-payload ! 0 swap lf-entry-length ! ;
: lf-name-store-bytes ( length -- offset )
  >r lf-name-input-copy lf-name-bytes lf-name-used @ + r@ move
  lf-name-used @ r> lf-name-used +! ;
: lf-name-add-str ( prefix length -- id )
  swap lf-name-tag-str lf-name-new >r
  over lf-name-store-bytes over lf-entry-payload ! lf-entry-length ! r> ;

\ Interning valid input: an existing identical name keeps its ID even when
\ the table is full; exhaustion changes nothing.
: lf-name-intern-num ( prefix number -- id true | false )
  2dup lf-name-find-num if nip nip true exit then
  lf-name-room? if lf-name-add-num true else 2drop false then ;
: lf-name-intern-str ( prefix length -- id true | false )
  2dup lf-name-find-str if nip nip true exit then
  lf-name-room? over lf-name-byte-room? and if lf-name-add-str true else 2drop false then ;

\ Intern a numeric component; invalid input changes nothing.
: lf-name-num-args? ( prefix number -- flag )
  0< 0= swap lf-name-valid? and lf-name-storage-valid? and ;
: lf-name-num ( prefix number -- id true | false )
  2dup lf-name-num-args? if lf-name-intern-num else 2drop false then ;

\ Intern a byte-string component. The input is copied before anything else
\ changes, so it may overlap any buffer here; it must stay readable during
\ the copy. Invalid input changes nothing.
: lf-name-str-args? ( prefix length -- flag )
  lf-name-byte-capacity upto? swap lf-name-valid? and lf-name-storage-valid? and ;
: lf-name-copy-in ( addr length -- length ) tuck lf-name-input-copy swap move ;
: lf-name-str ( prefix addr length -- id true | false )
  >r over r@ lf-name-str-args? r> swap
  if lf-name-copy-in lf-name-intern-str else 2drop drop false then ;

\ Every context starts with the anonymous name alone.
' lf-name-reset context-setup

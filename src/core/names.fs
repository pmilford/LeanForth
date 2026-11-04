\ Bounded interning of Lean structured names, one component at a time. A
\ name is anonymous (ID 0), or a prefix name extended by a byte string or a
\ nonnegative number; equal components under equal prefixes get one ID.
\ Untrusted. Bytes compare exactly; UTF-8 validity and Lean String meaning
\ are not checked. Not a trusted name table, declaration environment,
\ serialization or theorem-checking boundary.
\ State: entries live in a heap store, lf-names (lib/store.fs), whose
\ record 0 is the anonymous name; string bytes are appended to the byte
\ pool of one record, lf-name-pool. Both are members of the checker
\ context (lib/context.fs), reset by a set-up word in every context, so
\ IDs mean something only in their own context. Single-threaded within one
\ context: callers keep input memory readable and prevent raw mutation
\ during a call. A reset makes every ID stale, and a reused stale ID is
\ not detectable here.
\
\ The input view (ADR 0016 C3, C9 step 3; plan task 3.2.2). lf-name-attach
\ makes the names of a sealed compact input tier (core/compact.fs, filled
\ by import/stage.fs and shared read-only) this context's names: an input
\ name's ID is its number in that tier, and a name made afterwards goes
\ into this context's one scratch tier over it, interned with the input's,
\ so that equal names are always one ID (ADR 0016 C4). While a view is
\ attached the entry store is not used, every name is checked when it is
\ made (ADR 0016 C8) so lf-name-storage-valid? has nothing to audit, and
\ lf-name-reset empties the scratch tier (the generation still advances).
\ lf-name-detach ends the view. The scratch tier, a member of the context
\ record lf-name-view, is freed by its teardown word.

require ../lib/lib.fs
require ./diagnostics.fs
require ./compact.fs

64 constant lf-name-default
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

\ The entries are a heap store growing up to a capacity that is a setting
\ of each context, as for terms (terms.fs); a new context starts with
\ lf-name-default entries.
store-header context-record: lf-names
: lf-names-make ( -- )
  lf-name-default /lf-entry 1 lf-names store-heap-init ok? 0= abort" names: no heap" ;
' lf-names-make context-setup
:noname ( -- ) lf-names store-heap-free ; context-teardown
: lf-name-capacity ( -- n ) lf-names store-limit @ ;
: lf-name-capacity! ( n -- outcome ) lf-names store-limit! ;

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

\ The input view (see the header).
begin-structure /lf-nview
  field: lf-nview-input            \ the sealed input tier, or 0 for none
  /tier +field lf-nview-scratch    \ this context's scratch tier over it
end-structure
/lf-nview context-record: lf-name-view
:noname ( -- ) lf-name-view lf-nview-scratch tier-free ; context-teardown
: lf-name-viewed? ( -- flag ) lf-name-view lf-nview-input @ 0<> ;
: lf-name-tier ( -- tier ) lf-name-view lf-nview-scratch ;

\ The store's fields under their established names (tests corrupt them).
: lf-name-count ( -- addr ) lf-names store-count ;
: lf-name-generation ( -- addr ) lf-names store-generation ;
\ Entry address; the ID must already be validated (no view attached).
: lf-name-slot ( id -- addr ) lf-names store-slot ;
\ Numbered field of a valid entry (0 tag, 1 prefix, 2 payload, 3 length);
\ kept for existing callers, new code uses the named fields.
: lf-name-field ( id field# -- value ) cells swap lf-name-slot + @ ;
\ Kind and prefix of a valid ID.
: lf-name-tag@ ( id -- tag )
  lf-name-viewed? if lf-name-tier name-tag@ else lf-name-slot lf-entry-tag @ then ;
: lf-name-prefix@ ( id -- prefix )
  lf-name-viewed? if lf-name-tier name-prefix@ else lf-name-slot lf-entry-prefix @ then ;
\ A valid ID's stored hash, under a view (lf-name-digest).
: lf-name-hash ( id -- h ) lf-name-tier name-hash@ ;

\ Reset to the anonymous name alone and advance the generation; saturation
\ poisons the table rather than wrapping (see store-clear). Under a view,
\ the scratch tier is emptied.
: lf-name-scratch-reset ( -- ) lf-name-viewed? if lf-name-tier tier-reset drop then ;
: lf-name-reset ( -- )
  lf-name-scratch-reset 0 lf-name-slot /lf-entry erase 0 lf-name-used !
  lf-names store-clear ;

\ Count, byte use and generation are in range; checked before addressing.
: lf-name-state-valid? ( -- flag )
  lf-names store-count-valid? lf-name-used @ lf-name-byte-capacity upto? and ;
\ An ID is allocated now; a reused stale ID is undetectable.
: lf-name-stored? ( id -- flag )
  lf-name-state-valid? if lf-names store-valid? else drop false then ;
: lf-name-valid? ( id -- flag )
  lf-name-viewed? if lf-name-tier name-valid? else lf-name-stored? then ;

\ Attach the sealed input tier as this context's names, emptying the
\ scratch tier and advancing the generation: ok, or the outcome of making
\ the scratch tier (no view then). Detach: back to the entry store.
: lf-name-viewing ( input -- ) lf-name-view lf-nview-input ! lf-name-reset ;
: lf-name-unview ( -- ) lf-name-tier tier-free 0 lf-name-view lf-nview-input ! ;
: lf-name-attach ( input -- outcome )
  lf-name-unview dup lf-name-tier tier-extend dup ok?
  if drop lf-name-viewing outcome-ok else nip then ;
: lf-name-detach ( -- ) lf-name-unview lf-name-reset ;
\ The number of names under the view, for digests.
: lf-name-numbers ( -- n ) lf-name-tier tier-names cons-numbers ;

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
: lf-name-entries-valid? ( -- flag )
  lf-name-state-valid? 0= if false exit then
  0 lf-name-slot lf-name-slot-cells cells-zero? lf-names-ok? and ;
\ Under a view every name was checked when it was made.
: lf-name-storage-valid? ( -- flag )
  lf-name-viewed? if true else lf-name-entries-valid? then ;

\ Entry matching: same kind and prefix, then same number or same bytes. A
\ string query is the first length bytes of lf-name-input-copy.
: lf-name-head? ( prefix tag entry -- flag ) tuck lf-entry-tag @ = -rot lf-entry-prefix @ = and ;
: lf-name-num-match? ( prefix number entry -- flag )
  tuck lf-entry-payload @ = >r lf-name-tag-num swap lf-name-head? r> and ;
: lf-name-query ( length -- addr length ) lf-name-input-copy swap ;
: lf-name-bytes@ ( entry -- addr length ) dup lf-entry-payload @ lf-name-bytes + swap lf-entry-length @ ;
\ The component of a name: the bytes of a string component, the number of
\ a numeric one. Unchecked: the ID is valid and of that kind (lf-name-tag@),
\ and the bytes are read before the name store changes. Under a view, the
\ bytes of an input name never move; a scratch name's do when the scratch
\ tier grows.
: lf-name-text ( id -- c-addr u )
  lf-name-viewed? if lf-name-tier name-text@ else lf-name-slot lf-name-bytes@ then ;
: lf-name-payload ( id -- n )
  lf-name-viewed? if lf-name-tier name-number@ else lf-name-slot lf-entry-payload @ then ;
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
: lf-name-room? ( -- flag ) lf-names store-grow drop lf-names store-open? ;
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
\ the table is full; exhaustion changes nothing and is recorded as a
\ diagnostic: no free entry or a spent serial, or for a string, no room
\ for its bytes (the bytes needed and the capacity).
: lf-name-site ( -- site ) c" names lf-name-intern" ;
: lf-name-refused ( -- false )
  lf-names lf-name-site lf-diag-names-full lf-diag-store false ;
: lf-name-bytes-refused ( length -- false )
  lf-name-used @ + lf-name-byte-capacity lf-name-site lf-diag-name-bytes-full lf-diag-note
  false ;
: lf-name-str-refused ( prefix length -- false )
  nip lf-name-room? if lf-name-bytes-refused else drop lf-name-refused then ;
: lf-name-intern-num ( prefix number -- id true | false )
  2dup lf-name-find-num if nip nip true exit then
  lf-name-room? if lf-name-add-num true else 2drop lf-name-refused then ;
: lf-name-intern-str ( prefix length -- id true | false )
  2dup lf-name-find-str if nip nip true exit then
  lf-name-room? over lf-name-byte-room? and
  if lf-name-add-str true else lf-name-str-refused then ;

\ Intern a numeric component; invalid input changes nothing.
: lf-name-num-args? ( prefix number -- flag )
  0< 0= swap lf-name-valid? and lf-name-storage-valid? and ;
\ Under a view, names are made in the scratch tier (full there is false,
\ with no diagnostic).
: lf-name-made ( n outcome -- id true | false ) ok? if true else drop false then ;
: lf-name-viewed-num ( prefix number -- id true | false )
  lf-name-tier name-num lf-name-made ;
: lf-name-num ( prefix number -- id true | false )
  2dup lf-name-num-args? 0= if 2drop false exit then
  lf-name-viewed? if lf-name-viewed-num else lf-name-intern-num then ;

\ Intern a byte-string component. The input is copied before anything else
\ changes, so it may overlap any buffer here; it must stay readable during
\ the copy. Invalid input changes nothing.
: lf-name-str-args? ( prefix length -- flag )
  lf-name-byte-capacity upto? swap lf-name-valid? and lf-name-storage-valid? and ;
: lf-name-copy-in ( addr length -- length ) tuck lf-name-input-copy swap move ;
\ Under a view the copy, never the caller's text, goes to the scratch
\ tier, whose byte slab may move while it makes room.
: lf-name-viewed-str ( prefix length -- id true | false )
  lf-name-query lf-name-tier name-str lf-name-made ;
: lf-name-copied-str ( prefix length -- id true | false )
  lf-name-viewed? if lf-name-viewed-str else lf-name-intern-str then ;
: lf-name-str ( prefix addr length -- id true | false )
  >r over r@ lf-name-str-args? r> swap
  if lf-name-copy-in lf-name-copied-str else 2drop drop false then ;

\ Every context starts with the anonymous name alone.
' lf-name-reset context-setup

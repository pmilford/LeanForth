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
\ record lf-name-view, is freed by its teardown word. The scratch tier
\ points into the input tier, so the stage that holds the input tier must
\ outlive the view: free it only after lf-name-detach, or after the
\ context is freed.
\
\ The two modes. Every operation that reads or makes names -- a name's
\ kind, prefix and component, whether an ID is valid, the audit of one
\ component and of the whole storage, making a component, and the reset's
\ own part -- has one word for each mode, in two rows of execution tokens
\ (lf-name-stored-ops and lf-name-viewed-ops, filled once while loading,
\ read-only after). The public words run the current mode's word, so none
\ of them can read the entry store under a view. The entry store's own
\ words (lf-name-count, lf-name-slot, lf-name-field, lf-name-entries-from?) are for
\ the stored mode and for tests that corrupt entries; lf-name-entry-ok? is
\ false under a view.

require ../lib/lib.fs
require ../lib/hash32.fs
require ../lib/htab.fs
require ./diagnostics.fs
require ./compact.fs

64 constant lf-name-default
2048 constant lf-name-byte-capacity   \ the byte pool's first room (it grows)
0 constant lf-name-tag-anon
1 constant lf-name-tag-str
2 constant lf-name-tag-num

\ One entry: kind, prefix ID, then the number or the string's byte offset in
\ lf-name-bytes, then the string length (always 0 for a number), then the
\ name's hash in the index (see "The index" below): a hint, never compared
\ as a name, never audited.
begin-structure /lf-entry
  field: lf-entry-tag
  field: lf-entry-prefix
  field: lf-entry-payload
  field: lf-entry-length
  field: lf-entry-hash
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
\ The bytes and the copy are growable arrays with no fixed limit (plan
\ task 6.2.0), each starting with lf-name-byte-capacity bytes; a string
\ the heap cannot hold is refused as full. Their addresses are valid
\ until they grow: the copy grows only for a query longer than it is
\ (which cannot lie wholly in it), and the bytes only after the copy.
begin-structure /lf-npool
  field: lf-npool-used
end-structure
/lf-npool context-record: lf-name-pool
1 context-slab: lf-name-byte-cells
1 context-slab: lf-name-query-cells
: lf-name-pool-make ( -- )
  lf-name-byte-capacity dup lf-name-byte-cells slab-hold ok?
  swap lf-name-query-cells slab-hold ok? and 0= abort" names: no heap" ;
' lf-name-pool-make context-setup
: lf-name-used ( -- addr ) lf-name-pool lf-npool-used ;
: lf-name-bytes ( -- addr ) 0 lf-name-byte-cells slab-at ;
: lf-name-input-copy ( -- addr ) 0 lf-name-query-cells slab-at ;
: lf-name-byte-room ( -- n ) lf-name-byte-cells slab-capacity ;

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
\ Entry address, in the stored mode; the ID must already be validated.
: lf-name-slot ( id -- addr ) lf-names store-slot ;
\ Numbered field of a valid entry (0 tag, 1 prefix, 2 payload, 3 length);
\ kept for existing callers, new code uses the named fields.
: lf-name-field ( id field# -- value ) cells swap lf-name-slot + @ ;
\ A valid ID's stored hash, under a view (lf-name-digest).
: lf-name-hash ( id -- h ) lf-name-tier name-hash@ ;

\ Count, byte use and generation are in range; checked before addressing.
: lf-name-state-valid? ( -- flag )
  lf-names store-count-valid? lf-name-used @ lf-name-byte-room upto? and ;
\ An ID is allocated now; a reused stale ID is undetectable.
\ The state check covers the store's (store-count-valid?), so the ID is
\ only compared with the count.
: lf-name-stored? ( id -- flag )
  lf-name-state-valid? if 0 lf-name-count @ within else drop false then ;

\ Structural audit of the entry store, guarding later byte reads against
\ corrupted tags, prefixes, offsets and lengths. Checks bounds and that
\ prefixes point backwards; not uniqueness or immutability.
: lf-name-span? ( offset length -- flag )
  over lf-name-used @ upto? if swap lf-name-used @ swap - upto? else 2drop false then ;
: lf-name-num-ok? ( entry -- flag )
  dup lf-entry-payload @ 0< 0= swap lf-entry-length @ 0= and ;
: lf-name-str-ok? ( entry -- flag )
  dup lf-entry-payload @ swap lf-entry-length @ lf-name-span? ;
: lf-name-body-ok? ( entry -- flag )
  dup lf-entry-tag @ case
    lf-name-tag-num of lf-name-num-ok? endof
    lf-name-tag-str of lf-name-str-ok? endof
    nip false swap endcase ;   \ any other kind is invalid; ENDCASE drops the tag
: lf-name-entry-checked? ( id -- flag )
  dup lf-name-slot tuck lf-entry-prefix @ 0 rot within if lf-name-body-ok? else drop false then ;
\ One entry of the entry store; false under a view, whose IDs are not
\ entries (lf-name-part-ok? is the word for either mode).
: lf-name-entry-ok? ( id -- flag )
  lf-name-viewed? if drop false else lf-name-entry-checked? then ;
\ The header (count, byte use, generation: lf-name-state-valid?), the root
\ (all zero), and entries k .. count - 1, for k >= 1 (1: every entry).
: lf-name-sound? ( -- flag )
  lf-name-state-valid? if 0 lf-name-slot lf-name-slot-cells cells-zero? else false then ;
: lf-name-entry-past? ( k i -- k flag ) over + lf-name-entry-checked? ;
: lf-name-entries-from? ( k -- flag )
  lf-name-sound? if lf-name-count @ over - ['] lf-name-entry-past? all? nip
  else drop false then ;

\ The audit kept (ADR 0005 Amendment 1). Entries 1 .. count - 1 of the
\ record passed the audit in its generation, when byte use was used. The
\ next audit checks the header and the root again and then only the
\ entries from there up to today's count; it starts again from entry 1
\ after a reset (the generation moved) or when byte use went down (a
\ rollback or a write), which could leave an audited string outside the
\ bytes in use. An entry this module wrote is never written again, so an
\ entry once audited is not read by later audits: a write into it from
\ outside (a memory fault of other code, or a test) is caught only where
\ a reader checks that entry (lf-name-part-ok?, the index's find below).
begin-structure /lf-naudit
  field: lf-naudit-count
  field: lf-naudit-generation
  field: lf-naudit-used
end-structure
/lf-naudit context-record: lf-name-audit
: lf-name-audit-kept? ( -- flag )
  lf-name-audit dup lf-naudit-generation @ lf-name-generation @ =
  swap lf-naudit-used @ lf-name-used @ upto? and ;
\ The first entry the next audit reads, at least 1 (above the count after
\ a rollback: it then reads none, and keeps the lower count).
: lf-name-audit-from ( -- k )
  lf-name-audit-kept? if lf-name-audit lf-naudit-count @ 1 max else 1 then ;
: lf-name-audited ( -- )
  lf-name-audit lf-name-count @ over lf-naudit-count !
  lf-name-generation @ over lf-naudit-generation ! lf-name-used @ swap lf-naudit-used ! ;
\ A failed audit keeps nothing: the next one reads every entry again.
: lf-name-audit-drop ( -- ) lf-name-audit /lf-naudit erase ;
\ The stored mode's audit of the whole storage: the header, the root and
\ the entries not yet audited.
: lf-name-entries-valid? ( -- flag )
  lf-name-audit-from lf-name-entries-from?
  dup if lf-name-audited else lf-name-audit-drop then ;

\ A string query is the first length bytes of lf-name-input-copy.
: lf-name-query ( length -- addr length ) lf-name-input-copy swap ;
: lf-name-bytes@ ( entry -- addr length )
  dup lf-entry-payload @ lf-name-bytes + swap lf-entry-length @ ;

\ ---------------------------------------------------------------------------
\ The index (ADR 0005 Amendment 1): in the stored mode, a hash table
\ (lib/htab.fs) of entries 1 .. count - 1 by kind, prefix and component,
\ which finds a name in place of a linear search. An entry is made only
\ after a find for it failed, so no two entries are equal, and the index
\ gives the one entry equal to a name: the ID the linear search gave. It
\ follows the store: before a find, the entries a rollback gave back (at
\ or above the count) leave the table by their kept hashes, and a reset
\ empties it. A slot whose entry is at or above the count is passed over.
\ An entry the find reaches that fails its own audit
\ (lf-name-entry-checked?) stops the find, and the name is refused: its
\ bytes are never read. Entries that a raw write of the count exposed
\ (tests) are audited but not listed. The index is full when the table
\ cannot grow (the heap), recorded as the names being full.

\ The name sought: kind, prefix, the number or the query's length, its
\ hash, then the find's slot and whether the table had room for one more.
begin-structure /lf-nsought
  field: lf-nsought-tag
  field: lf-nsought-prefix
  field: lf-nsought-x
  field: lf-nsought-hash
  field: lf-nsought-slot
  field: lf-nsought-ready
end-structure
/lf-nsought context-record: lf-name-sought
: lf-name-sought-tag ( -- tag ) lf-name-sought lf-nsought-tag @ ;
: lf-name-sought-prefix ( -- prefix ) lf-name-sought lf-nsought-prefix @ ;
: lf-name-sought-x ( -- x ) lf-name-sought lf-nsought-x @ ;
: lf-name-sought-str? ( -- flag ) lf-name-sought-tag lf-name-tag-str = ;
\ The hash (lib/hash32.fs): kind, prefix, then the number or the bytes'.
: lf-name-x-hash ( -- h )
  lf-name-sought-x lf-name-sought-str? if lf-name-query hash-bytes then ;
: lf-name-sought-hash ( -- h )
  lf-name-sought-tag hash-fmix lf-name-sought-prefix hash-step lf-name-x-hash hash-step ;
: lf-name-seek! ( prefix x tag -- )
  lf-name-sought tuck lf-nsought-tag ! tuck lf-nsought-x ! lf-nsought-prefix !
  lf-name-sought-hash lf-name-sought lf-nsought-hash ! ;

\ Whether a checked entry is the name sought: the same kind and prefix,
\ then the same number or the same bytes.
: lf-name-head? ( entry -- flag )
  dup lf-entry-tag @ lf-name-sought-tag =
  swap lf-entry-prefix @ lf-name-sought-prefix = and ;
: lf-name-same-bytes? ( entry -- flag )
  lf-name-bytes@ lf-name-sought-x lf-name-query compare 0= ;
: lf-name-same-number? ( entry -- flag ) lf-entry-payload @ lf-name-sought-x = ;
: lf-name-part? ( entry -- flag )
  lf-name-sought-str? if lf-name-same-bytes? else lf-name-same-number? then ;
: lf-name-sought? ( entry -- flag )
  dup lf-name-head? if lf-name-part? else drop false then ;

\ The table's hooks: entry n's kept hash (0 beyond the store's block,
\ where only a slot left from a shrunk store points), and whether entry n
\ is the name sought or stops the find (see above).
: lf-name-entry-hash ( n -- h )
  dup lf-names store-capacity @ u< if lf-name-slot lf-entry-hash @ else drop 0 then ;
: lf-name-rehash ( n htab -- h ) drop lf-name-entry-hash ;
: lf-name-same ( n key htab -- flag )
  2drop dup lf-name-count @ u< 0= if drop false exit then
  dup lf-name-entry-checked? if lf-name-slot lf-name-sought? else drop true then ;
create lf-name-hooks /htab-hooks allot
' lf-name-rehash ' lf-name-same lf-name-hooks htab-hooks!

\ The table, a member of the checker context, and the entries listed in
\ it: 1 .. listed - 1, or fewer (an entry a raw write exposed is not).
\ 16 slots at first; a reset makes a table one large run grew small again.
begin-structure /lf-nindex
  /htab +field lf-nindex-table
  field: lf-nindex-listed
end-structure
/lf-nindex context-record: lf-name-index
: lf-name-table ( -- htab ) lf-name-index lf-nindex-table ;
: lf-name-listed ( -- addr ) lf-name-index lf-nindex-listed ;
: lf-name-table-make ( -- )
  4 lf-name-hooks lf-name-table htab-init drop 1 lf-name-listed ! ;
' lf-name-table-make context-setup
:noname ( -- ) lf-name-table htab-free ; context-teardown
: lf-name-table-empty ( -- )
  lf-name-table ['] lf-name-table-make htab-renew 1 lf-name-listed ! ;

\ Before a find: the entries a rollback gave back leave the table.
: lf-name-unlist ( n -- ) dup lf-name-entry-hash lf-name-table htab-remove drop ;
: lf-name-index-sync ( -- )
  lf-name-count @ lf-name-listed @ over max swap ?do i lf-name-unlist loop
  lf-name-count @ lf-name-listed @ min lf-name-listed ! ;
\ Synchronised and ready for one more entry (the outcome kept with the
\ name sought): whether the table can be read (no heap may leave none).
: lf-name-index-ready ( -- flag )
  lf-name-index-sync lf-name-table htab-ready lf-name-sought lf-nsought-ready !
  lf-name-table htab-live? ;
: lf-name-index-room? ( -- flag ) lf-name-sought lf-nsought-ready @ ok? ;
: lf-name-site ( -- site ) c" names lf-name-intern" ;
: lf-name-index-refused ( -- false )
  lf-name-table htab-count 0 lf-name-site lf-diag-names-full lf-diag-note false ;
\ The entry found: its ID, or false when it failed its audit.
: lf-name-found ( n -- id true | false ) dup lf-name-entry-checked? dup 0= if nip then ;
\ The name sought: its ID and true, then true; or false (refused), then
\ true; or false alone when it is absent (its slot kept for lf-name-list).
: lf-name-lookup ( -- id true true | false true | false )
  lf-name-index-ready 0= if lf-name-index-refused true exit then
  lf-name-sought dup lf-nsought-hash @ lf-name-table htab-find
  if lf-name-found true else lf-name-sought lf-nsought-slot ! false then ;
\ A new entry into the slot its lookup found, with its hash.
: lf-name-list ( id -- id )
  lf-name-sought lf-nsought-hash @ over lf-name-slot lf-entry-hash !
  dup lf-name-sought lf-nsought-slot @ lf-name-table htab-put
  lf-name-count @ lf-name-listed ! ;

\ Appending; callers have checked validity, absence and room. The store's
\ identities are issued but unused: names are compared by content.
: lf-name-room? ( -- flag ) lf-names store-ready drop lf-names store-open? ;
: lf-name-byte-room? ( length -- flag )
  lf-name-used @ + lf-name-byte-cells slab-hold ok? ;
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
\ A full index is recorded as names full too (lf-name-index-refused).
: lf-name-refused ( -- false )
  lf-names lf-name-site lf-diag-names-full lf-diag-store false ;
: lf-name-bytes-refused ( length -- false )
  lf-name-used @ + lf-name-byte-room lf-name-site lf-diag-name-bytes-full lf-diag-note
  false ;
: lf-name-str-refused ( length -- false )
  lf-name-room? if lf-name-bytes-refused else drop lf-name-refused then ;
\ The name sought, absent, made by xt ( prefix x -- id ) and listed, when
\ the table had room for it.
: lf-name-append ( xt -- id true | false )
  lf-name-index-room? 0= if drop lf-name-index-refused exit then
  lf-name-sought-prefix swap lf-name-sought-x swap execute lf-name-list true ;
: lf-name-intern-num ( prefix number -- id true | false )
  lf-name-tag-num lf-name-seek! lf-name-lookup if exit then
  lf-name-room? if ['] lf-name-add-num lf-name-append else lf-name-refused then ;
: lf-name-intern-str ( prefix length -- id true | false )
  lf-name-tag-str lf-name-seek! lf-name-lookup if exit then
  lf-name-room? lf-name-sought-x lf-name-byte-room? and
  if ['] lf-name-add-str lf-name-append else lf-name-sought-x lf-name-str-refused then ;

\ ---------------------------------------------------------------------------
\ The stored mode's words: the entry store.
: lf-name-entry-tag ( id -- tag ) lf-name-slot lf-entry-tag @ ;
: lf-name-entry-prefix ( id -- prefix ) lf-name-slot lf-entry-prefix @ ;
: lf-name-entry-text ( id -- c-addr u ) lf-name-slot lf-name-bytes@ ;
: lf-name-entry-payload ( id -- n ) lf-name-slot lf-entry-payload @ ;

\ The viewed mode's words: the scratch tier over the input tier. Every
\ name there was checked when it was made, so a component and the whole
\ storage need no audit. A name the scratch tier cannot make is false:
\ full is recorded as a diagnostic (the names under the view), invalid
\ is not.
: lf-name-tier-tag ( id -- tag ) lf-name-tier name-tag@ ;
: lf-name-tier-prefix ( id -- prefix ) lf-name-tier name-prefix@ ;
: lf-name-tier-text ( id -- c-addr u ) lf-name-tier name-text@ ;
: lf-name-tier-payload ( id -- n ) lf-name-tier name-number@ ;
: lf-name-tier-valid? ( id -- flag ) lf-name-tier name-valid? ;
: lf-name-checked ( id -- true ) drop true ;
: lf-name-all-checked ( -- true ) true ;
: lf-name-no-scratch ( -- ) ;
: lf-name-numbers ( -- n ) lf-name-tier tier-names cons-numbers ;
: lf-name-tier-full ( -- )
  lf-name-numbers 0 lf-name-site lf-diag-names-full lf-diag-note ;
: lf-name-made ( n outcome -- id true | false )
  dup ok? if drop true exit then
  outcome-full = if lf-name-tier-full then drop false ;
: lf-name-viewed-num ( prefix number -- id true | false )
  lf-name-tier name-num lf-name-made ;
\ The copy of the query, never the caller's text, goes to the scratch
\ tier, whose byte slab may move while it makes room.
: lf-name-viewed-str ( prefix length -- id true | false )
  lf-name-query lf-name-tier name-str lf-name-made ;
: lf-name-scratch-reset ( -- ) lf-name-tier tier-reset drop ;

\ ---------------------------------------------------------------------------
\ The two rows (see the header): one execution token per operation.
begin-structure /lf-nops
  field: lf-nops-tag        \ ( id -- tag ) of a valid ID
  field: lf-nops-prefix     \ ( id -- prefix ) of a valid ID
  field: lf-nops-text       \ ( id -- c-addr u ) of a valid string name
  field: lf-nops-payload    \ ( id -- n ) of a valid numeric name
  field: lf-nops-valid      \ ( id -- flag ) the ID is a name now
  field: lf-nops-part-ok    \ ( id -- flag ) a valid ID's component is well formed
  field: lf-nops-storage    \ ( -- flag ) every name is well formed
  field: lf-nops-num        \ ( prefix number -- id true | false ), checked arguments
  field: lf-nops-str        \ ( prefix length -- id true | false ), the query copied
  field: lf-nops-clear      \ ( -- ) the reset's part of the mode
end-structure
create lf-name-stored-ops /lf-nops allot
create lf-name-viewed-ops /lf-nops allot
: lf-nops! ( stored-xt viewed-xt field-xt -- )
  >r lf-name-viewed-ops r@ execute ! lf-name-stored-ops r> execute ! ;
' lf-name-entry-tag ' lf-name-tier-tag ' lf-nops-tag lf-nops!
' lf-name-entry-prefix ' lf-name-tier-prefix ' lf-nops-prefix lf-nops!
' lf-name-entry-text ' lf-name-tier-text ' lf-nops-text lf-nops!
' lf-name-entry-payload ' lf-name-tier-payload ' lf-nops-payload lf-nops!
' lf-name-stored? ' lf-name-tier-valid? ' lf-nops-valid lf-nops!
' lf-name-entry-checked? ' lf-name-checked ' lf-nops-part-ok lf-nops!
' lf-name-entries-valid? ' lf-name-all-checked ' lf-nops-storage lf-nops!
' lf-name-intern-num ' lf-name-viewed-num ' lf-nops-num lf-nops!
' lf-name-intern-str ' lf-name-viewed-str ' lf-nops-str lf-nops!
' lf-name-no-scratch ' lf-name-scratch-reset ' lf-nops-clear lf-nops!
: lf-name-ops ( -- ops )
  lf-name-viewed? if lf-name-viewed-ops else lf-name-stored-ops then ;

\ Kind and prefix of a valid ID.
: lf-name-tag@ ( id -- tag ) lf-name-ops lf-nops-tag @ execute ;
: lf-name-prefix@ ( id -- prefix ) lf-name-ops lf-nops-prefix @ execute ;
\ The component of a name: the bytes of a string component, the number of
\ a numeric one. Unchecked: the ID is valid and of that kind (lf-name-tag@),
\ and the bytes are read before the name store changes. Under a view, the
\ bytes of an input name never move; a scratch name's do when the scratch
\ tier grows.
: lf-name-text ( id -- c-addr u ) lf-name-ops lf-nops-text @ execute ;
: lf-name-payload ( id -- n ) lf-name-ops lf-nops-payload @ execute ;
: lf-name-valid? ( id -- flag ) lf-name-ops lf-nops-valid @ execute ;
\ A valid ID's own component is well formed: audited from its entry, or
\ checked when it was made under a view. The prefix chain of a valid ID
\ is then walked with lf-name-prefix@, one component at a time.
: lf-name-part-ok? ( id -- flag ) lf-name-ops lf-nops-part-ok @ execute ;
\ The whole storage is well formed: the entry store's audit, which reads
\ its header and root and every entry made since its last pass (ADR 0005
\ Amendment 1); under a view every name was checked when it was made.
: lf-name-storage-valid? ( -- flag ) lf-name-ops lf-nops-storage @ execute ;
\ Whether the valid ID's own component is a string, or a number (the
\ anonymous name is neither); whether it is the anonymous name.
: lf-name-str? ( id -- flag ) lf-name-tag@ lf-name-tag-str = ;
: lf-name-num? ( id -- flag ) lf-name-tag@ lf-name-tag-num = ;
: lf-name-anon? ( id -- flag ) lf-name-tag@ lf-name-tag-anon = ;
\ Whether an ID kept with the generation it was made in still names that
\ name: the store has not been reset since, and the ID is valid.
: lf-name-current? ( id generation -- flag )
  lf-name-generation @ = swap lf-name-valid? and ;
\ Whether the valid ID's own component is the string c-addr u (a numeric
\ component never is); the number of components of a valid ID (0 for the
\ anonymous name).
: lf-name-str-is? ( id c-addr u -- flag )
  rot dup lf-name-str? if lf-name-text compare 0= else drop 2drop false then ;
\ Whether the valid ID is the one-component name c-addr u: its own
\ component that string, its prefix the anonymous name (as Lean matches
\ Nat, Bool or eagerReduce by name).
: lf-name-top? ( id c-addr u -- flag )
  2 pick lf-name-prefix@ lf-name-anon? if lf-name-str-is? else 2drop drop false then ;
: lf-name-depth ( id -- n ) 0 begin over while 1+ swap lf-name-prefix@ swap repeat nip ;
\ The prefix k components up (k at most the ID's depth); a valid ID's
\ first component, the ancestor whose prefix is the anonymous name (the
\ anonymous name is its own).
: lf-name-ancestor ( id k -- id' ) 0 ?do lf-name-prefix@ loop ;
: lf-name-root ( id -- id' ) begin dup lf-name-prefix@ ?dup while nip repeat ;

\ Reset to the anonymous name alone and advance the generation; saturation
\ poisons the table rather than wrapping (see store-clear). Under a view,
\ the scratch tier is emptied.
: lf-name-reset ( -- )
  lf-name-ops lf-nops-clear @ execute 0 lf-name-slot /lf-entry erase 0 lf-name-used !
  lf-names store-clear lf-name-table-empty ;

\ Attach the sealed input tier as this context's names, emptying the
\ scratch tier and advancing the generation: ok, or the outcome of making
\ the scratch tier, which is freed again (no view then, and the names are
\ reset all the same, so every earlier ID is stale). Detach: back to the
\ entry store, reset.
: lf-name-viewing ( input -- ) lf-name-view lf-nview-input ! lf-name-reset ;
: lf-name-unview ( -- ) lf-name-tier tier-free 0 lf-name-view lf-nview-input ! lf-name-reset ;
: lf-name-attach ( input -- outcome )
  lf-name-unview dup lf-name-tier tier-extend dup ok?
  if drop lf-name-viewing outcome-ok else nip lf-name-tier tier-free then ;
\ Detaching also runs lf-name-detach-hook ( -- ), which import/feed.fs
\ sets while loading to end a term view of the same stage (core/terms.fs,
\ compact-store plan step S5), so that a caller that detaches the names
\ before freeing the stage leaves nothing that reads it.
defer lf-name-detach-hook ( -- )
:noname ( -- ) ; is lf-name-detach-hook
: lf-name-detach ( -- ) lf-name-unview lf-name-detach-hook ;

\ Intern a numeric component; invalid input changes nothing.
: lf-name-num-args? ( prefix number -- flag )
  0< 0= swap lf-name-valid? and lf-name-storage-valid? and ;
: lf-name-num ( prefix number -- id true | false )
  2dup lf-name-num-args? 0= if 2drop false exit then lf-name-ops lf-nops-num @ execute ;

\ Intern a byte-string component. The input is copied before anything else
\ changes, so it may overlap any buffer here; it must stay readable during
\ the copy. Invalid input changes nothing.
: lf-name-query-room? ( length -- flag )
  dup 0< if drop false else lf-name-query-cells slab-hold ok? then ;
: lf-name-str-args? ( prefix length -- flag )
  lf-name-query-room? swap lf-name-valid? and lf-name-storage-valid? and ;
: lf-name-copy-in ( addr length -- length ) tuck lf-name-input-copy swap move ;
: lf-name-copied-str ( prefix length -- id true | false )
  lf-name-ops lf-nops-str @ execute ;
: lf-name-str ( prefix addr length -- id true | false )
  >r over r@ lf-name-str-args? r> swap
  if lf-name-copy-in lf-name-copied-str else 2drop drop false then ;

\ A valid ID's own component put on base, interned; the last t
\ components of name put on base, from the first of them (Lean's
\ operator+ over a name's tail; t at most name's depth). False when the
\ store refuses one; the components put before it stay interned.
: lf-name-put ( base part -- name true | false )
  dup lf-name-str? if lf-name-text lf-name-str else lf-name-payload lf-name-num then ;
: lf-name-graft ( name t base -- name' true | false )
  begin over while
    >r 1- 2dup lf-name-ancestor r> swap lf-name-put 0= if 2drop false exit then
  repeat nip nip true ;

\ Every context starts with the anonymous name alone.
' lf-name-reset context-setup

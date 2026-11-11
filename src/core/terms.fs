\ Bounded storage for the syntax of a small Lean expression subset: Sort,
\ bound variable, application, lambda and Pi nodes. Untrusted; not a kernel
\ API. Constructors validate indices and payload ranges only; they do not
\ check scope, types, universe semantics, declarations or proofs.
\ Each term is a record of four 32-bit fields (lib/u32.fs; ADR 0016 C1,
\ compact-store plan step S3): its tag, its first and second fields, and
\ its data word, in a heap store (lib/store.fs) that grows up to a
\ capacity, a setting of each context (ADR 0016 C5, C9 step 3; plan task
\ 3.3.1): lf-term-capacity reads it, lf-term-capacity! sets it, and a new
\ context starts with lf-term-default records. A field holds 0 .. 2^32-1:
\ a larger or negative value is refused as a full store (C1's limits),
\ and so are more than 2^32-1 records. Running out is full, never
\ accepted. Children must already exist, so terms are acyclic DAGs.
\ Per-term side data of other modules lives in columns of the group
\ lf-term-columns (lib/store-columns.fs), which grow with the store.
\
\ Hash-consing (ADR 0016 C4; plan step S3). Equal records are one node:
\ lf-term-add looks the record (tag, first, second) up in a hash table of
\ the context (lib/htab.fs: open addressing, a slot holds an index plus
\ one, a hash is only a hint and an entry is equal only when its record
\ is, field by field) and gives back the equal node it finds, else
\ appends a new one and enters it. So a node rebuilt equal to an existing
\ one is that older node, with its older identity. Leaves whose meaning
\ is more than their fields are never shared: a module that makes such a
\ leaf names its tag with lf-term-unshare while loading (symbolic Sorts
\ and constants carry stamps, free variables their local-context entry).
\ Hash-consing only saves room and time: a missing entry costs a
\ duplicate, never a verdict, and no answer depends on it (C8). A
\ context may turn it off (lf-term-sharing!), as the authoring words do,
\ which keep side data per node. A rollback (lf-term-rollback, or a
\ scratch mark: core/scratch-marks.fs) takes the entries of the records
\ it gives back out of the table by Knuth's Algorithm R, as lib/cons.fs
\ does; a reset empties the table.
\
\ The data word (ADR 0016 C1) is computed when a node is made, from its
\ fields and its children's data words: bits 0-19 the loose bound
\ variable range (1 + the largest loose index, or 0: Lean's
\ loose_bvar_range), bit 20 set when a universe parameter occurs
\ (has_param_univ), bit 21 when a free variable occurs (has_fvar), bits
\ 22-31 the depth (a leaf 0, a node 1 + its deepest child), capped at
\ 1023. A range of all ones means no data: a leaf whose facts the term
\ store cannot know (its tag is unknown here, or a level or reference it
\ names is not valid when it is made), a range of 2^20 - 1 or more, and
\ every node above one. Leaves other than bound variables get their data
\ from the hook lf-term-leaf-data, which core/constant-term-boundary.fs
\ sets while loading.
\
\ Terms have no fixed depth (plan task 6.2.0): every pass keeps its
\ pending work on a stack in the heap that grows with the depth (walks,
\ frames, binder scopes); lf-walk-room is only the room a context's walk
\ starts with. A stack the heap cannot grow ends a pass full, never
\ accepted.
\ State: the store header lf-terms, the hash table lf-term-table, the
\ candidate record lf-term-key and the switch lf-term-share-off, members
\ of the checker context (lib/context.fs) whose blocks are on the heap,
\ freed by their teardown words, so each context has its own terms;
\ single-threaded within one context. The set of unshared tags and the
\ leaf-data hook are fixed while loading and read-only afterwards. A
\ reset invalidates every index, and a reused index cannot be told from
\ a stale one; identities (8-byte birth serials) never repeat and are
\ what handles check. Indices and identities mean something only in
\ their own context. No host address or record layout is a portable
\ serialization format.

require ../lib/lib.fs
require ../lib/u32.fs
require ../lib/hash32.fs
require ../lib/htab.fs
require ./diagnostics.fs
require ../lib/store-columns.fs

64 constant lf-term-default
64 constant lf-walk-room     \ a walk's first room, in items
1 constant lf-tag-sort
2 constant lf-tag-bvar
3 constant lf-tag-app
4 constant lf-tag-lam
5 constant lf-tag-pi

\ A record: the tag, the first and second fields, the data word, each a
\ 32-bit field read and written only through u32@ and u32! (C7).
4 u32s constant /lf-term
1 u32s constant lf-term-first-at
2 u32s constant lf-term-second-at
3 u32s constant lf-term-data-at

store-header context-record: lf-terms
: lf-terms-make ( -- )
  lf-term-default /lf-term 0 lf-terms store-heap-init ok? 0= abort" terms: no heap" ;
' lf-terms-make context-setup
:noname ( -- ) lf-terms store-heap-free ; context-teardown
' lf-terms column-group: lf-term-columns
:noname ( -- ) lf-term-columns columns-setup ; context-setup
:noname ( -- ) lf-term-columns columns-free ; context-teardown
\ The capacity setting of this context: most records the store may hold.
: lf-term-capacity ( -- n ) lf-terms store-limit @ ;
\ Set it, at least the records in use: ok; invalid for a smaller or
\ unsound one; full when shrinking the block finds no heap.
: lf-term-capacity! ( n -- outcome ) lf-terms store-limit! ;

\ The store's fields under their established names. Other modules roll a
\ failed transaction back through marks (core/scratch-marks.fs), never by
\ setting the count; tests corrupt these cells on purpose to check that
\ every operation fails closed.
: lf-term-count ( -- addr ) lf-terms store-count ;
: lf-term-generation ( -- addr ) lf-terms store-generation ;
: lf-term-serial ( -- addr ) lf-terms store-serial ;
: lf-term-identities ( -- addr ) lf-terms store-identities ;
\ Record address; the index must already be validated.
: lf-term-slot ( index -- addr ) lf-terms store-slot ;

\ Checked roots, range-checked reads (compact-store plan step S2; ADR
\ 0016 C8). The whole header (shape, seal, generation, count) is checked
\ once where a pass takes a term from outside: lf-term-count-valid?, or
\ lf-term-root? (lf-term-pair-valid? for two) for its root, or a handle
\ (generation-handles.fs). Every
\ read after that (lf-term-valid?, lf-term-identity, lf-term-read and the
\ walks' visits) checks only that the index is allocated (store-at?), so
\ a corrupted shape, seal or generation is refused at the root, never
\ found by a read; a corrupted count still refuses every read.
: lf-term-count-valid? ( -- flag ) lf-terms store-count-valid? ;
: lf-term-root? ( index -- flag ) lf-terms store-valid? ;
: lf-term-valid? ( index -- flag ) lf-terms store-at? ;
\ A live node's identity; identities never roll back and never wrap.
: lf-term-identity ( index -- identity true | false )
  dup lf-term-valid? if lf-terms store-identity @ true else drop false then ;

\ Read a node's tag and fields. An index that is not allocated returns
\ only false and no memory is read (the header is the root's to check).
: lf-term-fields@ ( addr -- tag first second )
  dup u32@ over lf-term-first-at + u32@ rot lf-term-second-at + u32@ ;
: lf-term-read ( index -- tag first second true | false )
  dup lf-term-valid? if lf-term-slot lf-term-fields@ true else drop false then ;
\ One field of a node. Unchecked: the index must already be validated,
\ for instance by an earlier lf-term-read of the same node, under a
\ checked root; no field read checks the header.
: lf-term-tag@ ( index -- tag ) lf-term-slot u32@ ;
: lf-term-first@ ( index -- first ) lf-term-slot lf-term-first-at + u32@ ;
: lf-term-second@ ( index -- second ) lf-term-slot lf-term-second-at + u32@ ;

\ Visiting a node of a walk (lib/walk.fs's walk-visit, for the term
\ records): read the current node, then dispatch on its tag with xt
\ ( first second walk tag -- outcome ); an unreadable node is invalid.
: lf-term-walk-read ( walk -- first second walk tag true | false )
  dup walk-node @ lf-term-read if 2swap true else drop false then ;
: lf-term-visit ( walk xt -- outcome )
  >r lf-term-walk-read if r> execute else r> drop outcome-invalid then ;

\ ---------------------------------------------------------------------------
\ The data word (see the header).
1 20 lshift constant lf-data-ranges   \ the ranges a data word holds
lf-data-ranges 1- constant lf-data-unknown   \ no data: the range all ones
: lf-data-loose ( data -- range ) lf-data-ranges 1- and ;
: lf-data-params? ( data -- flag ) lf-data-ranges and 0<> ;
: lf-data-fvar? ( data -- flag ) lf-data-ranges 2* and 0<> ;
: lf-data-depth ( data -- depth ) 22 rshift 1023 and ;
: lf-data-known? ( data -- flag ) lf-data-loose lf-data-unknown <> ;
\ The data word of a range below lf-data-unknown and two flags, depth 0.
: lf-data ( range params? fvar? -- data )
  lf-data-ranges 2* and swap lf-data-ranges and or or ;
\ A bound variable's: its index plus one, when that is below the
\ unknown range.
: lf-data-bvar ( index -- data )
  1+ dup lf-data-unknown u< 0= if drop lf-data-unknown then ;
\ A node's from its children's: the larger range (a binder's body counts
\ one less), the flags of either, one more than the deeper depth.
lf-data-ranges 3 * constant lf-data-flags
: lf-data-loose2 ( d1 d2 binder? -- range )
  >r lf-data-loose swap lf-data-loose swap r> if 1- 0 max then max ;
: lf-data-deeper ( d1 d2 -- bits )
  lf-data-depth swap lf-data-depth max 1+ 1023 min 22 lshift ;
: lf-data-both ( d1 d2 -- bits ) 2dup or lf-data-flags and -rot lf-data-deeper or ;
: lf-data-pair ( d1 d2 binder? -- data )
  >r 2dup lf-data-known? swap lf-data-known? and 0=
  if 2drop r> drop lf-data-unknown exit then
  2dup lf-data-both -rot r> lf-data-loose2 or ;
\ A node's data word as made. Unchecked: the index is valid.
: lf-term-data-word ( index -- data ) lf-term-slot lf-term-data-at + u32@ ;
\ Lean's cached node data, or false for a node without (see the header)
\ or an index that is not allocated.
: lf-term-data@ ( node -- data true | false )
  dup lf-term-valid? 0= if drop false exit then
  lf-term-data-word dup lf-data-known? dup 0= if nip then ;
\ Data of a leaf (tag first second -- data): bound variables here; the
\ hook knows the other leaves of the checker (set while loading by
\ core/constant-term-boundary.fs).
: lf-bvar-data ( first second -- data ) if drop lf-data-unknown else lf-data-bvar then ;
: lf-leaf-data-plain ( tag first second -- data )
  rot lf-tag-bvar = if lf-bvar-data else 2drop lf-data-unknown then ;
defer lf-term-leaf-data ( tag first second -- data )
' lf-leaf-data-plain is lf-term-leaf-data

\ ---------------------------------------------------------------------------
\ Hash-consing (see the header).
/htab context-record: lf-term-table
3 cells context-record: lf-term-key        \ the record sought: tag first second
1 cells context-record: lf-term-share-off   \ true when this context does not share
\ Tags whose leaves are never shared, a bit each; set while loading.
variable lf-term-unshared-tags   0 lf-term-unshared-tags !
: lf-term-tag-bit ( tag -- mask ) 1 swap 31 min lshift ;
: lf-term-unshare ( tag -- )
  lf-term-tag-bit lf-term-unshared-tags @ or lf-term-unshared-tags ! ;
: lf-term-shared-tag? ( tag -- flag ) lf-term-tag-bit lf-term-unshared-tags @ and 0= ;
\ The switch: sharing is on in a new context.
: lf-term-sharing? ( -- flag ) lf-term-share-off @ 0= ;
: lf-term-sharing! ( flag -- ) 0= lf-term-share-off ! ;

\ The table's hooks: the hash of record n from its fields, and whether
\ live record n equals the record sought.
: lf-term-hash ( tag first second -- h ) rot hash-fmix rot hash-step swap hash-step ;
: lf-term-rehash ( n htab -- h ) drop lf-term-slot lf-term-fields@ lf-term-hash ;
: lf-term-key= ( tag first second key -- flag )
  >r r@ 2 cells + @ = swap r@ cell+ @ = and swap r> @ = and ;
: lf-term-same ( n key htab -- flag )
  drop over lf-term-valid? 0= if 2drop false exit then
  >r lf-term-slot lf-term-fields@ r> lf-term-key= ;
create lf-term-hooks /htab-hooks allot
' lf-term-rehash ' lf-term-same lf-term-hooks htab-hooks!
\ A context's table: 16 slots at first, freed with the context. A table
\ that has grown large goes back to 16 slots when the store is reset, so
\ a reset costs little whatever an earlier run needed.
1024 constant lf-term-table-small
: lf-term-table-make ( -- ) 4 lf-term-hooks lf-term-table htab-init drop ;
' lf-term-table-make context-setup
:noname ( -- ) lf-term-table htab-free ; context-teardown
: lf-term-table-empty ( -- )
  lf-term-table dup htab-live? if dup htab-slots lf-term-table-small <= else false then
  if htab-clear else htab-free lf-term-table-make then ;

\ Room in the table for n entries without doubling (the feed sizes it
\ from the stage's counts, ADR 0016 C9); a table the heap cannot make
\ that large only costs time.
: lf-term-log2 ( n -- log2 ) 0 swap 1- begin ?dup while 1 rshift swap 1+ swap repeat ;
: lf-term-table-room ( n -- ) 4 * 3 / 1+ lf-term-log2 lf-term-table htab-presize drop ;

\ Taking records out of the table: entry index, if it is there (a record
\ made while sharing was off, or that the table could not take, is not),
\ and every record from count up to the store's count.
: lf-term-forget ( index -- )
  dup lf-term-slot lf-term-fields@ lf-term-hash lf-term-table htab-remove drop ;
: lf-term-unlist ( count -- )
  lf-term-table htab-live? 0= if drop exit then
  lf-term-count @ swap ?do
    i lf-term-tag@ lf-term-shared-tag? if i lf-term-forget then
  loop ;

\ Empty the store and its table, and advance the store's generation (see
\ store-clear).
: lf-term-reset ( -- ) lf-terms store-clear lf-term-table-empty ;
\ Roll the store back to a mark of it (lib/store.fs's store-mark): ok,
\ the records made since and their table entries given back; or invalid
\ with nothing changed for a mark that store-rollback refuses.
: lf-term-rollback ( mark -- outcome )
  dup lf-terms store-mark-valid? if dup mark-count @ lf-term-unlist then
  lf-terms store-rollback ;

\ ---------------------------------------------------------------------------
\ Making nodes. Append a node whose tag and fields the caller validated,
\ first growing the store and its columns when every record is in use. A
\ field outside 0 .. 2^32-1, an invalid count, a full store (at its
\ capacity, at 2^32-1 records, or no heap) or a spent serial returns
\ false, changes nothing and is recorded as a diagnostic.
: lf-term-site ( -- site ) c" terms lf-term-add" ;
: lf-term-refused ( -- false )
  lf-terms lf-term-site lf-diag-terms-full lf-diag-store false ;
1 cells context-record: lf-term-covered   \ capacity the columns last covered
\ The usual case first: a free record and columns that cover the store.
: lf-term-steady? ( -- flag )
  lf-terms dup store-filled? 0= swap store-capacity @ lf-term-covered @ = and ;
: lf-term-room? ( -- flag )
  lf-term-steady? if true exit then
  lf-terms store-ready ok? if lf-term-covered lf-term-columns columns-ready else false then ;
: lf-term-u32? ( x -- flag ) u32-mask u> 0= ;
: lf-term-fits? ( first second -- flag ) lf-term-u32? swap lf-term-u32? and ;
\ A field beyond 32 bits is full, the value and the largest field noted.
: lf-term-too-wide ( first second -- false )
  dup lf-term-u32? if drop else nip then u32-mask lf-term-site lf-diag-terms-full
  lf-diag-note false ;
\ At most 2^32 - 2 records, so that a table slot holds every index plus
\ one (ADR 0016 C4).
: lf-term-numbered? ( -- flag ) lf-term-count @ u32-mask 1- u< ;
: lf-term-binary-tag? ( tag -- flag ) lf-tag-app lf-tag-pi 1+ within ;
\ Data of a child; a child that is not allocated (a raw caller's) has none.
: lf-term-child-data ( index -- data )
  dup lf-term-valid? if lf-term-data-word else drop lf-data-unknown then ;
: lf-term-data-of ( tag first second -- data )
  2 pick lf-term-binary-tag? 0= if lf-term-leaf-data exit then
  lf-term-child-data swap lf-term-child-data swap rot lf-tag-app <> lf-data-pair ;
: lf-term-store! ( tag first second data addr -- )
  tuck lf-term-data-at + u32! tuck lf-term-second-at + u32!
  tuck lf-term-first-at + u32! u32! ;
: lf-term-new ( tag first second data -- index true | false )
  lf-terms store-new-slot 0= if 2drop 2drop lf-term-refused exit then
  >r lf-term-store! r> true ;
: lf-term-append ( tag first second -- index true | false )
  2 pick 2 pick 2 pick lf-term-data-of lf-term-new ;
\ Hash-consed: the equal node, or a new node entered at the empty slot
\ the find gave (nothing changes the table in between). A table that
\ cannot grow (no heap) only costs sharing.
: lf-term-key! ( tag first second -- )
  lf-term-key 2 cells + ! lf-term-key cell+ ! lf-term-key ! ;
: lf-term-key@ ( -- tag first second )
  lf-term-key @ lf-term-key cell+ @ lf-term-key 2 cells + @ ;
: lf-term-find ( tag first second -- n true | i false )
  2 pick 2 pick 2 pick lf-term-hash >r lf-term-key!
  lf-term-key r> lf-term-table htab-find ;
: lf-term-enter ( i index true | i false -- index true | false )
  if tuck swap lf-term-table htab-put true else drop false then ;
\ An equal node found is given only where an allocation would be allowed
\ (store-open?: a valid store with room and serials, and the test hook of
\ lib/store.fs), so a store that would refuse a new node refuses alike.
: lf-term-found ( n -- n true | false )
  lf-terms store-open? if true else drop lf-term-refused then ;
: lf-term-cons ( tag first second -- index true | false )
  lf-term-table htab-ready ok? 0= if lf-term-append exit then
  lf-term-find if lf-term-found exit then lf-term-key@ lf-term-append lf-term-enter ;
: lf-term-shares? ( tag -- flag ) lf-term-shared-tag? lf-term-sharing? and ;
: lf-term-add ( tag first second -- index true | false )
  2dup lf-term-fits? 0= if lf-term-too-wide nip exit then
  lf-term-room? lf-term-numbered? and 0= if 2drop drop lf-term-refused exit then
  2 pick lf-term-shares? if lf-term-cons else lf-term-append then ;

\ Leaves carry a nonnegative payload: a concrete universe level for Sort, a
\ de Bruijn index for a bound variable. Scope and typing are not checked.
\ Any other tag is refused, so a leaf can never hold a dangling child.
: lf-term-leaf-tag? ( tag -- flag ) lf-tag-sort lf-tag-bvar 1+ within ;
: lf-term-leaf ( payload tag -- index true | false )
  over 0< over lf-term-leaf-tag? 0= or if 2drop false else swap 0 lf-term-add then ;
: lf-term-sort ( level -- index true | false ) lf-tag-sort lf-term-leaf ;
: lf-term-bvar ( index -- index true | false ) lf-tag-bvar lf-term-leaf ;

\ Binary nodes: an application, lambda or Pi over two existing children. An
\ invalid tag, an invalid child or a failed allocation changes nothing. The
\ tag ranges rely on the tags being consecutive, checked here at load time.
lf-tag-bvar lf-tag-sort 1+ = lf-tag-lam lf-tag-app 1+ = and lf-tag-pi lf-tag-lam 1+ = and
0= [if] .( terms.fs: term tags must be consecutive) cr abort [then]
\ Two checked roots with one header check (and a new node's children).
: lf-term-pair-valid? ( left right -- flag ) lf-terms store-pair-valid? ;
: lf-term-binary ( left right tag -- index true | false )
  >r 2dup lf-term-pair-valid? r@ lf-term-binary-tag? and
  if r> -rot lf-term-add else r> drop 2drop false then ;
\ Application: function, then argument.
: lf-term-app ( function argument -- index true | false ) lf-tag-app lf-term-binary ;
\ Lambda: binder type annotation, then body. The body is not scope-checked.
: lf-term-lam ( annotation body -- index true | false ) lf-tag-lam lf-term-binary ;
\ Dependent function type: domain, then body. Nothing is typed.
: lf-term-pi ( domain body -- index true | false ) lf-tag-pi lf-term-binary ;

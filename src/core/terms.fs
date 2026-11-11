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
\ leaf names its tag with lf-term-unshare while loading (free variables:
\ their local-context entry). Symbolic Sorts and constants, whose stamps
\ say more than their fields, are shared only while those stamps hold
\ (the hook lf-term-reusable?, compact-store plan step S4).
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
\
\ The input view (compact-store plan step S5; ADR 0016 C3). A context
\ may read a sealed compact input tier (core/compact.fs, filled by
\ import/stage.fs) in place: lf-term-attach makes the tier's expressions
\ the first term numbers, 0 .. lf-term-base - 1, each the number the
\ stage gave it, and the store's own records follow them, record r being
\ term lf-term-base + r. Every reader below takes a term number and reads
\ an input node from the tier's 16-byte record (C1), its tag translated
\ to the checker's: a bound variable, application, lambda or Pi (binder
\ name and information ignored, as Lean's kernel ignores them) with the
\ record's own fields; a Sort, constant or literal with the fields the
\ importer gave it in the view's leaf table (lf-term-input-leaf: the
\ level, reference or literal it became in this context, and the stamp a
\ symbolic Sort or constant carries, generation-handles.fs); any other
\ kind (a let, projection, metadata or free variable, a let's body
\ record) is no term of the view, so a node above one is copied into the
\ store instead (import/feed.fs). An input node is sealed: never rolled
\ back or reset, its data word the tier's (computed when it was staged,
\ C8, the same facts as this store's), and its identity is the negative
\ number invert index, which no birth serial is. Making a node equal to
\ an input node gives that node (lf-term-add finds an application or
\ bound variable in the tier's table, a Sort or constant in the leaf
\ table), so equal terms are one number across the two parts. Without a
\ view lf-term-base is 0 and everything is as before. The tier must
\ outlive the view: lf-term-detach (or freeing the context) first.
\
\ State: the store header lf-terms, the hash table lf-term-table, the
\ candidate record lf-term-key, the switch lf-term-share-off and the view
\ record lf-term-view, members
\ of the checker context (lib/context.fs) whose blocks are on the heap,
\ freed by their teardown words, so each context has its own terms;
\ single-threaded within one context. The set of unshared tags, the
\ input tag table and the
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
require ../lib/slab.fs
require ../lib/cons.fs
require ./diagnostics.fs
require ./compact.fs
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
\ every operation fails closed. Under an input view (see the header) the
\ count, marks and capacity are the store's own records', and term
\ numbers start lf-term-base higher.
: lf-term-count ( -- addr ) lf-terms store-count ;
: lf-term-generation ( -- addr ) lf-terms store-generation ;
: lf-term-serial ( -- addr ) lf-terms store-serial ;
: lf-term-identities ( -- addr ) lf-terms store-identities ;

\ ---------------------------------------------------------------------------
\ The input view (see the header): the tier, its expression count (the
\ first store number), the address of its first record (a sealed slab
\ never moves), the leaf table and a set over the tier's expressions in
\ which a candidate is sought (cons.fs: a find there looks in the tier).
begin-structure /lf-tview
  field: lf-tview-tier       \ the sealed tier read in place, or 0
  field: lf-tview-base       \ its expressions: the numbers below are input nodes
  field: lf-tview-records    \ address of its record 0
  /cons +field lf-tview-probe    \ a set over its expressions, never committed to
  /htab +field lf-tview-nodes    \ leaf entries by node
  /htab +field lf-tview-fields   \ leaf entries by tag and fields
  /slab +field lf-tview-leaves   \ the entries: node, first, second, stamp
end-structure
/lf-tview context-record: lf-term-view
: lf-term-base ( -- n ) lf-term-view lf-tview-base @ ;
: lf-term-tier ( -- tier ) lf-term-view lf-tview-tier @ ;
: lf-term-viewed? ( -- flag ) lf-term-tier 0<> ;
\ Whether a number names an input node (it may still be no term).
: lf-term-input? ( index -- flag ) lf-term-base u< ;
\ A store record's address from its term number. Unchecked: the number
\ names a record of the store (lf-term-valid?, not an input node).
: lf-term-slot ( index -- addr ) lf-term-base - lf-terms store-slot ;

\ The input tags: per tag of the tier (compact-exprs.fs) the checker's
\ tag, plus lf-tin-leaf-bit when its fields come from the leaf table; 0
\ for a kind that is no term of the view. A module that defines a leaf
\ tag registers it while loading (lf-term-input-leaf-tag), read-only
\ afterwards.
64 constant lf-tin-leaf-bit
create lf-term-input-tags head-tag-mask 1+ cells allot
lf-term-input-tags head-tag-mask 1+ cells erase
: lf-term-input-tag! ( lftag tag -- ) cells lf-term-input-tags + ! ;
\ The checker's tags whose input nodes are in the leaf table, a bit each.
variable lf-tin-leaf-tags   0 lf-tin-leaf-tags !
: lf-term-input-leaf-tag ( lftag tag -- )
  over 1 swap lshift lf-tin-leaf-tags @ or lf-tin-leaf-tags !
  >r lf-tin-leaf-bit or r> lf-term-input-tag! ;
lf-tag-bvar tag-bvar lf-term-input-tag!   lf-tag-app tag-app lf-term-input-tag!
: lf-tin-binders ( -- )
  4 0 do lf-tag-lam tag-lam i + lf-term-input-tag! lf-tag-pi tag-pi i + lf-term-input-tag! loop ;
lf-tin-binders

\ An input record and its parts. Unchecked: index < lf-term-base.
: lf-tin-at ( index -- addr ) /quad * lf-term-view lf-tview-records @ + ;
: lf-tin-code ( index -- x ) lf-tin-at quad-head u32@ head-tag cells lf-term-input-tags + @ ;
: lf-tin-leaf? ( x -- flag ) lf-tin-leaf-bit and 0<> ;

\ The leaf table: entry n is a unit of four cells; it is found by its
\ node, or by the checker's tag and fields of that node.
begin-structure /lf-tleaf
  field: lf-tleaf-node
  field: lf-tleaf-first
  field: lf-tleaf-second
  field: lf-tleaf-stamp
end-structure
: lf-tleaf ( n -- entry ) lf-term-view lf-tview-leaves slab-at ;
: lf-tleaf-tag ( entry -- tag ) lf-tleaf-node @ lf-tin-code lf-tin-leaf-bit 1- and ;
: lf-tleaf-fields ( entry -- tag first second )
  dup lf-tleaf-tag over lf-tleaf-first @ rot lf-tleaf-second @ ;
: lf-tnode-rehash ( n htab -- h ) drop lf-tleaf lf-tleaf-node @ hash-fmix ;
: lf-tnode-same ( n key htab -- flag ) drop swap lf-tleaf lf-tleaf-node @ = ;
\ The fields hash as a store record's (lf-term-hash below, the same mix).
: lf-tfields-hash ( tag first second -- h ) rot hash-fmix rot hash-step swap hash-step ;
: lf-tfields-rehash ( n htab -- h ) drop lf-tleaf lf-tleaf-fields lf-tfields-hash ;
: lf-tfields= ( tag first second addr -- flag )
  >r r@ 2 cells + @ = swap r@ cell+ @ = and swap r> @ = and ;
: lf-tfields-same ( n key htab -- flag ) drop >r lf-tleaf lf-tleaf-fields r> lf-tfields= ;
create lf-tnode-hooks /htab-hooks allot
' lf-tnode-rehash ' lf-tnode-same lf-tnode-hooks htab-hooks!
create lf-tfields-hooks /htab-hooks allot
' lf-tfields-rehash ' lf-tfields-same lf-tfields-hooks htab-hooks!
\ The entry of an input leaf node, or 0.
: lf-tin-leaf ( index -- entry | 0 )
  dup hash-fmix lf-term-view lf-tview-nodes htab-find if lf-tleaf else drop 0 then ;
3 cells context-record: lf-tin-key
: lf-tin-leaf-find ( tag first second -- node true | false )
  lf-tin-key tuck 2 cells + ! tuck cell+ ! tuck ! dup >r @ r@ cell+ @ r@ 2 cells + @
  lf-tfields-hash r> swap lf-term-view lf-tview-fields htab-find
  if lf-tleaf lf-tleaf-node @ true else drop false then ;

\ Reading an input node. Unchecked, but a leaf without an entry reads as
\ fields 0 0 and is not valid.
: lf-tin-valid? ( index -- flag )
  dup lf-tin-code ?dup 0= if drop false exit then
  lf-tin-leaf? if lf-tin-leaf 0<> else drop true then ;
: lf-tin-tag@ ( index -- tag ) lf-tin-code lf-tin-leaf-bit 1- and ;
: lf-tin-leaf@ ( index -- first second )
  lf-tin-leaf ?dup if dup lf-tleaf-first @ swap lf-tleaf-second @ else 0 0 then ;
: lf-tin-ab@ ( index -- first second ) lf-tin-at dup quad-a u32@ swap quad-b u32@ ;
: lf-tin-fields@ ( index -- first second )
  dup lf-tin-code lf-tin-leaf? if lf-tin-leaf@ else lf-tin-ab@ then ;
: lf-tin-first@ ( index -- first )
  dup lf-tin-code lf-tin-leaf? if lf-tin-leaf@ drop else lf-tin-at quad-a u32@ then ;
: lf-tin-second@ ( index -- second )
  dup lf-tin-code lf-tin-leaf? if lf-tin-leaf@ nip else lf-tin-at quad-b u32@ then ;
\ The stamp an input leaf carries (its level's or reference's identity
\ in this context, generation-handles.fs), 0 for none.
: lf-term-leaf-stamp ( index -- stamp )
  lf-tin-leaf ?dup if lf-tleaf-stamp @ else 0 then ;
\ An input node's identity: a negative number, which no serial is.
: lf-term-input-identity ( index -- identity ) invert ;

\ Checked roots, range-checked reads (compact-store plan step S2; ADR
\ 0016 C8). The whole header (shape, seal, generation, count) is checked
\ once where a pass takes a term from outside: lf-term-count-valid?, or
\ lf-term-root? (lf-term-pair-valid? for two) for its root, or a handle
\ (generation-handles.fs). Every
\ read after that (lf-term-valid?, lf-term-identity, lf-term-read and the
\ walks' visits) checks only that the index is allocated (store-at?), or
\ for an input node that the view holds it as a term, so
\ a corrupted shape, seal or generation is refused at the root, never
\ found by a read; a corrupted count still refuses every read.
: lf-term-count-valid? ( -- flag ) lf-terms store-count-valid? ;
: lf-term-valid? ( index -- flag )
  dup lf-term-input? if lf-tin-valid? else lf-term-base - lf-terms store-at? then ;
: lf-term-root? ( index -- flag )
  lf-term-count-valid? if lf-term-valid? else drop false then ;
\ A live node's identity; identities never roll back and never wrap.
: lf-term-identity ( index -- identity true | false )
  dup lf-term-valid? 0= if drop false exit then
  dup lf-term-input? if lf-term-input-identity
  else lf-term-base - lf-terms store-identity @ then true ;

\ Read a node's tag and fields. An index that is not allocated returns
\ only false and no memory is read (the header is the root's to check).
\ lf-term-fields@ reads a store record at its address.
: lf-term-fields@ ( addr -- tag first second )
  dup u32@ over lf-term-first-at + u32@ rot lf-term-second-at + u32@ ;
\ Unchecked: the node's tag and fields, input or store.
: lf-term-fields ( index -- tag first second )
  dup lf-term-input? if dup lf-tin-tag@ swap lf-tin-fields@ exit then
  lf-term-slot lf-term-fields@ ;
: lf-term-read ( index -- tag first second true | false )
  dup lf-term-valid? if lf-term-fields true else drop false then ;
\ One field of a node. Unchecked: the index must already be validated,
\ for instance by an earlier lf-term-read of the same node, under a
\ checked root; no field read checks the header.
: lf-term-tag@ ( index -- tag )
  dup lf-term-input? if lf-tin-tag@ else lf-term-slot u32@ then ;
: lf-term-first@ ( index -- first )
  dup lf-term-input? if lf-tin-first@ else lf-term-slot lf-term-first-at + u32@ then ;
: lf-term-second@ ( index -- second )
  dup lf-term-input? if lf-tin-second@ else lf-term-slot lf-term-second-at + u32@ then ;
\ The end of a store mark as a term number: the nodes below it (input
\ nodes included) are older than the mark.
: lf-term-mark-end ( mark -- n ) mark-count @ lf-term-base + ;

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
: lf-term-data-word ( index -- data )
  dup lf-term-input? if lf-tin-at quad-data u32@ else lf-term-slot lf-term-data-at + u32@ then ;
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
  lf-term-base tuck + swap lf-term-count @ + swap ?do
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
\ Attaching and detaching a view (see the header). Both empty the store
\ first (lf-term-reset), as numbers change meaning. The hook
\ lf-term-view-hook ( -- outcome ) runs after either, for per-node data
\ of another module that must cover the input nodes (the audit's marks,
\ constant-term-boundary.fs); set while loading.
defer lf-term-view-hook ( -- outcome )
' outcome-ok is lf-term-view-hook
: lf-tview-free ( -- )
  lf-term-view dup lf-tview-probe cons-free dup lf-tview-nodes htab-free
  dup lf-tview-fields htab-free dup lf-tview-leaves slab-free /lf-tview erase ;
:noname ( -- ) lf-tview-free ; context-teardown
: lf-tview-tables ( -- outcome )
  4 lf-tnode-hooks lf-term-view lf-tview-nodes htab-init dup ok? 0= if exit then drop
  4 lf-tfields-hooks lf-term-view lf-tview-fields htab-init dup ok? 0= if exit then drop
  /lf-tleaf dup slab-limit-max lf-term-view lf-tview-leaves slab-init ;
: lf-tview-place ( exprs -- )
  lf-term-view >r dup cons-numbers r@ lf-tview-base ! 0 swap cons-at r> lf-tview-records ! ;
: lf-tview-make ( tier -- outcome )
  dup lf-term-view lf-tview-tier ! tier-exprs
  4 over lf-term-view lf-tview-probe cons-extend dup ok? 0= if nip exit then drop
  lf-tview-tables dup ok? 0= if nip exit then drop lf-tview-place outcome-ok ;
\ Read the sealed tier in place: ok; invalid for a tier that is not
\ sealed (or a sealed scratch tier); full when the heap has no room, the
\ view then detached. Detaching gives the hook's outcome.
: lf-term-detach ( -- outcome ) lf-tview-free lf-term-reset lf-term-view-hook ;
: lf-tview-hooked ( -- outcome ) lf-term-view-hook dup ok? 0= if lf-term-detach drop then ;
: lf-term-attach ( tier -- outcome )
  lf-term-detach drop dup tier-exprs cons-sealed? 0= if drop outcome-invalid exit then
  lf-tview-make dup ok? if drop lf-tview-hooked exit then lf-term-detach drop ;

\ Give input leaf node index its fields and stamp (the importer, after
\ attaching; see the header): ok; invalid for a number that is no input
\ leaf of the view or has its entry already; full when the heap has no
\ room. When another entry has the same fields, the first is kept for
\ finding by fields (lf-term-add).
: lf-tleaf-room ( -- outcome )
  lf-term-view lf-tview-nodes htab-ready dup ok? 0= if exit then
  drop lf-term-view lf-tview-fields htab-ready ;
: lf-tleaf-fill ( first second stamp index n -- )
  lf-tleaf tuck lf-tleaf-node ! tuck lf-tleaf-stamp ! tuck lf-tleaf-second !
  lf-tleaf-first ! ;
: lf-tleaf-by-node ( n -- )
  dup lf-tleaf lf-tleaf-node @ dup hash-fmix lf-term-view lf-tview-nodes htab-find
  if 2drop else lf-term-view lf-tview-nodes htab-put then ;
: lf-tleaf-hash ( n -- key h ) lf-tleaf lf-tleaf-fields lf-tfields-hash lf-tin-key swap ;
: lf-tleaf-by-fields ( n -- )
  dup lf-tleaf lf-tleaf-fields lf-tin-leaf-find if 2drop exit then
  dup lf-tleaf-hash lf-term-view lf-tview-fields htab-find
  if 2drop else lf-term-view lf-tview-fields htab-put then ;
: lf-tleaf-new ( first second stamp index -- outcome )
  lf-tleaf-room dup ok? 0= if >r 2drop 2drop r> exit then drop
  1 lf-term-view lf-tview-leaves slab-claim dup ok? 0= if nip >r 2drop 2drop r> exit then
  drop dup >r lf-tleaf-fill r@ lf-tleaf-by-node r> lf-tleaf-by-fields outcome-ok ;
: lf-tin-leaf-node? ( index -- flag )
  dup lf-term-input? if lf-tin-code lf-tin-leaf? else drop false then ;
: lf-term-input-leaf ( first second stamp index -- outcome )
  dup lf-tin-leaf-node? if dup lf-tin-leaf 0= else false then
  if lf-tleaf-new else 2drop 2drop outcome-invalid then ;

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
: lf-term-numbered? ( -- flag ) lf-term-count @ lf-term-base + u32-mask 1- u< ;
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
  lf-term-base + >r lf-term-store! r> true ;
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
\ Whether a found node may be given again: a leaf whose meaning is more
\ than its fields (a symbolic Sort's or a constant's stamps,
\ generation-handles.fs) only while those still hold; the hook is set
\ while loading (core/constant-term-boundary.fs). A node it refuses is
\ taken out of the table, and the record is sought again, so a new node
\ is made and entered in its place (compact-store plan step S4).
defer lf-term-reusable? ( n -- flag )
:noname ( n -- flag ) drop true ; is lf-term-reusable?

\ An input node equal to the record (see the header): an application of
\ two input nodes or a bound variable in the tier's expression table,
\ through the view's set over it (the candidate written at its free end
\ and sought there, never kept); a leaf (a Sort, constant or literal) in
\ the leaf table by its fields. No other record is sought: it equals no
\ input node of the view (the importer copies the kinds the view does
\ not read, and every node above one, into the store). A found leaf is
\ given again only while its stamps hold (lf-term-reusable?).
: lf-tin-probe ( head a b -- n true | false )
  lf-term-view lf-tview-probe >r 1 0 r@ cons-room ok? 0= if 2drop drop r> drop false exit then
  r@ cand! r@ cons-top expr-hash true r> cons-find
  if dup lf-term-input? dup 0= if nip then else drop false then ;
: lf-tin-app ( first second -- n true | false )
  2dup lf-term-input? swap lf-term-input? and
  if tag-app 0 pack-head -rot lf-tin-probe else 2drop false then ;
: lf-tin-bvar ( first second -- n true | false )
  over bvar-fits? over 0= and if tag-bvar 0 pack-head -rot lf-tin-probe else 2drop false then ;
: lf-tin-leaf-tag? ( tag -- flag ) lf-term-tag-bit lf-tin-leaf-tags @ and 0<> ;
: lf-tin-sought ( tag first second -- n true | false )
  2 pick case
    lf-tag-app of rot drop lf-tin-app endof
    lf-tag-bvar of rot drop lf-tin-bvar endof
    lf-tin-leaf-tag? if lf-tin-leaf-find else 2drop drop false then 0 endcase ;
: lf-tin-given ( tag first second -- n true | false )
  lf-term-viewed? 0= if 2drop drop false exit then
  lf-tin-sought dup if over lf-term-reusable? 0= if 2drop false then then ;
: lf-term-cons ( tag first second -- index true | false )
  lf-term-table htab-ready ok? 0= if lf-term-append exit then
  2 pick 2 pick 2 pick lf-tin-given if nip nip nip lf-term-found exit then
  lf-term-find 0= if lf-term-key@ lf-term-append lf-term-enter exit then
  dup lf-term-reusable? if lf-term-found exit then
  lf-term-forget lf-term-key@ recurse ;
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
: lf-term-pair-valid? ( left right -- flag )
  lf-term-count-valid? if lf-term-valid? swap lf-term-valid? and else 2drop false then ;
: lf-term-binary ( left right tag -- index true | false )
  >r 2dup lf-term-pair-valid? r@ lf-term-binary-tag? and
  if r> -rot lf-term-add else r> drop 2drop false then ;
\ Application: function, then argument.
: lf-term-app ( function argument -- index true | false ) lf-tag-app lf-term-binary ;
\ Lambda: binder type annotation, then body. The body is not scope-checked.
: lf-term-lam ( annotation body -- index true | false ) lf-tag-lam lf-term-binary ;
\ Dependent function type: domain, then body. Nothing is typed.
: lf-term-pi ( domain body -- index true | false ) lf-tag-pi lf-term-binary ;

\ Bounded storage for the syntax of a small Lean expression subset: Sort,
\ bound variable, application, lambda and Pi nodes, and the binary nodes
\ of lets and projections (and leaves other modules define). Untrusted; not a kernel
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
\ the first term numbers, 0 .. lf-term-base - 1, record u of the stage
\ being term 2u + 1 and what it carries term 2u (see "Term numbers of the
\ view" below; lets and projections since step S5's parts 4-5), and the
\ store's own records follow them, record r being term lf-term-base + r.
\ Every reader below takes a term number and reads an input node from the
\ tier's 16-byte record (C1), its tag translated to the checker's: a
\ bound variable, application, lambda or Pi (binder name and information
\ ignored, as Lean's kernel ignores them) with the record's own fields,
\ its children's records as term numbers; a let's lambda from the let's
\ two records; a Sort, constant, literal, let, projection or projection
\ leaf with the fields the importer gave it in the view's leaf table
\ (lf-term-input-leaf: the level, reference or literal it became in this
\ context, and the stamp a symbolic Sort or constant carries,
\ generation-handles.fs; a let's value and lambda; a projection's leaf
\ and term); any other kind
\ (metadata, a free variable, a let's body record) is no term of the
\ view, so a node above one is copied into the store instead
\ (import/feed.fs). An input node is sealed: never rolled back or reset,
\ its data word the tier's (computed when it was staged, C8, the same
\ facts as this store's; a let's lambda's computed from its children's),
\ and its identity is the negative number invert index, which no birth
\ serial is. Making a node equal to an input node gives that node
\ (lf-term-add finds an application or bound variable in the tier's
\ table, a binder in the binder table, a Sort, constant, literal, let,
\ projection or projection leaf in the leaf table), so
\ equal terms are one number across the two parts. Without a view
\ lf-term-base is 0 and everything is as before. The tier must outlive
\ the view: lf-term-detach (or freeing the context) first.
\
\ State: the store header lf-terms, the hash table lf-term-table, the
\ candidate record lf-term-key, the switch lf-term-share-off and the view
\ record lf-term-view, members
\ of the checker context (lib/context.fs) whose blocks are on the heap,
\ freed by their teardown words, so each context has its own terms (a
\ worker's view may read the leaf and binder tables of the context that
\ fed them, through copies of their headers: lf-term-borrow);
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
require ../lib/bits.fs
require ../lib/slab.fs
require ../lib/cons.fs
require ./diagnostics.fs
require ./compact.fs
require ../lib/store-columns.fs
require ./scratch-meter.fs

64 constant lf-term-default
64 constant lf-walk-room     \ a walk's first room, in items
1 constant lf-tag-sort
2 constant lf-tag-bvar
3 constant lf-tag-app
4 constant lf-tag-lam
5 constant lf-tag-pi
\ The other binary nodes (compact-store plan step S5, parts 4-5): a let,
\ LET(v, fun x : T => b) (core/let-terms.fs), one tag for each value of
\ Lean's nonDep flag; a projection, PROJECTION(leaf, e)
\ (core/projections.fs). Their children are at the node's own depth.
12 constant lf-tag-let
14 constant lf-tag-projection
15 constant lf-tag-let-nondep
\ A tag's bit (tags above 31 share bit 31, which no binary tag has).
: lf-tag-bit ( tag -- mask ) 1 swap 31 min lshift ;
lf-tag-app lf-tag-bit lf-tag-lam lf-tag-bit or lf-tag-pi lf-tag-bit or
lf-tag-let lf-tag-bit or lf-tag-projection lf-tag-bit or lf-tag-let-nondep lf-tag-bit or
constant lf-binary-tags
\ Binary nodes: two children; binders: the second under one more binder.
: lf-term-binary-tag? ( tag -- flag ) lf-tag-bit lf-binary-tags and 0<> ;
: lf-term-binder-tag? ( tag -- flag ) dup lf-tag-lam = swap lf-tag-pi = or ;
\ The binder depth of a node's body: one more under a lambda or Pi
\ (false at max-n: no room), the same under any other tag.
: lf-term-inner ( depth tag -- depth' true | false )
  lf-term-binder-tag? 0= if true exit then dup max-n = if drop false else 1+ true then ;

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
  /htab +field lf-tview-binders  \ input binders by tag and children
  field: lf-tview-borrowed       \ true: the four tables above are another
                                 \ context's, read in place (lf-term-borrow)
  field: lf-tview-horizon        \ 0, or no leaf entry of a node from it on
                                 \ is found (lf-term-horizon!)
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

\ Term numbers of the view (compact-store plan step S5, parts 4-5): the
\ tier's record u is term 2u + 1, and term 2u is the node the record
\ carries besides itself, if any: a letE record's lambda (its type and the
\ body its second record holds) and a proj record's leaf (its structure's
\ name and its field index); every child stays below its parent, as the
\ store's own nodes, and nothing is copied. A let, a projection and a
\ projection's leaf are leaves of the leaf table, whose entries the
\ importer gives, so that equal nodes are one node, as when copied: a
\ let is LET(v, lam), lam the first input binder equal to its lambda
\ (2u, or an earlier lambda of the same type and body); a projection is
\ PROJECTION(leaf, e), the leaf the first input one of its name and index
\ (2u, or an earlier projection's).
: lf-tin-child ( u -- index ) 2* 1+ ;
\ The input codes: per tag of the tier (compact-exprs.fs) and parity of
\ the term number (the record itself, odd, or what it carries, even) the
\ checker's tag (bits 0-5), lf-tin-leaf-bit when its fields come from
\ the leaf table, and how its fields are read (bits 7-9): a pair of
\ children (app, binders), the raw fields (a bound variable), a let's
\ lambda; a projection's leaf has a mode of its own for its data word
\ (0, closed); 0 for no term of the view. A module that defines a leaf
\ tag registers it while loading (lf-term-input-leaf-tag,
\ lf-term-input-leaf-twin), read-only afterwards.
63 constant lf-tin-tag-mask
64 constant lf-tin-leaf-bit
0 constant lf-tin-pair
128 constant lf-tin-raw
384 constant lf-tin-let-lam
512 constant lf-tin-proj-leaf
896 constant lf-tin-modes
create lf-term-input-codes head-tag-mask 1+ 2* cells allot
lf-term-input-codes head-tag-mask 1+ 2* cells erase
: lf-tin-entry ( tag parity -- addr ) swap 2* + cells lf-term-input-codes + ;
: lf-term-input-tag! ( code tag -- ) 1 lf-tin-entry ! ;
: lf-term-input-twin! ( code tag -- ) 0 lf-tin-entry ! ;
\ The checker's tags whose input nodes are in the leaf table, a bit each.
variable lf-tin-leaf-tags   0 lf-tin-leaf-tags !
: lf-tin-leaf-tags+ ( lftag -- ) 1 swap lshift lf-tin-leaf-tags @ or lf-tin-leaf-tags ! ;
: lf-term-input-leaf-tag ( lftag tag -- )
  over lf-tin-leaf-tags+ >r lf-tin-leaf-bit or r> lf-term-input-tag! ;
\ The same for what a record of tag carries, read in mode.
: lf-term-input-leaf-twin ( lftag mode tag -- )
  2 pick lf-tin-leaf-tags+ >r or lf-tin-leaf-bit or r> lf-term-input-twin! ;
lf-tag-bvar lf-tin-raw or tag-bvar lf-term-input-tag!
lf-tag-app tag-app lf-term-input-tag!
: lf-tin-binders ( -- )
  4 0 do
    lf-tag-lam tag-lam i + lf-term-input-tag!  lf-tag-pi tag-pi i + lf-term-input-tag!
  loop ;
lf-tin-binders
: lf-tin-lets ( -- )
  lf-tag-let tag-let lf-term-input-leaf-tag
  lf-tag-let-nondep tag-let-nondep lf-term-input-leaf-tag
  lf-tag-lam lf-tin-let-lam or dup tag-let lf-term-input-twin!
  tag-let-nondep lf-term-input-twin!
  lf-tag-projection tag-proj lf-term-input-leaf-tag ;
lf-tin-lets

\ An input record and its parts. Unchecked: index < lf-term-base.
: lf-tin-at ( index -- addr ) 1 rshift /quad * lf-term-view lf-tview-records @ + ;
: lf-tin-code ( index -- x )
  dup 1 and swap lf-tin-at quad-head u32@ head-tag swap lf-tin-entry @ ;
: lf-tin-leaf? ( x -- flag ) lf-tin-leaf-bit and 0<> ;
: lf-tin-plain? ( x -- flag ) lf-tin-leaf-bit lf-tin-modes or and 0= ;

\ The leaf table: entry n is a unit of four cells; it is found by its
\ node, or by the checker's tag and fields of that node.
begin-structure /lf-tleaf
  field: lf-tleaf-node
  field: lf-tleaf-first
  field: lf-tleaf-second
  field: lf-tleaf-stamp
end-structure
: lf-tleaf ( n -- entry ) lf-term-view lf-tview-leaves slab-at ;
: lf-tleaf-tag ( entry -- tag ) lf-tleaf-node @ lf-tin-code lf-tin-tag-mask and ;
: lf-tleaf-fields ( entry -- tag first second )
  dup lf-tleaf-tag over lf-tleaf-first @ rot lf-tleaf-second @ ;
: lf-tnode-rehash ( n htab -- h ) drop lf-tleaf lf-tleaf-node @ hash-fmix ;
: lf-tnode-same ( n key htab -- flag ) drop swap lf-tleaf lf-tleaf-node @ = ;
\ The record a hash table is asked for (the input view's lf-tin-key, the
\ store's lf-term-key, levels.fs's lf-level-key): a tag and two fields,
\ hashed alike, and whether a record's fields are the ones sought.
begin-structure /lf-sought
  field: lf-sought-tag
  field: lf-sought-first
  field: lf-sought-second
end-structure
: lf-sought! ( tag first second key -- )
  tuck lf-sought-second ! tuck lf-sought-first ! lf-sought-tag ! ;
: lf-sought@ ( key -- tag first second )
  dup lf-sought-tag @ over lf-sought-first @ rot lf-sought-second @ ;
: lf-sought= ( tag first second key -- flag )
  >r r@ lf-sought-second @ = swap r@ lf-sought-first @ = and
  swap r> lf-sought-tag @ = and ;
: lf-fields-hash ( tag first second -- h ) rot hash-fmix rot hash-step swap hash-step ;
\ The key's hash after its fields are stored.
: lf-sought-hash! ( tag first second key -- key h )
  dup >r lf-sought! r@ dup lf-sought@ lf-fields-hash r> drop ;
: lf-tfields-rehash ( n htab -- h ) drop lf-tleaf lf-tleaf-fields lf-fields-hash ;
: lf-tfields-same ( n key htab -- flag ) drop >r lf-tleaf lf-tleaf-fields r> lf-sought= ;
create lf-tnode-hooks /htab-hooks allot
' lf-tnode-rehash ' lf-tnode-same lf-tnode-hooks htab-hooks!
create lf-tfields-hooks /htab-hooks allot
' lf-tfields-rehash ' lf-tfields-same lf-tfields-hooks htab-hooks!
\ The entry of an input leaf node, or 0.
: lf-tin-leaf ( index -- entry | 0 )
  dup hash-fmix lf-term-view lf-tview-nodes htab-find if lf-tleaf else drop 0 then ;
\ The record sought, and its hash, for a table's find.
/lf-sought context-record: lf-tin-key
: lf-tin-key! ( tag first second -- key h ) lf-tin-key lf-sought-hash! ;
\ A node below the horizon, when one is set (see lf-term-horizon! below;
\ the cell holds the horizon plus one, 0 for none).
: lf-tin-before? ( node -- flag )
  lf-term-view lf-tview-horizon @ ?dup if 1- u< else drop true then ;
: lf-tin-leaf-find ( tag first second -- node true | false )
  lf-tin-key! lf-term-view lf-tview-fields htab-find
  if lf-tleaf lf-tleaf-node @ dup lf-tin-before? dup 0= if nip then
  else drop false then ;
\ The horizon: while one is set, a leaf entry of a node from it on is not
\ found by its fields. A worker that shares a fed input
\ (import/feed.fs's lf-feed-shared) remakes the feed's copies of
\ expression e with the horizon 2e, so that each finds only the leaves
\ the feed had entered when it made that copy, as when it fed them;
\ lf-term-unbounded ends it.
: lf-term-horizon! ( node -- ) 1+ lf-term-view lf-tview-horizon ! ;
: lf-term-unbounded ( -- ) 0 lf-term-view lf-tview-horizon ! ;

\ Reading an input node. Unchecked, but a leaf without an entry reads as
\ fields 0 0 and is not valid.
: lf-tin-valid? ( index -- flag )
  dup lf-tin-code ?dup 0= if drop false exit then
  lf-tin-leaf? if lf-tin-leaf 0<> else drop true then ;
: lf-tin-tag@ ( index -- tag ) lf-tin-code lf-tin-tag-mask and ;
: lf-tin-leaf@ ( index -- first second )
  lf-tin-leaf ?dup if dup lf-tleaf-first @ swap lf-tleaf-second @ else 0 0 then ;
\ The fields by how the code reads them (see above): a pair of children;
\ the raw fields; a let's lambda's type and body (the let's second
\ record).
: lf-tin-raw@ ( index -- first second ) lf-tin-at quad-ab@ ;
: lf-tin-pair@ ( index -- first second ) lf-tin-raw@ swap lf-tin-child swap lf-tin-child ;
: lf-tin-let-lam@ ( index -- first second )
  lf-tin-at dup quad-a u32@ lf-tin-child swap /quad + quad-a u32@ lf-tin-child ;
: lf-tin-moded@ ( index x -- first second )
  lf-tin-modes and case lf-tin-raw of lf-tin-raw@ endof
    lf-tin-let-lam of lf-tin-let-lam@ endof  >r lf-tin-pair@ r> endcase ;
: lf-tin-other@ ( index x -- first second )
  dup lf-tin-leaf? if drop lf-tin-leaf@ else lf-tin-moded@ then ;
: lf-tin-fields@ ( index -- first second )
  dup lf-tin-code dup lf-tin-plain? if drop lf-tin-pair@ else lf-tin-other@ then ;
: lf-tin-first@ ( index -- first )
  dup lf-tin-code dup lf-tin-plain?
  if drop lf-tin-at quad-a u32@ lf-tin-child else lf-tin-other@ drop then ;
: lf-tin-second@ ( index -- second )
  dup lf-tin-code dup lf-tin-plain?
  if drop lf-tin-at quad-b u32@ lf-tin-child else lf-tin-other@ nip then ;
\ The binder name and information (0 explicit .. 3 instance implicit) of
\ an input lambda or Pi, from its record (C1 keeps them for printing; the
\ checker's rules ignore them); a let's lambda has the let's name and is
\ explicit. False for any other number. Unchecked: the view is attached.
: lf-tin-head ( index -- head ) lf-tin-at quad-head u32@ ;
: lf-tin-binder-kind ( head -- name kind )
  dup head-payload swap head-tag tag-lam - 3 and ;
\ Whether input node index is a let's lambda (read from the let's records).
: lf-tin-let-lam? ( index -- flag ) lf-tin-code lf-tin-modes and lf-tin-let-lam = ;
: lf-term-input-binder@ ( index -- name kind true | false )
  dup lf-term-input? 0= if drop false exit then
  dup lf-tin-let-lam? if lf-tin-head head-payload 0 true exit then
  dup 1 and if lf-tin-head dup head-tag binder-tag? else 0 then
  if lf-tin-binder-kind true else drop false then ;
\ The entry number of an input leaf node, or false.
: lf-tin-leaf# ( index -- n true | false )
  dup hash-fmix lf-term-view lf-tview-nodes htab-find dup 0= if nip then ;
\ The unit of an input node in a table of one unit per tier record and
\ one per leaf entry (the audit's marks, constant-term-boundary.fs): a
\ record's own; for a let's lambda that of the let's second record,
\ which is no term; for a projection's leaf, the record count plus its
\ entry number; none for any other number.
: lf-term-input-records ( -- n ) lf-term-base 1 rshift ;
: lf-term-input-units ( -- n )
  lf-term-input-records lf-term-view lf-tview-leaves slab-count + ;
: lf-term-input-unit ( index -- u true | false )
  dup 1 and if 1 rshift true exit then
  dup lf-tin-let-lam? if 1 rshift 1+ true exit then
  lf-tin-leaf# if lf-term-input-records + true else false then ;
\ The stamp an input leaf carries (its level's or reference's identity
\ in this context, generation-handles.fs), 0 for none.
: lf-term-leaf-stamp ( index -- stamp )
  lf-tin-leaf ?dup if lf-tleaf-stamp @ else 0 then ;
\ An input node's identity: a negative number, which no serial is.
: lf-term-input-identity ( index -- identity ) invert ;

\ The binder table: input lambdas and Pis that the importer enters
\ (lf-term-input-binder), found by tag and children, binder name and
\ information ignored, as Lean's == ignores them. A slot holds the node.
: lf-tbind-fields ( n -- tag first second ) dup lf-tin-tag@ swap lf-tin-fields@ ;
: lf-tbind-rehash ( n htab -- h ) drop lf-tbind-fields lf-fields-hash ;
: lf-tbind-same ( n key htab -- flag ) drop >r lf-tbind-fields r> lf-sought= ;
create lf-tbind-hooks /htab-hooks allot
' lf-tbind-rehash ' lf-tbind-same lf-tbind-hooks htab-hooks!
: lf-tin-binder-find ( tag first second -- node true | false )
  lf-tin-key! lf-term-view lf-tview-binders htab-find dup 0= if nip then ;

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
\ A node with its identity, 0 when it is not live (a pass then refuses it).
: lf-term-handle ( index -- index identity ) dup lf-term-identity 0= if 0 then ;

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
\ The node's kind, by its tag, unchecked as lf-term-tag@: a tag; an
\ application, lambda, Pi or bound variable; a binary node (two
\ children) or a binder (lambda or Pi). A constant's is
\ constant-term-boundary.fs's lf-term-const?, beside its tag.
: lf-term-tag? ( index tag -- flag ) swap lf-term-tag@ = ;
: lf-term-app? ( index -- flag ) lf-tag-app lf-term-tag? ;
: lf-term-lam? ( index -- flag ) lf-tag-lam lf-term-tag? ;
: lf-term-pi? ( index -- flag ) lf-tag-pi lf-term-tag? ;
: lf-term-bvar? ( index -- flag ) lf-tag-bvar lf-term-tag? ;
: lf-term-binary? ( index -- flag ) lf-term-tag@ lf-term-binary-tag? ;
: lf-term-binder? ( index -- flag ) lf-term-tag@ lf-term-binder-tag? ;
\ Whether the node is the bound variable #n.
: lf-term-bvar-is? ( index n -- flag )
  over lf-term-bvar? if swap lf-term-first@ = else 2drop false then ;
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
\ An input node's data word: its record's (C1's, computed when it was
\ staged); a let's lambda's from its type's and body's, as made here; a
\ projection leaf's 0 (closed, no parameter), as constant-term-boundary.fs
\ gives a store leaf.
: lf-tin-data@ ( index -- data ) lf-tin-at quad-data u32@ ;
: lf-tin-lam-data ( index -- data )
  lf-tin-let-lam@ swap lf-tin-data@ swap lf-tin-data@ true lf-data-pair ;
: lf-tin-data ( index -- data )
  dup lf-tin-code lf-tin-modes and
  dup lf-tin-let-lam = if drop lf-tin-lam-data exit then
  lf-tin-proj-leaf = if drop 0 else lf-tin-data@ then ;
\ A node's data word as made. Unchecked: the index is valid.
: lf-term-data-word ( index -- data )
  dup lf-term-input? if lf-tin-data exit then
  lf-term-slot lf-term-data-at + u32@ ;
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
/lf-sought context-record: lf-term-key   \ the record sought: tag first second
1 cells context-record: lf-term-share-off   \ true when this context does not share
\ Tags whose leaves are never shared, a bit each; set while loading.
variable lf-term-unshared-tags   0 lf-term-unshared-tags !
: lf-term-tag-bit ( tag -- mask ) lf-tag-bit ;
: lf-term-unshare ( tag -- )
  lf-term-tag-bit lf-term-unshared-tags @ or lf-term-unshared-tags ! ;
: lf-term-shared-tag? ( tag -- flag ) lf-term-tag-bit lf-term-unshared-tags @ and 0= ;
\ The switch: sharing is on in a new context.
: lf-term-sharing? ( -- flag ) lf-term-share-off @ 0= ;
: lf-term-sharing! ( flag -- ) 0= lf-term-share-off ! ;

\ Whether node n may be given for a record made equal to it (hash-consing,
\ below): a hook, by default always. kernel/check-declaration.fs sets it so
\ that in a check a node made before the check (an input node or the
\ importer's copy) is given only once the check has reached it (agent PF,
\ ADR 0014 Amendment 7): what a check meets then depends only on its
\ declaration and what it reads, never on the other records of the tier.
\ A node not given only costs sharing: a new node is made, never another
\ result.
defer lf-term-findable? ( n -- flag )
:noname ( n -- flag ) drop true ; is lf-term-findable?

\ The table's hooks: the hash of record n from its fields, and whether
\ live record n equals the record sought (and may be given).
: lf-term-rehash ( n htab -- h ) drop lf-term-slot lf-term-fields@ lf-fields-hash ;
\ The fields are compared before the hook is asked, which a probe then
\ asks only of the one live record equal to the key, never of the others
\ its run passes (agent PERF1: the hook reads the environment's validity,
\ about 5% of Init's checking time when asked of every record probed).
\ Neither changes what the other reads, so the order changes no answer.
\ Unchecked (lf-term-equal?, lf-term-given?): record n is live.
: lf-term-equal? ( n key -- flag ) >r lf-term-slot lf-term-fields@ r> lf-sought= ;
: lf-term-given? ( n key -- flag )
  over swap lf-term-equal? if lf-term-findable? else drop false then ;
: lf-term-same ( n key htab -- flag )
  drop over lf-term-valid? if lf-term-given? else 2drop false then ;
create lf-term-hooks /htab-hooks allot
' lf-term-rehash ' lf-term-same lf-term-hooks htab-hooks!
\ A context's table: 16 slots at first, freed with the context. A table
\ that has grown large goes back to 16 slots when the store is reset, so
\ a reset costs little whatever an earlier run needed.
: lf-term-table-make ( -- ) 4 lf-term-hooks lf-term-table htab-init drop ;
' lf-term-table-make context-setup
:noname ( -- ) lf-term-table htab-free ; context-teardown
: lf-term-table-empty ( -- ) lf-term-table ['] lf-term-table-make htab-renew ;

\ Room in the table for n entries without doubling (the feed sizes it
\ from the stage's counts, ADR 0016 C9); a table the heap cannot make
\ that large only costs time.
: lf-term-table-room ( n -- ) 4 * 3 / 1+ log2-ceiling lf-term-table htab-presize drop ;

\ Taking records out of the table: entry index, if it is there (a record
\ made while sharing was off, or that the table could not take, is not),
\ and every record from count up to the store's count.
: lf-term-forget ( index -- )
  dup lf-term-slot lf-term-fields@ lf-fields-hash lf-term-table htab-remove drop ;
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
\ The four tables, nodes to binders, lie together in the view record; a
\ borrowed view's are another context's (lf-term-borrow below), so only
\ the copies of their headers are erased.
0 lf-tview-binders /htab + 0 lf-tview-nodes - constant /lf-tview-shared
: lf-tview-tables-free ( view -- )
  dup lf-tview-borrowed @ if lf-tview-nodes /lf-tview-shared erase exit then
  dup lf-tview-nodes htab-free dup lf-tview-fields htab-free
  dup lf-tview-leaves slab-free lf-tview-binders htab-free ;
: lf-tview-free ( -- )
  lf-term-view dup lf-tview-probe cons-free dup lf-tview-tables-free /lf-tview erase ;
:noname ( -- ) lf-tview-free ; context-teardown
: lf-tview-tables ( -- outcome )
  4 lf-tnode-hooks lf-term-view lf-tview-nodes htab-init dup ok? 0= if exit then drop
  4 lf-tfields-hooks lf-term-view lf-tview-fields htab-init dup ok? 0= if exit then drop
  4 lf-tbind-hooks lf-term-view lf-tview-binders htab-init dup ok? 0= if exit then drop
  /lf-tleaf dup slab-limit-max lf-term-view lf-tview-leaves slab-init ;
: lf-tview-place ( exprs -- )
  lf-term-view >r dup cons-numbers 2* r@ lf-tview-base !
  0 swap cons-at r> lf-tview-records ! ;
: lf-tview-make ( tier -- outcome )
  dup lf-term-view lf-tview-tier ! tier-exprs
  4 over lf-term-view lf-tview-probe cons-extend dup ok? 0= if nip exit then drop
  lf-tview-tables dup ok? 0= if nip exit then drop lf-tview-place outcome-ok ;
\ Read the sealed tier in place: ok; invalid for a tier that is not
\ sealed (or a sealed scratch tier); full when the heap has no room, the
\ view then detached. Detaching gives the hook's outcome.
: lf-term-detach ( -- outcome ) lf-tview-free lf-term-reset lf-term-view-hook ;
: lf-tview-hooked ( -- outcome )
  lf-term-view-hook dup ok? 0= if lf-term-detach drop then ;
: lf-term-attach ( tier -- outcome )
  lf-term-detach drop dup tier-exprs cons-sealed? 0= if drop outcome-invalid exit then
  lf-tview-make dup ok? if drop lf-tview-hooked exit then lf-term-detach drop ;
\ After the importer has given the leaves their entries (below), the hook
\ again, so that other modules' per-node data covers the leaves that
\ have units of their own (lf-term-input-unit): ok, or the hook's failure
\ (full when the heap has no room), the view kept.
: lf-term-view-grown ( -- outcome ) lf-term-view-hook ;

\ Sharing a fed view (shared input, ADR 0016 S8; import/feed.fs's
\ lf-feed-shared): a context attached to the same tier as the source
\ context reads the source's leaf and binder tables in place, through
\ copies of their headers, its own empty tables freed first; the hash
\ tables' copies are frozen (lib/htab.fs), so a find writes nothing and no
\ entry can be added. Its probe, store, stamps and marks stay its own.
\ The source, which fed the tables (import/feed.fs), must outlive this
\ context and add no entry while it reads them; they are never freed here
\ (lf-tview-tables-free erases the copies). ok, then the hook again (its
\ failure, full, keeps the view); invalid, nothing changed, when this
\ context has no view, its tier is not the source's, it borrowed already
\ or the source is this context. lf-member-in gives the address of a
\ member of the current context in another context: every context has
\ the same layout (lib/context.fs).
: lf-member-in ( addr context -- addr' ) swap lf-context @ - + ;
\ The units of a slab member copied from the same member of the source
\ context into this context's, which must be empty (the literals' limbs
\ and bytes, a few kilobytes, which checks append to): ok; invalid when it
\ is not empty or the source is this context; full when the heap has no
\ room.
: lf-slab-bytes-of ( slab -- addr u ) 0 over slab-at swap slab-used-bytes ;
: lf-slab-copy-in ( slab source -- outcome )
  over swap lf-member-in 2dup = 2 pick slab-count 0<> or
  if 2drop outcome-invalid exit then
  dup slab-count 2 pick slab-claim nip dup ok? 0= if nip nip exit then drop
  lf-slab-bytes-of rot 0 swap slab-at swap move outcome-ok ;
: lf-tview-frozen ( view -- )
  dup lf-tview-nodes htab-freeze dup lf-tview-fields htab-freeze
  lf-tview-binders htab-freeze ;
: lf-tview-copy ( source-view -- )
  lf-term-view dup lf-tview-tables-free >r lf-tview-nodes r@ lf-tview-nodes
  /lf-tview-shared move true r@ lf-tview-borrowed ! r> lf-tview-frozen ;
: lf-tview-lendable? ( source-view -- flag )
  dup lf-term-view <> swap lf-tview-tier @ lf-term-tier = and lf-term-viewed? and
  lf-term-view lf-tview-borrowed @ 0= and ;
: lf-term-borrow ( source -- outcome )
  lf-term-view swap lf-member-in dup lf-tview-lendable?
  if lf-tview-copy lf-term-view-grown else drop outcome-invalid then ;

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
: lf-tleaf-hash ( n -- key h ) lf-tleaf lf-tleaf-fields lf-fields-hash lf-tin-key swap ;
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

\ Enter input binder index in the binder table (the importer, for each
\ binder it reads in place): ok; invalid for a number that is no input
\ lambda or Pi; full when the heap has no room. When another binder has
\ the same tag and children, the first stays; lf-term-input-binder-first
\ also says whether index is that first one (false: an earlier binder of
\ its == class is in the table, which the importer then gives index's
\ uses instead: import/feed.fs, ADR 0014 Amendment 7).
: lf-tin-binder? ( index -- flag )
  dup lf-term-input? 0= if drop false exit then
  lf-tin-tag@ lf-term-binder-tag? ;
: lf-tbind-new? ( index -- flag )
  dup lf-tbind-fields lf-tin-key! lf-term-view lf-tview-binders htab-find
  if 2drop false else lf-term-view lf-tview-binders htab-put true then ;
: lf-term-input-binder-first ( index -- flag outcome )
  dup lf-tin-binder? 0= if drop false outcome-invalid exit then
  lf-term-view lf-tview-binders htab-ready dup ok? 0= if nip false swap exit then
  drop lf-tbind-new? outcome-ok ;
: lf-term-input-binder ( index -- outcome ) lf-term-input-binder-first nip ;
\ Whether input binder index is not the binder the table holds for its ==
\ class, so the importer gave its uses that earlier one: for a shared feed,
\ which reads the source's table in place and enters nothing.
: lf-term-input-binder-merged? ( index -- flag )
  dup lf-tin-binder? 0= if drop false exit then
  dup lf-tbind-fields lf-tin-key! lf-term-view lf-tview-binders htab-find
  if <> else 2drop false then ;

\ ---------------------------------------------------------------------------
\ Making nodes. Append a node whose tag and fields the caller validated,
\ first growing the store and its columns when every record is in use. A
\ field outside 0 .. 2^32-1, an invalid count, a full store (at its
\ capacity, at 2^32-1 records, or no heap) or a spent serial returns
\ false, changes nothing and is recorded as a diagnostic; so does a
\ record past a check's memory limit (scratch-meter.fs).
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
\ Data of a child; a child that is not allocated (a raw caller's) has none.
: lf-term-child-data ( index -- data )
  dup lf-term-valid? if lf-term-data-word else drop lf-data-unknown then ;
\ A let's data word as Lean's letE and the stage make it: the value and the
\ lambda LET(v, fun x : T => b) hold, one level deeper than the deepest of
\ type, value and body, not than the lambda (which is one deeper than T
\ and b; review rvS5B M1). An unknown word stays unknown.
: lf-term-let-tag? ( tag -- flag ) dup lf-tag-let = swap lf-tag-let-nondep = or ;
: lf-let-lam-data ( data -- data' )
  dup lf-data-known? if 1 22 lshift - then ;
: lf-term-let-data ( value-data lam-data -- data )
  lf-let-lam-data false lf-data-pair ;
: lf-term-data-of ( tag first second -- data )
  2 pick lf-term-binary-tag? 0= if lf-term-leaf-data exit then
  lf-term-child-data swap lf-term-child-data swap rot
  dup lf-term-let-tag? if drop lf-term-let-data exit then
  lf-term-binder-tag? lf-data-pair ;
: lf-term-store! ( tag first second data addr -- )
  tuck lf-term-data-at + u32! tuck lf-term-second-at + u32!
  tuck lf-term-first-at + u32! u32! ;
\ A new record is charged to a check's memory limit here, where it is
\ made, never one found shared (review rvRS F4): a refusal is exact.
: lf-term-new ( tag first second data -- index true | false )
  lf-meter-term? 0= if 2drop 2drop lf-term-refused exit then
  lf-terms store-new-slot 0= if 2drop 2drop lf-term-refused exit then
  lf-term-base + >r lf-term-store! r> true ;
: lf-term-append ( tag first second -- index true | false )
  2 pick 2 pick 2 pick lf-term-data-of lf-term-new ;
\ Hash-consed: the equal node, or a new node entered at the empty slot
\ the find gave (nothing changes the table in between). A table that
\ cannot grow (no heap) only costs sharing.
: lf-term-key@ ( -- tag first second ) lf-term-key lf-sought@ ;
: lf-term-find ( tag first second -- n true | i false )
  lf-term-key lf-sought-hash! lf-term-table htab-find ;
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
\ two input records or a bound variable in the tier's expression table,
\ through the view's set over it (the candidate written at its free end
\ and sought there, never kept); a leaf (a Sort, constant or literal) in
\ the leaf table by its fields (a let, a projection and its leaf among
\ them); a binder in the binder table. No other record is sought: it
\ equals no
\ input node of the view (the importer copies the kinds the view does
\ not read, and every node above one, into the store). A found leaf is
\ given again only while its stamps hold (lf-term-reusable?).
: lf-tin-record? ( index -- flag ) dup 1 and 0<> swap lf-term-input? and ;
: lf-tin-probe ( head a b -- n true | false )
  lf-term-view lf-tview-probe >r 1 0 r@ cons-room ok? 0=
  if 2drop drop r> drop false exit then
  r@ cand! r@ cons-top expr-hash true r> cons-find
  if lf-tin-child dup lf-term-input? dup 0= if nip then else drop false then ;
: lf-tin-app ( first second -- n true | false )
  2dup lf-tin-record? swap lf-tin-record? and
  if 1 rshift swap 1 rshift swap tag-app 0 pack-head -rot lf-tin-probe
  else 2drop false then ;
: lf-tin-bvar ( first second -- n true | false )
  over bvar-fits? over 0= and
  if tag-bvar 0 pack-head -rot lf-tin-probe else 2drop false then ;
: lf-tin-leaf-tag? ( tag -- flag ) lf-term-tag-bit lf-tin-leaf-tags @ and 0<> ;
: lf-tin-binder ( tag first second -- n true | false )
  2dup lf-term-input? swap lf-term-input? and
  if lf-tin-binder-find else 2drop drop false then ;
: lf-tin-sought ( tag first second -- n true | false )
  2 pick case
    lf-tag-app of rot drop lf-tin-app endof
    lf-tag-bvar of rot drop lf-tin-bvar endof
    lf-tag-lam of lf-tin-binder endof  lf-tag-pi of lf-tin-binder endof
    lf-tin-leaf-tag? if lf-tin-leaf-find else 2drop drop false then 0 endcase ;
\ An input node found may be given when it is reusable and findable (the
\ hook asked only of a reusable one).
: lf-tin-may? ( n -- flag )
  dup lf-term-reusable? if lf-term-findable? else drop false then ;
: lf-tin-given ( tag first second -- n true | false )
  lf-term-viewed? 0= if 2drop drop false exit then
  lf-tin-sought 0= if false exit then dup lf-tin-may? dup 0= if nip then ;
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

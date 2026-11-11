\ Bounded storage for the syntax of a small Lean expression subset: Sort,
\ bound variable, application, lambda and Pi nodes. Untrusted; not a kernel
\ API. Constructors validate indices and payload ranges only; they do not
\ check scope, types, universe semantics, declarations or proofs.
\ Each term is a tagged node (lib/node.fs) in a heap store (lib/store.fs)
\ that grows up to a capacity, a setting of each context (ADR 0016 C5,
\ C9 step 3; plan task 3.3.1): lf-term-capacity reads it,
\ lf-term-capacity! sets it, and a new context starts with
\ lf-term-default records. Running out is full, never accepted. Children
\ must already exist, so terms are acyclic DAGs. Per-term side data of
\ other modules lives in columns of the group lf-term-columns
\ (lib/store-columns.fs), which grow with the store.
\ Terms have no fixed depth (plan task 6.2.0): every pass keeps its
\ pending work on a stack in the heap that grows with the depth (walks,
\ frames, binder scopes); lf-walk-room is only the room a context's walk
\ starts with. A stack the heap cannot grow ends a pass full, never
\ accepted.
\ State: the store header lf-terms, a member of the checker context
\ (lib/context.fs) whose block is on the heap, freed by its teardown
\ word, so each context has its own terms; single-threaded within one
\ context. A reset invalidates every index, and a reused index cannot be
\ told from a stale one; identities never repeat and are what handles
\ check. Indices and identities mean something only in their own context.
\ No host address or cell layout is a portable serialization format.

require ../lib/lib.fs
require ./diagnostics.fs
require ../lib/store-columns.fs

64 constant lf-term-default
64 constant lf-walk-room     \ a walk's first room, in items
1 constant lf-tag-sort
2 constant lf-tag-bvar
3 constant lf-tag-app
4 constant lf-tag-lam
5 constant lf-tag-pi

store-header context-record: lf-terms
: lf-terms-make ( -- )
  lf-term-default /node 0 lf-terms store-heap-init ok? 0= abort" terms: no heap" ;
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
\ Node address; the index must already be validated.
: lf-term-slot ( index -- addr ) lf-terms store-slot ;

\ Empty the store and advance its generation (see store-clear).
: lf-term-reset ( -- ) lf-terms store-clear ;

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

\ Append a node whose tag and fields the caller validated, first growing
\ the store and its columns when every record is in use. An invalid
\ count, a full store (at its capacity, or no heap) or a spent serial
\ returns false, changes nothing and is recorded as a diagnostic.
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
: lf-term-new ( tag first second -- index true | false )
  lf-terms node-new dup 0= if drop lf-term-refused then ;
: lf-term-add ( tag first second -- index true | false )
  lf-term-room? if lf-term-new else 2drop drop lf-term-refused then ;

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
: lf-term-binary-tag? ( tag -- flag ) lf-tag-app lf-tag-pi 1+ within ;
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

\ Lean's cached node data (compact-store plan step S2): the data word of
\ ADR 0016 C1, bits 0-19 the loose bound-variable range (1 + the largest
\ loose index, or 0: Lean's loose_bvar_range), bit 20 set when a universe
\ parameter occurs (has_param_univ), bit 21 when a free variable occurs
\ (has_fvar). lf-term-data@ gives it when it is known, else false; a
\ caller then finds what it needs by walking, as before. Until the
\ compact store keeps it in each record (plan step S3), kernel/caches.fs
\ serves it from its skeleton memo while the caches are on; without that
\ module, or with the caches off, nothing is known, nor is a range of
\ 20 bits or more. The hook is set once, at load time, and shared.
defer lf-term-data@ ( node -- data true | false )
:noname ( node -- false ) drop false ; is lf-term-data@
1 20 lshift constant lf-data-ranges   \ the ranges a data word holds
: lf-data-loose ( data -- range ) lf-data-ranges 1- and ;
: lf-data-params? ( data -- flag ) lf-data-ranges and 0<> ;
: lf-data-fvar? ( data -- flag ) lf-data-ranges 2* and 0<> ;
\ The data word of a range below lf-data-ranges and two flags.
: lf-data ( range params? fvar? -- data )
  lf-data-ranges 2* and swap lf-data-ranges and or or ;

\ Read a node's tag and fields. An index that is not allocated returns
\ only false and no memory is read (the header is the root's to check).
: lf-term-read ( index -- tag first second true | false ) lf-terms node-read ;
\ One field of a node. Unchecked: the index must already be validated,
\ for instance by an earlier lf-term-read of the same node, under a
\ checked root; no field read checks the header.
: lf-term-tag@ ( index -- tag ) lf-term-slot node-tag @ ;
: lf-term-first@ ( index -- first ) lf-term-slot node-first @ ;
: lf-term-second@ ( index -- second ) lf-term-slot node-second @ ;

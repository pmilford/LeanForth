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
\ (store-columns.fs), which grow with the store.
\ The deepest nesting the passes support (work stacks, frames, binder
\ contexts) is lf-depth-limit, a constant that no longer follows the
\ store's capacity: a term deeper than that ends a pass full or
\ exhausted, never accepted.
\ State: the store header lf-terms, a member of the checker context
\ (lib/context.fs) whose block is on the heap, freed by its teardown
\ word, so each context has its own terms; single-threaded within one
\ context. A reset invalidates every index, and a reused index cannot be
\ told from a stale one; identities never repeat and are what handles
\ check. Indices and identities mean something only in their own context.
\ No host address or cell layout is a portable serialization format.

require ../lib/lib.fs
require ./diagnostics.fs
require ./store-columns.fs

64 constant lf-term-default
64 constant lf-depth-limit
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

\ The store's fields under their established names. Other modules save and
\ restore lf-term-count to roll back a failed transaction, and tests corrupt
\ these cells on purpose to check that every operation fails closed.
: lf-term-count ( -- addr ) lf-terms store-count ;
: lf-term-generation ( -- addr ) lf-terms store-generation ;
: lf-term-serial ( -- addr ) lf-terms store-serial ;
: lf-term-identities ( -- addr ) lf-terms store-identities ;
\ Node address; the index must already be validated.
: lf-term-slot ( index -- addr ) lf-terms store-slot ;

\ Empty the store and advance its generation (see store-clear).
: lf-term-reset ( -- ) lf-terms store-clear ;
: lf-term-count-valid? ( -- flag ) lf-terms store-count-valid? ;
: lf-term-valid? ( index -- flag ) lf-terms store-valid? ;
\ A live node's identity; identities never roll back and never wrap.
: lf-term-identity ( index -- identity true | false ) lf-terms store-identity@ ;

\ Append a node whose tag and fields the caller validated, first growing
\ the store and its columns when every record is in use. An invalid
\ count, a full store (at its capacity, or no heap) or a spent serial
\ returns false, changes nothing and is recorded as a diagnostic.
: lf-term-site ( -- site ) c" terms lf-term-add" ;
: lf-term-refused ( -- false )
  lf-terms lf-term-site lf-diag-terms-full lf-diag-store false ;
: lf-term-room? ( -- flag )
  lf-terms store-grow ok? if lf-term-columns columns-cover ok? else false then ;
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

\ Read a node's tag and fields. An invalid index returns only false and no
\ memory is read.
: lf-term-read ( index -- tag first second true | false ) lf-terms node-read ;
\ One field of a node. Unchecked: the index must already be validated,
\ for instance by an earlier lf-term-read of the same node.
: lf-term-tag@ ( index -- tag ) lf-term-slot node-tag @ ;
: lf-term-first@ ( index -- first ) lf-term-slot node-first @ ;
: lf-term-second@ ( index -- second ) lf-term-slot node-second @ ;

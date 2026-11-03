\ Bounded storage for the syntax of a small Lean expression subset: Sort,
\ bound variable, application, lambda and Pi nodes. Untrusted; not a kernel
\ API. Constructors validate indices and payload ranges only; they do not
\ check scope, types, universe semantics, declarations or proofs.
\ Each term is a tagged node (lib/node.fs) in a bounded store
\ (lib/store.fs). Children must already exist, so terms are acyclic DAGs.
\ State: the store lf-terms, a member of the checker context
\ (lib/context.fs), so each context has its own terms; single-threaded
\ within one context. A reset invalidates every index, and a reused index
\ cannot be told from a stale one; identities never repeat and are what
\ handles check. Indices and identities mean something only in their own
\ context. No host address or cell layout is a portable serialization
\ format.

require ../lib/lib.fs

64 constant lf-term-capacity
1 constant lf-tag-sort
2 constant lf-tag-bvar
3 constant lf-tag-app
4 constant lf-tag-lam
5 constant lf-tag-pi

lf-term-capacity /node 0 context-store: lf-terms

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

\ Append a node whose tag and fields the caller validated. An invalid count,
\ a full store or a spent serial returns false and changes nothing.
: lf-term-add ( tag first second -- index true | false ) lf-terms node-new ;

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

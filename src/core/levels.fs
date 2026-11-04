\ Bounded storage for symbolic Lean-style universe level syntax: zero,
\ successor, max, imax and parameters. Untrusted. This module does not decide
\ level equality, validate parameter scope, check declarations or confer
\ theorem validity. Parameter identifiers are opaque positive cell values,
\ not a complete Lean name representation.
\ Each level is a tagged node (lib/node.fs) in a heap store
\ (lib/store.fs) whose record 0 is always the zero level, growing up to a
\ capacity that is a setting of each context, as for terms (terms.fs):
\ lf-level-capacity reads it, lf-level-capacity! sets it, a new context
\ starts with lf-level-default. Per-level side data of other modules lives
\ in columns of the group lf-level-columns (lib/store-columns.fs). Level
\ graphs have no fixed depth (plan task 6.2.0): lf-level-walk-room is
\ only the room a level walk starts with.
\ State: the store header lf-levels, a member of the checker context
\ (lib/context.fs) whose block is on the heap, made and reset by set-up
\ words in every context and freed by its teardown word; single-threaded
\ within one context. A reset invalidates all indices. The cell layout is
\ host-specific and must never be serialized directly.

require ../lib/lib.fs
require ./diagnostics.fs
require ../lib/store-columns.fs

64 constant lf-level-default
64 constant lf-level-walk-room   \ a level walk's first room
0 constant lf-level-tag-zero
1 constant lf-level-tag-succ
2 constant lf-level-tag-max
3 constant lf-level-tag-imax
4 constant lf-level-tag-param

store-header context-record: lf-levels
: lf-levels-make ( -- )
  lf-level-default /node 1 lf-levels store-heap-init ok? 0= abort" levels: no heap" ;
' lf-levels-make context-setup
:noname ( -- ) lf-levels store-heap-free ; context-teardown
\ The capacity setting of this context, and setting it (as for terms).
: lf-level-capacity ( -- n ) lf-levels store-limit @ ;
: lf-level-capacity! ( n -- outcome ) lf-levels store-limit! ;

\ The store's fields under their established names; other modules roll back
\ lf-level-count, and tests corrupt these cells to check fail-closed behavior.
: lf-level-count ( -- addr ) lf-levels store-count ;
: lf-level-generation ( -- addr ) lf-levels store-generation ;
: lf-level-serial ( -- addr ) lf-levels store-serial ;
: lf-level-identities ( -- addr ) lf-levels store-identities ;
\ Node address; the index must already be validated.
: lf-level-slot ( index -- addr ) lf-levels store-slot ;

\ Discard every level and claim record 0 as the zero level with a fresh
\ identity. Unchecked: the serial must not be spent; lf-level-reset checks.
: lf-level-restart ( -- ) 0 lf-level-count ! lf-levels store-claim lf-level-slot /node erase ;
\ Reset to the zero level alone and advance the generation. A spent identity
\ serial poisons the store instead of reusing an identity.
: lf-level-reset ( -- )
  lf-levels store-spent? if lf-levels store-poison exit then
  lf-level-restart lf-levels store-epoch+ ;

\ Count and index checks; a valid store always holds the zero level. They
\ cannot detect stale indices reused after a reset, or corrupted fields.
: lf-level-count-valid? ( -- flag ) lf-levels store-count-valid? ;
: lf-level-valid? ( index -- flag ) lf-levels store-valid? ;
\ A live node's identity, including the zero level's; never repeats.
: lf-level-identity ( index -- identity true | false ) lf-levels store-identity@ ;

\ Append a node whose tag and fields the caller validated; a failed
\ allocation returns false, changes nothing and is recorded as a
\ diagnostic.
: lf-level-site ( -- site ) c" levels lf-level-add" ;
: lf-level-refused ( -- false )
  lf-levels lf-level-site lf-diag-levels-full lf-diag-store false ;
' lf-levels column-group: lf-level-columns
1 cells context-record: lf-level-covered   \ capacity the columns last covered
\ The usual case first: a free record and columns that cover the store.
: lf-level-steady? ( -- flag )
  lf-levels dup store-filled? 0= swap store-capacity @ lf-level-covered @ = and ;
: lf-level-room? ( -- flag )
  lf-level-steady? if true exit then
  lf-levels store-ready ok? if lf-level-covered lf-level-columns columns-ready else false then ;
: lf-level-new ( tag first second -- index true | false )
  lf-levels node-new dup 0= if drop lf-level-refused then ;
: lf-level-add ( tag first second -- index true | false )
  lf-level-room? if lf-level-new else 2drop drop lf-level-refused then ;

\ Successor of an existing level; the second field is unused.
: lf-level-succ ( child -- index true | false )
  dup lf-level-valid? if lf-level-tag-succ swap 0 lf-level-add else drop false then ;
\ Parameter carrying an opaque, positive name identifier.
: lf-level-param ( name-id -- index true | false )
  dup 0> if lf-level-tag-param swap 0 lf-level-add else drop false then ;

\ max or imax of two existing levels, stored as syntax without simplifying
\ or asserting any equality. The tag range relies on imax = max + 1.
lf-level-tag-imax lf-level-tag-max 1+ <>
[if] .( levels.fs: max and imax tags must be consecutive) cr abort [then]
: lf-level-binary-tag? ( tag -- flag ) lf-level-tag-max lf-level-tag-imax 1+ within ;
: lf-level-pair-valid? ( left right -- flag ) lf-levels store-pair-valid? ;
: lf-level-binary ( left right tag -- index true | false )
  >r 2dup lf-level-pair-valid? r@ lf-level-binary-tag? and
  if r> -rot lf-level-add else r> drop 2drop false then ;
: lf-level-max ( left right -- index true | false ) lf-level-tag-max lf-level-binary ;
: lf-level-imax ( left right -- index true | false ) lf-level-tag-imax lf-level-binary ;

\ Read an allocated node. A valid index alone does not authenticate fields.
: lf-level-read ( index -- tag first second true | false ) lf-levels node-read ;
\ One field of a node. Unchecked: the index must already be validated,
\ for instance by an earlier lf-level-read of the same node.
: lf-level-tag@ ( index -- tag ) lf-level-slot node-tag @ ;
: lf-level-first@ ( index -- first ) lf-level-slot node-first @ ;
: lf-level-second@ ( index -- second ) lf-level-slot node-second @ ;

\ Every context starts with the zero level alone, and with its columns.
' lf-level-reset context-setup
:noname ( -- ) lf-level-columns columns-setup ; context-setup
:noname ( -- ) lf-level-columns columns-free ; context-teardown

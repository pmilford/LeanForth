\ Bounded storage for symbolic Lean-style universe level syntax: zero,
\ successor, max, imax and parameters. Untrusted. This module does not decide
\ level equality, validate parameter scope, check declarations or confer
\ theorem validity. Parameter identifiers are opaque positive cell values,
\ not a complete Lean name representation.
\ Each level is a tagged node (lib/node.fs) in a bounded store
\ (lib/store.fs) whose record 0 is always the zero level. Global,
\ single-threaded and not re-entrant; a reset invalidates all indices. The
\ cell layout is host-specific and must never be serialized directly.

require ../lib/lib.fs

64 constant lf-level-capacity
0 constant lf-level-tag-zero
1 constant lf-level-tag-succ
2 constant lf-level-tag-max
3 constant lf-level-tag-imax
4 constant lf-level-tag-param

lf-level-capacity /node 1 store: lf-levels

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
\ allocation returns false and changes nothing.
: lf-level-add ( tag first second -- index true | false ) lf-levels node-new ;

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

lf-level-reset

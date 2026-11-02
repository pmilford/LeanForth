\ Untrusted bounded storage for symbolic Lean-style universe syntax.
\ This module does not decide level equality, validate parameter scope, check
\ declarations, or confer theorem validity. Parameter identifiers are opaque
\ positive host-cell integers, not a complete Lean name representation.
\ Global mutable storage is single-threaded; reset invalidates all indices.
\ The three-cell layout is host-specific and must never be serialized directly.

64 constant lf-level-capacity
0 constant lf-level-tag-zero
1 constant lf-level-tag-succ
2 constant lf-level-tag-max
3 constant lf-level-tag-imax
4 constant lf-level-tag-param
create lf-level-storage lf-level-capacity 3 * cells allot
variable lf-level-count
variable lf-level-generation
variable lf-level-serial
create lf-level-identities lf-level-capacity cells allot

\ Return a slot address; the caller must ensure the index is in bounds.
: lf-level-slot ( index -- addr ) 3 * cells lf-level-storage + ;

\ Reset to the implicit zero node at index zero, invalidating all old indices.
: lf-level-reset ( -- )
  lf-level-serial @ -1 1 rshift = if
    0 lf-level-count ! -1 lf-level-generation ! exit
  then
  1 lf-level-serial +!
  lf-level-serial @ lf-level-identities !
  0 lf-level-slot dup 0 swap ! dup cell+ 0 swap ! 2 cells + 0 swap !
  1 lf-level-count !
  \ Saturation fails closed instead of wrapping and reusing an old generation.
  lf-level-generation @ dup 0< if drop exit then
  dup -1 1 rshift = if drop -1 else 1+ then lf-level-generation ! ;

\ Check that the mutable count is in its valid range, including the zero node.
: lf-level-count-valid? ( -- flag )
  lf-level-count @ dup 1 >= swap lf-level-capacity <= and
  lf-level-generation @ 0< 0= and ;

\ Test whether an index is currently allocated. It cannot detect stale indices
\ reused after reset, or corruption of the node fields themselves.
: lf-level-valid? ( index -- flag )
  lf-level-count-valid? 0= if drop false exit then
  dup 0< 0= swap lf-level-count @ < and ;

\ Append a node whose tag and fields were already validated by its caller.
\ On invalid count or exhaustion return false without changing storage count.
: lf-level-add ( tag first second -- index true | false )
  lf-level-count-valid? 0= if 2drop drop false exit then
  lf-level-count @ lf-level-capacity >= if 2drop drop false exit then
  lf-level-serial @ -1 1 rshift = if 2drop drop false exit then
  1 lf-level-serial +!
  lf-level-serial @ lf-level-count @ cells lf-level-identities + !
  lf-level-count @ lf-level-slot >r
  r@ 2 cells + ! r@ cell+ ! r> !
  lf-level-count @ 1 lf-level-count +! true ;

\ Return a live node's non-repeating allocation identity, including zero.
: lf-level-identity ( index -- identity true | false )
  dup lf-level-valid? 0= if drop false exit then
  cells lf-level-identities + @ true ;

\ Construct a successor of an earlier level; the second field is unused.
: lf-level-succ ( child -- index true | false )
  dup lf-level-valid? 0= if drop false exit then
  lf-level-tag-succ swap 0 lf-level-add ;

\ Construct a parameter carrying an opaque, positive name identifier.
: lf-level-param ( name-id -- index true | false )
  dup 0<= if drop false exit then
  lf-level-tag-param swap 0 lf-level-add ;

\ Construct max or imax from two previously allocated level indices.
: lf-level-binary ( left right tag -- index true | false )
  dup lf-level-tag-max = over lf-level-tag-imax = or 0= if
    drop 2drop false exit
  then
  >r over lf-level-valid? over lf-level-valid? and 0= if
    r> drop 2drop false exit
  then
  r> -rot lf-level-add ;

\ Store max and imax syntax without simplifying it or asserting equality.
: lf-level-max ( left right -- index true | false )
  lf-level-tag-max lf-level-binary ;
: lf-level-imax ( left right -- index true | false )
  lf-level-tag-imax lf-level-binary ;

\ Read an allocated node. A valid index alone does not authenticate its fields.
: lf-level-read ( index -- tag first second true | false )
  dup lf-level-valid? 0= if drop false exit then
  lf-level-slot dup @ swap cell+ dup @ swap cell+ @ true ;

0 lf-level-generation !
0 lf-level-serial !
lf-level-reset

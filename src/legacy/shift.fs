\ Untrusted bounded de Bruijn shifting experiment over the term prototype.
\ It returns a transformed node or an explicit failure, never a theorem result.
\ The arena and traversal state are global, mutable, and not reentrant; neither
\ this implementation nor the representation is approved for a trusted kernel.
\ Only nonnegative values representable as signed host cells are supported.
include ../core/terms.fs

0 constant lf-shift-ok
1 constant lf-shift-invalid
2 constant lf-shift-exhausted
-1 1 rshift constant lf-shift-cell-max
7 constant lf-shift-frame-cells
create lf-shift-frames lf-term-capacity lf-shift-frame-cells * cells allot
variable lf-shift-level
variable lf-shift-fuel
variable lf-shift-start

\ Locate a frame; callers must supply a level inside the bounded frame array.
: lf-shift-frame ( level -- addr ) lf-shift-frame-cells * cells lf-shift-frames + ;

\ Return the active frame. A traversal frame must already have been pushed.
: lf-shift-current ( -- addr ) lf-shift-level @ 1- lf-shift-frame ;

\ Read or write a numbered cell in the active frame.
: lf-shift@ ( offset -- value ) cells lf-shift-current + @ ;
: lf-shift! ( value offset -- ) cells lf-shift-current + ! ;

\ Pop the current frame while preserving the result and status on the stack.
: lf-shift-leave ( result status -- result status ) -1 lf-shift-level +! ;

\ Convert a term constructor's optional result to an index and shift status.
: lf-shift-allocated ( index true | false -- index status )
  if lf-shift-ok else -1 lf-shift-exhausted then ;

\ The input child must precede its parent and belong to the original arena.
\ This prevents newly allocated outputs, cycles and forward references from
\ being interpreted as source nodes during a traversal.
: lf-shift-child? ( index -- flag )
  dup 0< 0= over 0 lf-shift@ < and swap lf-shift-start @ < and ;

\ Shift one source node. Each visited node consumes one unit of fuel, and each
\ nested call consumes one bounded frame. Output nodes are appended to the arena.
\ A variable below the cutoff is unchanged; otherwise its index is increased.
: lf-shift-walk ( node cutoff amount -- node status )
  lf-shift-fuel @ 0= lf-shift-level @ lf-term-capacity >= or if
    2drop drop -1 lf-shift-exhausted exit
  then
  -1 lf-shift-fuel +!
  lf-shift-level @ lf-shift-frame >r
  r@ 2 cells + ! r@ cell+ ! r> !
  1 lf-shift-level +!
  0 lf-shift@ dup 0< swap lf-shift-start @ >= or if
    -1 lf-shift-invalid lf-shift-leave exit
  then
  0 lf-shift@ lf-term-read 0= if
    -1 lf-shift-invalid lf-shift-leave exit
  then
  5 lf-shift! 4 lf-shift! 3 lf-shift!
  3 lf-shift@ lf-tag-sort = if
    4 lf-shift@ 0< 5 lf-shift@ 0<> or if
      -1 lf-shift-invalid else 0 lf-shift@ lf-shift-ok then
    lf-shift-leave exit
  then
  3 lf-shift@ lf-tag-bvar = if
    4 lf-shift@ 0< 5 lf-shift@ 0<> or if
      -1 lf-shift-invalid lf-shift-leave exit
    then
    4 lf-shift@ 1 lf-shift@ < if
      0 lf-shift@ lf-shift-ok lf-shift-leave exit
    then
    4 lf-shift@ lf-shift-cell-max 2 lf-shift@ - > if
      -1 lf-shift-exhausted lf-shift-leave exit
    then
    4 lf-shift@ 2 lf-shift@ + lf-term-bvar lf-shift-allocated
    lf-shift-leave exit
  then
  3 lf-shift@ lf-tag-app = 3 lf-shift@ lf-tag-lam = or
  3 lf-shift@ lf-tag-pi = or 0= if
    -1 lf-shift-invalid lf-shift-leave exit
  then
  4 lf-shift@ lf-shift-child? 5 lf-shift@ lf-shift-child? and 0= if
    -1 lf-shift-invalid lf-shift-leave exit
  then
  3 lf-shift@ lf-tag-app <> 1 lf-shift@ lf-shift-cell-max = and if
    -1 lf-shift-exhausted lf-shift-leave exit
  then
  4 lf-shift@ 1 lf-shift@ 2 lf-shift@ recurse
  dup if lf-shift-leave exit then drop 6 lf-shift!
  5 lf-shift@ 1 lf-shift@
  3 lf-shift@ lf-tag-app <> if 1+ then
  2 lf-shift@ recurse
  dup if lf-shift-leave exit then drop
  6 lf-shift@ swap 3 lf-shift@ lf-term-binary lf-shift-allocated
  lf-shift-leave ;

\ Shift loose indices at or above cutoff. Status is ok, invalid or exhausted;
\ on failure discard all nodes allocated by this traversal. The initial arena
\ and inputs must not be mutated concurrently. No status confers proof validity.
: lf-shift ( node cutoff amount fuel -- node status )
  dup 0< if 2drop 2drop -1 lf-shift-invalid exit then lf-shift-fuel !
  2dup 0< swap 0< or if 2drop drop -1 lf-shift-invalid exit then
  lf-term-count-valid? 0= if 2drop drop -1 lf-shift-invalid exit then
  lf-term-count @ lf-shift-start ! 0 lf-shift-level !
  lf-shift-walk
  dup if lf-shift-start @ lf-term-count ! then ;

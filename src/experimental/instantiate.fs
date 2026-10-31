\ Untrusted single-binder instantiation experiment over the term prototype.
\ This is syntax manipulation, not type checking or theorem acceptance. Its
\ global mutable arena, host-cell limits and bounded host recursion are not
\ approved for a trusted kernel. Inputs must not be mutated concurrently.
include shift.fs

lf-shift-ok constant lf-inst-ok
lf-shift-invalid constant lf-inst-invalid
lf-shift-exhausted constant lf-inst-exhausted
6 constant lf-inst-frame-cells
create lf-inst-frames lf-term-capacity lf-inst-frame-cells * cells allot
variable lf-inst-level
variable lf-inst-fuel
variable lf-inst-start
variable lf-inst-replacement

\ Return a traversal frame; callers must use a level inside the frame array.
: lf-inst-frame ( level -- addr ) lf-inst-frame-cells * cells lf-inst-frames + ;

\ Return the active frame; one must have been pushed already.
: lf-inst-current ( -- addr ) lf-inst-level @ 1- lf-inst-frame ;

\ Read or write a numbered cell in the active frame.
: lf-inst@ ( offset -- value ) cells lf-inst-current + @ ;
: lf-inst! ( value offset -- ) cells lf-inst-current + ! ;

\ Pop the active frame while preserving a result and status.
: lf-inst-leave ( result status -- result status ) -1 lf-inst-level +! ;

\ Ensure a child belongs to the original input and precedes its parent.
: lf-inst-child? ( index -- flag )
  dup 0< 0= over 0 lf-inst@ < and swap lf-inst-start @ < and ;

\ Shift a replacement with the remaining shared visit budget. The shift
\ module records unused fuel; allocation failures return a failure status.
: lf-inst-shift ( node amount -- result status )
  0 swap lf-inst-fuel @ lf-shift
  lf-shift-fuel @ lf-inst-fuel ! ;

\ Instantiate one source node at the supplied binder depth. A locally bound
\ variable is retained; the targeted loose variable is replaced with a shifted
\ copy; outer variables are lowered by one. Each visit consumes one fuel unit.
: lf-inst-walk ( node depth -- result status )
  lf-inst-fuel @ 0= lf-inst-level @ lf-term-capacity >= or if
    2drop -1 lf-inst-exhausted exit
  then
  -1 lf-inst-fuel +!
  lf-inst-level @ lf-inst-frame >r r@ cell+ ! r> !
  1 lf-inst-level +!
  0 lf-inst@ dup 0< swap lf-inst-start @ >= or if
    -1 lf-inst-invalid lf-inst-leave exit
  then
  0 lf-inst@ lf-term-read 0= if
    -1 lf-inst-invalid lf-inst-leave exit
  then
  4 lf-inst! 3 lf-inst! 2 lf-inst!
  2 lf-inst@ lf-tag-sort = if
    3 lf-inst@ 0< 4 lf-inst@ 0<> or if
      -1 lf-inst-invalid else 0 lf-inst@ lf-inst-ok then
    lf-inst-leave exit
  then
  2 lf-inst@ lf-tag-bvar = if
    3 lf-inst@ 0< 4 lf-inst@ 0<> or if
      -1 lf-inst-invalid lf-inst-leave exit
    then
    3 lf-inst@ 1 lf-inst@ < if
      0 lf-inst@ lf-inst-ok lf-inst-leave exit
    then
    3 lf-inst@ 1 lf-inst@ = if
      lf-inst-replacement @ 1 lf-inst@ lf-inst-shift
      lf-inst-leave exit
    then
    3 lf-inst@ 1- lf-term-bvar lf-shift-allocated lf-inst-leave exit
  then
  2 lf-inst@ lf-tag-app = 2 lf-inst@ lf-tag-lam = or
  2 lf-inst@ lf-tag-pi = or 0= if
    -1 lf-inst-invalid lf-inst-leave exit
  then
  3 lf-inst@ lf-inst-child? 4 lf-inst@ lf-inst-child? and 0= if
    -1 lf-inst-invalid lf-inst-leave exit
  then
  2 lf-inst@ lf-tag-app <> 1 lf-inst@ lf-shift-cell-max = and if
    -1 lf-inst-exhausted lf-inst-leave exit
  then
  3 lf-inst@ 1 lf-inst@ recurse
  dup if lf-inst-leave exit then drop 5 lf-inst!
  4 lf-inst@ 1 lf-inst@
  2 lf-inst@ lf-tag-app <> if 1+ then recurse
  dup if lf-inst-leave exit then drop
  5 lf-inst@ swap 2 lf-inst@ lf-term-binary lf-shift-allocated
  lf-inst-leave ;

\ Replace loose variable zero and remove its binder. First validate the full
\ replacement with a zero shift, discarding temporary copies; then process the
\ root. Both operations draw from one visit budget. On any failure, discard
\ all newly allocated nodes by restoring the original allocation count.
: lf-instantiate ( root replacement fuel -- result status )
  dup 0< if drop 2drop -1 lf-inst-invalid exit then lf-inst-fuel !
  lf-term-count-valid? 0= if 2drop -1 lf-inst-invalid exit then
  dup lf-term-valid? 0= if 2drop -1 lf-inst-invalid exit then
  lf-inst-replacement ! lf-term-count @ lf-inst-start !
  lf-inst-replacement @ 0 lf-inst-shift
  dup if nip nip -1 swap exit then 2drop
  lf-inst-start @ lf-term-count ! 0 lf-inst-level !
  0 lf-inst-walk
  dup if lf-inst-start @ lf-term-count ! then ;

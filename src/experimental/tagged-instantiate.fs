\ Untrusted single-binder substitution for tagged symbolic handles.
\ Dependencies including tagged-shift.fs must already be loaded. Global state
\ is non-reentrant; callers must not mutate arenas concurrently. This is
\ syntax transformation, not type checking or theorem acceptance.
lf-tshift-ok constant lf-tinst-ok
lf-tshift-invalid constant lf-tinst-invalid
lf-tshift-exhausted constant lf-tinst-exhausted
6 constant lf-tinst-frame-cells
create lf-tinst-frames lf-term-capacity lf-tinst-frame-cells * cells allot
variable lf-tinst-level
variable lf-tinst-fuel
variable lf-tinst-start
variable lf-tinst-replacement

\ Return a traversal frame; callers must use a level inside the frame array.
: lf-tinst-frame ( level -- addr ) lf-tinst-frame-cells * cells lf-tinst-frames + ;

\ Return the active frame; one must have been pushed already.
: lf-tinst-current ( -- addr ) lf-tinst-level @ 1- lf-tinst-frame ;

\ Read or write a numbered cell in the active frame.
: lf-tinst@ ( offset -- value ) cells lf-tinst-current + @ ;
: lf-tinst! ( value offset -- ) cells lf-tinst-current + ! ;

\ Pop the active frame while preserving a result and status.
: lf-tinst-leave ( result status -- result status ) -1 lf-tinst-level +! ;

\ Ensure a child belongs to the original input and precedes its parent.
: lf-tinst-child? ( index -- flag )
  dup 0< 0= over 0 lf-tinst@ < and swap lf-tinst-start @ < and ;

\ Shift a replacement with the remaining shared visit budget. The shift
\ module records unused fuel; allocation failures return a failure status.
: lf-tinst-shift ( node amount -- result status )
  0 lf-tshift-level !
  lf-tinst-start @ lf-tshift-start !
  lf-tinst-fuel @ lf-tshift-fuel !
  0 swap lf-tshift-walk
  lf-tshift-fuel @ lf-tinst-fuel ! ;

\ Instantiate one source node at the supplied binder depth. A locally bound
\ variable is retained; the targeted loose variable is replaced with a shifted
\ copy; outer variables are lowered by one. Each visit consumes one fuel unit.
: lf-tinst-walk ( node depth -- result status )
  lf-tinst-fuel @ 0= lf-tinst-level @ lf-term-capacity >= or if
    2drop -1 lf-tinst-exhausted exit
  then
  -1 lf-tinst-fuel +!
  lf-tinst-level @ lf-tinst-frame >r r@ cell+ ! r> !
  1 lf-tinst-level +!
  0 lf-tinst@ dup 0< swap lf-tinst-start @ >= or if
    -1 lf-tinst-invalid lf-tinst-leave exit
  then
  0 lf-tinst@ lf-term-read 0= if
    -1 lf-tinst-invalid lf-tinst-leave exit
  then
  4 lf-tinst! 3 lf-tinst! 2 lf-tinst!
  2 lf-tinst@ lf-tag-symbolic-sort = if
    3 lf-tinst@ 0< 4 lf-tinst@ 0<> or if
      -1 lf-tinst-invalid else 0 lf-tinst@ lf-tinst-ok then
    lf-tinst-leave exit
  then
  2 lf-tinst@ lf-tag-bvar = if
    3 lf-tinst@ 0< 4 lf-tinst@ 0<> or if
      -1 lf-tinst-invalid lf-tinst-leave exit
    then
    3 lf-tinst@ 1 lf-tinst@ < if
      0 lf-tinst@ lf-tinst-ok lf-tinst-leave exit
    then
    3 lf-tinst@ 1 lf-tinst@ = if
      lf-tinst-replacement @ 1 lf-tinst@ lf-tinst-shift
      lf-tinst-leave exit
    then
    3 lf-tinst@ 1- lf-term-bvar lf-tshift-allocated lf-tinst-leave exit
  then
  2 lf-tinst@ lf-tag-app = 2 lf-tinst@ lf-tag-lam = or
  2 lf-tinst@ lf-tag-pi = or 0= if
    -1 lf-tinst-invalid lf-tinst-leave exit
  then
  3 lf-tinst@ lf-tinst-child? 4 lf-tinst@ lf-tinst-child? and 0= if
    -1 lf-tinst-invalid lf-tinst-leave exit
  then
  2 lf-tinst@ lf-tag-app <> 1 lf-tinst@ lf-tshift-cell-max = and if
    -1 lf-tinst-exhausted lf-tinst-leave exit
  then
  3 lf-tinst@ 1 lf-tinst@ recurse
  dup if lf-tinst-leave exit then drop 5 lf-tinst!
  4 lf-tinst@ 1 lf-tinst@
  2 lf-tinst@ lf-tag-app <> if 1+ then recurse
  dup if lf-tinst-leave exit then drop
  5 lf-tinst@ swap 2 lf-tinst@ lf-term-binary lf-tshift-allocated
  lf-tinst-leave ;

\ Validate both complete handles with one fuel budget before allocating, even
\ when the replacement is unused. Roll back term allocations on every failure;
\ allocation serials are intentionally never rewound. Sort nodes are reused.
\ Failed validation leaves zero remaining fuel as a conservative bound.
\ ( source source-id replacement replacement-id fuel -- result result-id status )
: lf-tagged-instantiate ( source sid replacement rid fuel -- result id status )
  dup 0< if drop 2drop 2drop -1 0 lf-tinst-invalid exit then
  lf-tinst-fuel !
  2over lf-tinst-fuel @ lf-hterm-check
  dup if 0 lf-tinst-fuel ! >r 2drop 2drop -1 0 r> exit then drop
  lf-href-fuel @ lf-tinst-fuel !
  2dup lf-tinst-fuel @ lf-hterm-check
  dup if 0 lf-tinst-fuel ! >r 2drop 2drop -1 0 r> exit then drop
  lf-href-fuel @ lf-tinst-fuel !
  drop lf-tinst-replacement ! drop
  lf-term-count @ lf-tinst-start ! 0 lf-tinst-level !
  0 lf-tinst-walk
  dup if lf-tinst-start @ lf-term-count ! nip -1 0 rot exit then
  drop dup lf-term-identity 0= if
    drop lf-tinst-start @ lf-term-count ! -1 0 lf-tinst-invalid exit
  then lf-tinst-ok ;

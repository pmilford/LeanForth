\ Untrusted capture-avoiding single-binder instantiation of mixed terms.
\ Load mixed-shift.fs and its dependencies first. Global state
\ is non-reentrant; callers must not mutate arenas concurrently. This is
\ syntax transformation, not type checking or theorem acceptance.
lf-mshift-ok constant lf-minst-ok
lf-mshift-invalid constant lf-minst-invalid
lf-mshift-exhausted constant lf-minst-exhausted
6 constant lf-minst-frame-cells
create lf-minst-frames lf-term-capacity lf-minst-frame-cells * cells allot
variable lf-minst-level
variable lf-minst-fuel
variable lf-minst-start
variable lf-minst-replacement

\ Return a traversal frame; callers must use a level inside the frame array.
: lf-minst-frame ( level -- addr ) lf-minst-frame-cells * cells lf-minst-frames + ;

\ Return the active frame; one must have been pushed already.
: lf-minst-current ( -- addr ) lf-minst-level @ 1- lf-minst-frame ;

\ Read or write a numbered cell in the active frame.
: lf-minst@ ( offset -- value ) cells lf-minst-current + @ ;
: lf-minst! ( value offset -- ) cells lf-minst-current + ! ;

\ Pop the active frame while preserving a result and status.
: lf-minst-leave ( result status -- result status ) -1 lf-minst-level +! ;

\ Ensure a child belongs to the original input and precedes its parent.
: lf-minst-child? ( index -- flag )
  dup 0< 0= over 0 lf-minst@ < and swap lf-minst-start @ < and ;

\ Shift a replacement with the remaining shared visit budget. The shift
\ module records unused fuel; allocation failures return a failure status.
: lf-minst-shift ( node amount -- result status )
  0 lf-mshift-depth !
  lf-mshift-amount !
  lf-minst-fuel @ lf-mshift-fuel !
  0 lf-mshift-walk
  lf-mshift-fuel @ lf-minst-fuel ! ;

\ Instantiate one source node at the supplied binder depth. A locally bound
\ variable is retained; the targeted loose variable is replaced with a shifted
\ copy; outer variables are lowered by one. Each visit consumes one fuel unit.
: lf-minst-walk ( node depth -- result status )
  lf-minst-fuel @ 0= lf-minst-level @ lf-term-capacity >= or if
    2drop -1 lf-minst-exhausted exit
  then
  -1 lf-minst-fuel +!
  lf-minst-level @ lf-minst-frame >r r@ cell+ ! r> !
  1 lf-minst-level +!
  0 lf-minst@ dup 0< swap lf-minst-start @ >= or if
    -1 lf-minst-invalid lf-minst-leave exit
  then
  0 lf-minst@ lf-term-read 0= if
    -1 lf-minst-invalid lf-minst-leave exit
  then
  4 lf-minst! 3 lf-minst! 2 lf-minst!
  2 lf-minst@ lf-tag-symbolic-sort =
  2 lf-minst@ lf-tag-constant = or if
    0 lf-minst@ lf-minst-ok lf-minst-leave exit
  then
  2 lf-minst@ lf-tag-bvar = if
    3 lf-minst@ 0< 4 lf-minst@ 0<> or if
      -1 lf-minst-invalid lf-minst-leave exit
    then
    3 lf-minst@ 1 lf-minst@ < if
      0 lf-minst@ lf-minst-ok lf-minst-leave exit
    then
    3 lf-minst@ 1 lf-minst@ = if
      lf-minst-replacement @ 1 lf-minst@ lf-minst-shift
      lf-minst-leave exit
    then
    3 lf-minst@ 1- lf-term-bvar lf-mshift-allocated lf-minst-leave exit
  then
  2 lf-minst@ lf-tag-app = 2 lf-minst@ lf-tag-lam = or
  2 lf-minst@ lf-tag-pi = or 0= if
    -1 lf-minst-invalid lf-minst-leave exit
  then
  3 lf-minst@ lf-minst-child? 4 lf-minst@ lf-minst-child? and 0= if
    -1 lf-minst-invalid lf-minst-leave exit
  then
  2 lf-minst@ lf-tag-app <> 1 lf-minst@ lf-mshift-max = and if
    -1 lf-minst-exhausted lf-minst-leave exit
  then
  3 lf-minst@ 1 lf-minst@ recurse
  dup if lf-minst-leave exit then drop 5 lf-minst!
  4 lf-minst@ 1 lf-minst@
  2 lf-minst@ lf-tag-app <> if 1+ then recurse
  dup if lf-minst-leave exit then drop
  5 lf-minst@ swap 2 lf-minst@ lf-term-binary lf-mshift-allocated
  lf-minst-leave ;

\ Validate both complete handles with one fuel budget before allocating, even
\ when the replacement is unused. Roll back term allocations on every failure;
\ allocation serials are intentionally never rewound. Constant and Sort nodes are reused with their stamps.
\ Identities are session-local; resets invalidate handles. Child indices rely
\ on backward edges and no raw mutation or count edits during their lifetime.
\ Fuel charges both audits, source visits and each replacement shift visit.
\ No type, scope, proof, or executable-program correctness is established.
\ Failed validation leaves zero remaining fuel as a conservative bound.
\ ( source source-id replacement replacement-id fuel -- result result-id status )
: lf-mixed-instantiate ( source sid replacement rid fuel -- result id status )
  dup 0< if 0 lf-minst-fuel ! drop 2drop 2drop -1 0 lf-minst-invalid exit then
  lf-minst-fuel !
  2over lf-minst-fuel @ lf-cterm-check
  dup if 0 lf-minst-fuel ! >r 2drop 2drop
    r> lf-repr-exhausted = if -1 0 lf-minst-exhausted
    else -1 0 lf-minst-invalid then exit then drop
  lf-cterm-fuel @ lf-minst-fuel !
  2dup lf-minst-fuel @ lf-cterm-check
  dup if 0 lf-minst-fuel ! >r 2drop 2drop
    r> lf-repr-exhausted = if -1 0 lf-minst-exhausted
    else -1 0 lf-minst-invalid then exit then drop
  lf-cterm-fuel @ lf-minst-fuel !
  drop lf-minst-replacement ! drop
  lf-term-count @ lf-minst-start ! 0 lf-minst-level !
  0 lf-minst-walk
  dup if lf-minst-start @ lf-term-count ! nip -1 0 rot exit then
  drop dup lf-term-identity 0= if
    drop lf-minst-start @ lf-term-count ! -1 0 lf-minst-invalid exit
  then lf-minst-ok ;

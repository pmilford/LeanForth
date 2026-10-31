\ Untrusted bounded de Bruijn shifting experiment over the term prototype.
\ It returns a transformed node or an explicit failure, never a theorem result.
\ The arena and traversal state are global, mutable, and not reentrant; neither
\ this implementation nor the representation is approved for a trusted kernel.
\ Only nonnegative values representable as signed host cells are supported.
\ Dependencies: terms.fs, levels.fs, level-scope.fs, tagged-sort-boundary.fs,
\ symbolic-session.fs and generation-handles.fs must already be loaded.

0 constant lf-tshift-ok
1 constant lf-tshift-invalid
2 constant lf-tshift-exhausted
-1 1 rshift constant lf-tshift-cell-max
7 constant lf-tshift-frame-cells
create lf-tshift-frames lf-term-capacity lf-tshift-frame-cells * cells allot
variable lf-tshift-level
variable lf-tshift-fuel
variable lf-tshift-start
variable lf-tshift-cutoff
variable lf-tshift-amount

\ Locate a frame; callers must supply a level inside the bounded frame array.
: lf-tshift-frame ( level -- addr ) lf-tshift-frame-cells * cells lf-tshift-frames + ;

\ Return the active frame. A traversal frame must already have been pushed.
: lf-tshift-current ( -- addr ) lf-tshift-level @ 1- lf-tshift-frame ;

\ Read or write a numbered cell in the active frame.
: lf-tshift@ ( offset -- value ) cells lf-tshift-current + @ ;
: lf-tshift! ( value offset -- ) cells lf-tshift-current + ! ;

\ Pop the current frame while preserving the result and status on the stack.
: lf-tshift-leave ( result status -- result status ) -1 lf-tshift-level +! ;

\ Convert a term constructor's optional result to an index and shift status.
: lf-tshift-allocated ( index true | false -- index status )
  if lf-tshift-ok else -1 lf-tshift-exhausted then ;

\ The input child must precede its parent and belong to the original arena.
\ This prevents newly allocated outputs, cycles and forward references from
\ being interpreted as source nodes during a traversal.
: lf-tshift-child? ( index -- flag )
  dup 0< 0= over 0 lf-tshift@ < and swap lf-tshift-start @ < and ;

\ Shift one source node. Each visited node consumes one unit of fuel, and each
\ nested call consumes one bounded frame. Output nodes are appended to the arena.
\ A variable below the cutoff is unchanged; otherwise its index is increased.
: lf-tshift-walk ( node cutoff amount -- node status )
  lf-tshift-fuel @ 0= lf-tshift-level @ lf-term-capacity >= or if
    2drop drop -1 lf-tshift-exhausted exit
  then
  -1 lf-tshift-fuel +!
  lf-tshift-level @ lf-tshift-frame >r
  r@ 2 cells + ! r@ cell+ ! r> !
  1 lf-tshift-level +!
  0 lf-tshift@ dup 0< swap lf-tshift-start @ >= or if
    -1 lf-tshift-invalid lf-tshift-leave exit
  then
  0 lf-tshift@ lf-term-read 0= if
    -1 lf-tshift-invalid lf-tshift-leave exit
  then
  5 lf-tshift! 4 lf-tshift! 3 lf-tshift!
  3 lf-tshift@ lf-tag-symbolic-sort = if
    4 lf-tshift@ 0< 5 lf-tshift@ 0<> or if
      -1 lf-tshift-invalid else 0 lf-tshift@ lf-tshift-ok then
    lf-tshift-leave exit
  then
  3 lf-tshift@ lf-tag-bvar = if
    4 lf-tshift@ 0< 5 lf-tshift@ 0<> or if
      -1 lf-tshift-invalid lf-tshift-leave exit
    then
    4 lf-tshift@ 1 lf-tshift@ < if
      0 lf-tshift@ lf-tshift-ok lf-tshift-leave exit
    then
    4 lf-tshift@ lf-tshift-cell-max 2 lf-tshift@ - > if
      -1 lf-tshift-exhausted lf-tshift-leave exit
    then
    4 lf-tshift@ 2 lf-tshift@ + lf-term-bvar lf-tshift-allocated
    lf-tshift-leave exit
  then
  3 lf-tshift@ lf-tag-app = 3 lf-tshift@ lf-tag-lam = or
  3 lf-tshift@ lf-tag-pi = or 0= if
    -1 lf-tshift-invalid lf-tshift-leave exit
  then
  4 lf-tshift@ lf-tshift-child? 5 lf-tshift@ lf-tshift-child? and 0= if
    -1 lf-tshift-invalid lf-tshift-leave exit
  then
  3 lf-tshift@ lf-tag-app <> 1 lf-tshift@ lf-tshift-cell-max = and if
    -1 lf-tshift-exhausted lf-tshift-leave exit
  then
  4 lf-tshift@ 1 lf-tshift@ 2 lf-tshift@ recurse
  dup if lf-tshift-leave exit then drop 6 lf-tshift!
  5 lf-tshift@ 1 lf-tshift@
  3 lf-tshift@ lf-tag-app <> if 1+ then
  2 lf-tshift@ recurse
  dup if lf-tshift-leave exit then drop
  6 lf-tshift@ swap 3 lf-tshift@ lf-term-binary lf-tshift-allocated
  lf-tshift-leave ;

\ Shift a live symbolic handle. Validation and shifting share one budget.
\ Success returns index identity ok; failure returns -1 0 status. The
\ original Sort nodes and their stamps are reused, never reconstructed.
\ Rollback restores the term count but deliberately does not rewind serials.
\ No raw mutation or concurrent access is permitted. Not a type judgment.
: lf-tagged-shift ( index identity cutoff amount fuel -- index identity status )
  dup 0< if 2drop 2drop drop -1 0 lf-tshift-invalid exit then
  lf-tshift-fuel !
  2dup 0< swap 0< or if 2drop 2drop -1 0 lf-tshift-invalid exit then
  lf-tshift-amount ! lf-tshift-cutoff !
  2dup lf-tshift-fuel @ lf-hterm-check
  dup if >r 2drop -1 0 r> exit then drop
  drop
  lf-href-fuel @ lf-tshift-fuel !
  lf-term-count @ lf-tshift-start ! 0 lf-tshift-level !
  lf-tshift-cutoff @ lf-tshift-amount @ lf-tshift-walk
  dup if lf-tshift-start @ lf-term-count ! nip -1 0 rot exit then
  drop dup lf-term-identity 0= if
    drop lf-tshift-start @ lf-term-count ! -1 0 lf-tshift-invalid exit
  then lf-tshift-ok ;

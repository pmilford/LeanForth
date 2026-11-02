\ Untrusted mixed-term shift. Load constant-term-boundary.fs and its
\ dependencies first. Structural transformation only; no proof judgment.
\ Global scratch and arenas are single-threaded, non-reentrant; exclude raw
\ mutation, resets and concurrent access during a call.
0 constant lf-mshift-ok
1 constant lf-mshift-invalid
2 constant lf-mshift-exhausted
-1 1 rshift constant lf-mshift-max
4 constant lf-mshift-frame-cells
create lf-mshift-frames lf-term-capacity lf-mshift-frame-cells * cells allot
variable lf-mshift-depth
variable lf-mshift-fuel
variable lf-mshift-start
variable lf-mshift-cutoff
variable lf-mshift-amount

: lf-mshift@ ( field -- value )
  cells lf-mshift-depth @ 1- lf-mshift-frame-cells * cells lf-mshift-frames + + @ ;
: lf-mshift! ( value field -- )
  cells lf-mshift-depth @ 1- lf-mshift-frame-cells * cells lf-mshift-frames + + ! ;
: lf-mshift-leave ( node status -- node status ) -1 lf-mshift-depth +! ;
: lf-mshift-allocated ( node true | false -- node status )
  if lf-mshift-ok else -1 lf-mshift-exhausted then ;

\ The preaudit establishes tags, payloads and backward edges. Each occurrence
\ in a DAG costs a visit; the bounded frame array also bounds recursion depth.
: lf-mshift-walk ( node cutoff -- node status )
  lf-mshift-fuel @ 0= lf-mshift-depth @ lf-term-capacity >= or if
    2drop -1 lf-mshift-exhausted exit
  then
  -1 lf-mshift-fuel +! 1 lf-mshift-depth +!
  1 lf-mshift! 0 lf-mshift!
  0 lf-mshift@ lf-term-read 0= if
    -1 lf-mshift-invalid lf-mshift-leave exit
  then
  drop 2 lf-mshift! 3 lf-mshift!
  3 lf-mshift@ lf-tag-symbolic-sort =
  3 lf-mshift@ lf-tag-constant = or if
    0 lf-mshift@ lf-mshift-ok lf-mshift-leave exit
  then
  3 lf-mshift@ lf-tag-bvar = if
    2 lf-mshift@ 1 lf-mshift@ < if
      0 lf-mshift@ lf-mshift-ok lf-mshift-leave exit
    then
    2 lf-mshift@ lf-mshift-max lf-mshift-amount @ - > if
      -1 lf-mshift-exhausted lf-mshift-leave exit
    then
    2 lf-mshift@ lf-mshift-amount @ + lf-term-bvar lf-mshift-allocated
    lf-mshift-leave exit
  then
  3 lf-mshift@ lf-tag-app <> 1 lf-mshift@ lf-mshift-max = and if
    -1 lf-mshift-exhausted lf-mshift-leave exit
  then
  2 lf-mshift@ 1 lf-mshift@ recurse
  dup if lf-mshift-leave exit then drop 2 lf-mshift!
  0 lf-mshift@ lf-term-read drop nip nip
  1 lf-mshift@ 3 lf-mshift@ lf-tag-app <> if 1+ then recurse
  dup if lf-mshift-leave exit then drop
  2 lf-mshift@ swap 3 lf-mshift@ lf-term-binary lf-mshift-allocated
  lf-mshift-leave ;

\ Shift a live mixed root. Validation and traversal share fuel; invalid input
\ and resource exhaustion are distinct. On failure discard appended nodes,
\ but never rewind allocation serials. Failed audit leaves fuel at zero.
\ Leaf constants and symbolic sorts are reused with their original stamps.
\ A zero shift returns the audited root without allocating or traversing it.
: lf-mixed-shift ( index identity cutoff amount fuel -- index identity status )
  dup 0< if 2drop 2drop drop -1 0 lf-mshift-invalid exit then
  lf-mshift-fuel !
  2dup 0< swap 0< or if 2drop 2drop -1 0 lf-mshift-invalid exit then
  lf-mshift-amount ! lf-mshift-cutoff !
  2dup lf-mshift-fuel @ lf-cterm-check
  dup if
    0 lf-mshift-fuel ! >r 2drop
    r> lf-repr-exhausted = if -1 0 lf-mshift-exhausted
    else -1 0 lf-mshift-invalid then exit
  then drop
  lf-cterm-fuel @ lf-mshift-fuel !
  lf-mshift-amount @ 0= if lf-mshift-ok exit then
  drop
  lf-term-count @ lf-mshift-start ! 0 lf-mshift-depth !
  lf-mshift-cutoff @ lf-mshift-walk
  dup if lf-mshift-start @ lf-term-count ! nip -1 0 rot exit then
  drop dup lf-term-identity 0= if
    drop lf-mshift-start @ lf-term-count ! -1 0 lf-mshift-invalid exit
  then lf-mshift-ok ;

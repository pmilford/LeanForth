\ Untrusted mixed-term weak-head beta reduction. Load mixed-instantiate.fs
\ and its dependencies first. Global arenas and scratch are non-reentrant;
\ exclude concurrent mutation, resets, raw edits and nested calls. Handles
\ are session-local diagnostics, not capabilities or serialized values.
lf-minst-ok constant lf-mbeta-ok
lf-minst-invalid constant lf-mbeta-invalid
lf-minst-exhausted constant lf-mbeta-exhausted
4 constant lf-mbeta-frame-cells
create lf-mbeta-frames lf-term-capacity lf-mbeta-frame-cells * cells allot
variable lf-mbeta-level
variable lf-mbeta-fuel
variable lf-mbeta-start

: lf-mbeta-frame ( level -- addr ) lf-mbeta-frame-cells * cells lf-mbeta-frames + ;
: lf-mbeta@ ( field -- value ) cells lf-mbeta-level @ 1- lf-mbeta-frame + @ ;
: lf-mbeta! ( value field -- ) cells lf-mbeta-level @ 1- lf-mbeta-frame + ! ;
: lf-mbeta-leave ( node status -- node status ) -1 lf-mbeta-level +! ;

\ Visit the function spine only. Generated nodes are live arena roots and
\ are passed with their current identities to the public instantiator. Each
\ visit costs fuel; instantiation's audits, traversal and shifts share it.
: lf-mbeta-walk ( node -- node status )
  lf-mbeta-fuel @ 0= lf-mbeta-level @ lf-term-capacity >= or if
    drop -1 lf-mbeta-exhausted exit
  then
  -1 lf-mbeta-fuel +!
  lf-mbeta-level @ lf-mbeta-frame ! 1 lf-mbeta-level +!
  0 lf-mbeta@ lf-term-read 0= if -1 lf-mbeta-invalid lf-mbeta-leave exit then
  3 lf-mbeta! 2 lf-mbeta! 1 lf-mbeta!
  1 lf-mbeta@ lf-tag-app <> if 0 lf-mbeta@ lf-mbeta-ok lf-mbeta-leave exit then
  2 lf-mbeta@ recurse
  dup if lf-mbeta-leave exit then drop
  dup lf-term-read 0= if drop -1 lf-mbeta-invalid lf-mbeta-leave exit then
  \ Stack: reduced-head tag domain body. Discard the domain, retain body.
  swap drop swap lf-tag-lam = if
    \ Reduced head is a lambda; instantiate its body with the argument.
    swap drop dup lf-term-identity 0= if
      drop -1 lf-mbeta-invalid lf-mbeta-leave exit
    then
    3 lf-mbeta@ dup lf-term-identity 0= if
      drop 2drop -1 lf-mbeta-invalid lf-mbeta-leave exit
    then
    \ Stack: body body-id argument argument-id.
    lf-mbeta-fuel @ lf-mixed-instantiate
    lf-minst-fuel @ lf-mbeta-fuel !
    dup if nip lf-mbeta-leave exit then
    drop drop recurse lf-mbeta-leave exit
  then
  drop
  dup 2 lf-mbeta@ = if drop 0 lf-mbeta@ lf-mbeta-ok lf-mbeta-leave exit then
  3 lf-mbeta@ lf-term-app lf-mshift-allocated lf-mbeta-leave ;

\ ( index identity fuel -- index identity status )
\ Audit the complete mixed graph before allocating, even discarded arguments
\ and lambda annotations. Fuel covers audit (including level visits), spine
\ visits and all instantiation work; repeated DAG visits are charged again.
\ Bounded reference/context scans are unmetered as in lf-cterm-check. On
\ failure restore the initial term count, never allocation serials; failed
\ preflight conservatively leaves zero fuel. Success returns a live stamped
\ root; unchanged constants and Sorts retain their identities. Exhaustion
\ includes fuel, frame, arena and index limits. Does not check scope, types,
\ declarations, equality, proofs, or executable-program correctness.
: lf-mixed-beta ( index identity fuel -- index identity status )
  dup 0< if drop 2drop 0 lf-mbeta-fuel ! -1 0 lf-mbeta-invalid exit then
  lf-mbeta-fuel !
  2dup lf-mbeta-fuel @ lf-cterm-check
  dup if 0 lf-mbeta-fuel ! >r 2drop
    r> lf-repr-exhausted = if -1 0 lf-mbeta-exhausted
    else -1 0 lf-mbeta-invalid then exit then drop
  drop lf-cterm-fuel @ lf-mbeta-fuel !
  lf-term-count @ lf-mbeta-start ! 0 lf-mbeta-level !
  lf-mbeta-walk
  dup if lf-mbeta-start @ lf-term-count ! nip -1 0 rot exit then
  drop dup lf-term-identity 0= if
    drop lf-mbeta-start @ lf-term-count ! -1 0 lf-mbeta-invalid exit
  then lf-mbeta-ok ;

\ Untrusted symbolic weak-head beta reduction. Load tagged-instantiate.fs and
\ its dependencies first. Global arenas and scratch frames are non-reentrant;
\ concurrent mutation is forbidden. This establishes no typing or theorem.
lf-tinst-ok constant lf-tbeta-ok
lf-tinst-invalid constant lf-tbeta-invalid
lf-tinst-exhausted constant lf-tbeta-exhausted
4 constant lf-tbeta-frame-cells
create lf-tbeta-frames lf-term-capacity lf-tbeta-frame-cells * cells allot
variable lf-tbeta-level
variable lf-tbeta-fuel
variable lf-tbeta-start

: lf-tbeta-frame ( level -- addr ) lf-tbeta-frame-cells * cells lf-tbeta-frames + ;
: lf-tbeta@ ( offset -- value ) cells lf-tbeta-level @ 1- lf-tbeta-frame + @ ;
: lf-tbeta! ( value offset -- ) cells lf-tbeta-level @ 1- lf-tbeta-frame + ! ;
: lf-tbeta-leave ( node status -- node status ) -1 lf-tbeta-level +! ;

\ Reduce only the function spine. Each visit spends one unit; substitution's
\ public validation and traversal consume the same remaining budget. An app
\ with a changed non-lambda head is rebuilt, leaving arguments unreduced.
: lf-tbeta-walk ( node -- node status )
  lf-tbeta-fuel @ 0= lf-tbeta-level @ lf-term-capacity >= or if
    drop -1 lf-tbeta-exhausted exit
  then
  -1 lf-tbeta-fuel +!
  lf-tbeta-level @ lf-tbeta-frame ! 1 lf-tbeta-level +!
  0 lf-tbeta@ lf-term-read 0= if -1 lf-tbeta-invalid lf-tbeta-leave exit then
  3 lf-tbeta! 2 lf-tbeta! 1 lf-tbeta!
  1 lf-tbeta@ lf-tag-app <> if 0 lf-tbeta@ lf-tbeta-ok lf-tbeta-leave exit then
  2 lf-tbeta@ recurse
  dup if lf-tbeta-leave exit then drop
  dup lf-term-read 0= if drop -1 lf-tbeta-invalid lf-tbeta-leave exit then
  swap drop swap lf-tag-lam = if
    \ Stack: reduced-head body. Its domain is irrelevant to contraction.
    swap drop dup lf-term-identity 0= if
      drop -1 lf-tbeta-invalid lf-tbeta-leave exit
    then
    3 lf-tbeta@ dup lf-term-identity 0= if
      drop 2drop -1 lf-tbeta-invalid lf-tbeta-leave exit
    then
    lf-tbeta-fuel @ lf-tagged-instantiate
    lf-tinst-fuel @ lf-tbeta-fuel !
    dup if nip lf-tbeta-leave exit then
    drop drop recurse lf-tbeta-leave exit
  then
  drop
  dup 2 lf-tbeta@ = if drop 0 lf-tbeta@ lf-tbeta-ok lf-tbeta-leave exit then
  3 lf-tbeta@ lf-term-app lf-tshift-allocated lf-tbeta-leave ;

\ ( index identity fuel -- index identity status )
\ Audit the entire input before reduction, including arguments that beta may
\ discard. On failure restore the term count, never allocation serials.
\ Failed preflight conservatively reports zero fuel remaining. Sorts are reused
\ by substitution, preserving their level and allocation identity stamps.
: lf-tagged-beta ( index identity fuel -- index identity status )
  dup 0< if drop 2drop -1 0 lf-tbeta-invalid exit then
  lf-tbeta-fuel !
  2dup lf-tbeta-fuel @ lf-hterm-check
  dup if 0 lf-tbeta-fuel ! >r 2drop -1 0 r> exit then drop
  drop lf-href-fuel @ lf-tbeta-fuel !
  lf-term-count @ lf-tbeta-start ! 0 lf-tbeta-level !
  lf-tbeta-walk
  dup if lf-tbeta-start @ lf-term-count ! nip -1 0 rot exit then
  drop dup lf-term-identity 0= if
    drop lf-tbeta-start @ lf-term-count ! -1 0 lf-tbeta-invalid exit
  then lf-tbeta-ok ;

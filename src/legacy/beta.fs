\ Untrusted weak-head beta reduction experiment for the term prototype.
\ It manipulates syntax without checking types, proofs or Lean declarations.
\ The mutable arena, global scratch state and host recursion are not suitable
\ for a trusted kernel; callers must prevent concurrent mutation.
include instantiate.fs

lf-shift-ok constant lf-beta-ok
lf-shift-invalid constant lf-beta-invalid
lf-shift-exhausted constant lf-beta-exhausted
4 constant lf-beta-frame-cells
create lf-beta-frames lf-term-capacity lf-beta-frame-cells * cells allot
variable lf-beta-level
variable lf-beta-fuel
variable lf-beta-start

\ Locate a frame; callers must provide an index inside the frame array.
: lf-beta-frame ( level -- addr ) lf-beta-frame-cells * cells lf-beta-frames + ;

\ Return the active frame; one must already have been pushed.
: lf-beta-current ( -- addr ) lf-beta-level @ 1- lf-beta-frame ;

\ Read or write a numbered cell in the active frame.
: lf-beta@ ( offset -- value ) cells lf-beta-current + @ ;
: lf-beta! ( value offset -- ) cells lf-beta-current + ! ;

\ Pop the active frame while retaining the result and status.
: lf-beta-leave ( result status -- result status ) -1 lf-beta-level +! ;

\ Reduce only the head of an expression. If the head of an application
\ becomes a lambda, instantiate its body with the argument and continue.
\ Subterms under binders and arguments are not normalized by this word.
: lf-beta-walk ( node -- result status )
  lf-beta-fuel @ 0= lf-beta-level @ lf-term-capacity >= or if
    drop -1 lf-beta-exhausted exit
  then
  -1 lf-beta-fuel +!
  lf-beta-level @ lf-beta-frame ! 1 lf-beta-level +!
  0 lf-beta@ lf-term-read 0= if
    -1 lf-beta-invalid lf-beta-leave exit
  then
  2 lf-beta! 1 lf-beta!
  lf-tag-app <> if 0 lf-beta@ lf-beta-ok lf-beta-leave exit then
  1 lf-beta@ recurse
  dup if lf-beta-leave exit then drop 3 lf-beta!
  3 lf-beta@ lf-term-read 0= if
    -1 lf-beta-invalid lf-beta-leave exit
  then
  rot lf-tag-lam = if
    nip 2 lf-beta@ lf-beta-fuel @ lf-instantiate
    lf-inst-fuel @ lf-beta-fuel !
    dup if lf-beta-leave exit then drop
    recurse lf-beta-leave exit
  then
  2drop
  3 lf-beta@ 1 lf-beta@ = if
    0 lf-beta@ lf-beta-ok lf-beta-leave exit
  then
  3 lf-beta@ 2 lf-beta@ lf-term-app lf-shift-allocated lf-beta-leave ;

\ Reduce one root with a nonnegative shared visit budget. First validate its
\ shape using a zero shift and discard that temporary output. If any operation
\ fails, restore the arena allocation count. Success does not prove equality
\ or well-typedness; it is merely the result of this experimental reduction.
: lf-beta-whnf ( node fuel -- result status )
  dup 0< if 2drop -1 lf-beta-invalid exit then lf-beta-fuel !
  lf-term-count-valid? 0= if drop -1 lf-beta-invalid exit then
  dup lf-term-valid? 0= if drop -1 lf-beta-invalid exit then
  lf-term-count @ lf-beta-start !
  dup 0 0 lf-beta-fuel @ lf-shift
  lf-shift-fuel @ lf-beta-fuel !
  dup if nip nip -1 swap exit then 2drop
  lf-beta-start @ lf-term-count ! 0 lf-beta-level !
  lf-beta-walk
  dup if lf-beta-start @ lf-term-count ! then ;

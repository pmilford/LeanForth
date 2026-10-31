\ Untrusted concrete evaluator for the experimental symbolic level arena.
\ A numeric result is not level equality, a checked type, or a theorem. A
\ parameter yields unknown; no value is guessed for it. Global state, host
\ cells and bounded host recursion are assumptions, not a trusted boundary.
\ The caller must include levels.fs and level-scope.fs before this file.

0 constant lf-lvalue-ok
1 constant lf-lvalue-invalid
2 constant lf-lvalue-exhausted
3 constant lf-lvalue-unknown
-1 1 rshift constant lf-lvalue-cell-max
4 constant lf-lvalue-frame-cells
create lf-lvalue-frames lf-level-capacity lf-lvalue-frame-cells * cells allot
variable lf-lvalue-depth
variable lf-lvalue-fuel

\ Address the active recursion frame; callers must hold an active frame.
: lf-lvalue-frame ( -- addr )
  lf-lvalue-depth @ 1- lf-lvalue-frame-cells * cells lf-lvalue-frames + ;
\ Read or write a numbered field of the active frame.
: lf-lvalue@ ( offset -- value ) cells lf-lvalue-frame + @ ;
: lf-lvalue! ( value offset -- ) cells lf-lvalue-frame + ! ;
\ Leave a frame without changing the result or status.
: lf-lvalue-leave ( result status -- result status ) -1 lf-lvalue-depth +! ;

\ Translate structural statuses explicitly; unexpected values fail closed.
: lf-lvalue-scope-status ( status -- status )
  case
    lf-lscope-ok of lf-lvalue-ok endof
    lf-lscope-invalid of lf-lvalue-invalid endof
    lf-lscope-exhausted of lf-lvalue-exhausted endof
    drop lf-lvalue-invalid 0
  endcase ;

\ Evaluate a previously validated node. The internal value -1 represents a
\ symbolic result; it cannot be confused with a concrete nonnegative level.
: lf-lvalue-walk ( node -- value status )
  lf-lvalue-fuel @ 0= lf-lvalue-depth @ lf-level-capacity >= or if
    drop -1 lf-lvalue-exhausted exit
  then
  -1 lf-lvalue-fuel +! 1 lf-lvalue-depth +!
  lf-level-read 0= if -1 lf-lvalue-invalid lf-lvalue-leave exit then
  2 lf-lvalue! 1 lf-lvalue! 0 lf-lvalue!
  0 lf-lvalue@ lf-level-tag-zero = if 0 lf-lvalue-ok lf-lvalue-leave exit then
  0 lf-lvalue@ lf-level-tag-param = if -1 lf-lvalue-ok lf-lvalue-leave exit then
  1 lf-lvalue@ recurse dup if lf-lvalue-leave exit then drop
  dup -1 = if lf-lvalue-ok lf-lvalue-leave exit then
  0 lf-lvalue@ lf-level-tag-succ = if
    dup lf-lvalue-cell-max = if drop -1 lf-lvalue-exhausted else 1+ lf-lvalue-ok then
    lf-lvalue-leave exit
  then
  3 lf-lvalue!
  2 lf-lvalue@ recurse dup if lf-lvalue-leave exit then drop
  dup -1 = if lf-lvalue-ok lf-lvalue-leave exit then
  0 lf-lvalue@ lf-level-tag-imax = over 0= and if
    drop 0
  else
    3 lf-lvalue@ max
  then
  lf-lvalue-ok lf-lvalue-leave ;

\ Validate the complete reachable graph and context first. Validation and
\ evaluation share fuel, but context validation has its own fixed bound.
\ Unknown, invalid or exhausted returns -1 and never authorizes a theorem.
: lf-level-value ( root fuel -- value status )
  dup 0< if 2drop -1 lf-lvalue-invalid exit then
  over swap lf-lscope-check lf-lvalue-scope-status
  ?dup if nip -1 swap exit then
  lf-lscope-fuel @ lf-lvalue-fuel !
  0 lf-lvalue-depth ! lf-lvalue-walk
  dup 0= if over -1 = if drop lf-lvalue-unknown then then ;

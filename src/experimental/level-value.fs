\ Untrusted concrete evaluator for the experimental symbolic level arena.
\ A numeric result is not level equality, a checked type, or a theorem. A
\ parameter yields unknown unless explicitly assigned in the separate instance
\ evaluator; checking one instance does not prove a polymorphic claim. Global state, host
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
variable lf-lvalue-use-assignments
create lf-lassign-ids lf-level-capacity cells allot
create lf-lassign-values lf-level-capacity cells allot
variable lf-lassign-count
variable lf-lassign-level-generation
variable lf-lassign-context-generation

\ Clear the finite map of explicit parameter-to-nonnegative-cell assignments.
: lf-lassign-reset ( -- )
  0 lf-lassign-count !
  lf-level-generation @ lf-lassign-level-generation !
  lf-lscope-generation @ lf-lassign-context-generation ! ;

\ Validate the assignment count before using it as an array bound.
: lf-lassign-count-valid? ( -- flag )
  lf-lassign-count @ dup 0< 0= swap lf-level-capacity <= and ;

\ Search a validated assignment table; missing identifiers return only false.
: lf-lassign-find ( id -- value true | false )
  lf-lassign-count @ 0 ?do
    dup i cells lf-lassign-ids + @ = if
      drop i cells lf-lassign-values + @ true unloop exit
    then
  loop drop false ;

\ Revalidate the finite map against the current context before evaluation.
\ Its bounded quadratic work is separate from the level-visit fuel.
: lf-lassign-valid? ( -- flag )
  lf-lassign-count-valid? lf-lscope-context-valid? and 0= if false exit then
  lf-level-count-valid? 0= if false exit then
  lf-level-generation @ lf-lassign-level-generation @ <>
  lf-lscope-generation @ lf-lassign-context-generation @ <> or if false exit then
  lf-lassign-count @ 0 ?do
    i cells lf-lassign-values + @ 0< if false unloop exit then
    i cells lf-lassign-ids + @ dup 0<= if drop false unloop exit then
    lf-lscope-member? 0= if false unloop exit then
    i 0 ?do
      i cells lf-lassign-ids + @ j cells lf-lassign-ids + @ = if
        false unloop unloop exit
      then
    loop
  loop true ;

\ Add one explicit assignment to a valid current map and context. Reject
\ duplicates, negative values, stale snapshots and exhaustion without mutation.
: lf-lassign-add ( id value -- flag )
  lf-lassign-valid? 0= if 2drop false exit then
  dup 0< if 2drop false exit then
  over lf-lscope-member? 0= if 2drop false exit then
  lf-lassign-count @ lf-level-capacity >= if 2drop false exit then
  over lf-lassign-find if drop 2drop false exit then
  lf-lassign-count @ cells lf-lassign-values + !
  lf-lassign-count @ cells lf-lassign-ids + !
  1 lf-lassign-count +! true ;

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
  0 lf-lvalue@ lf-level-tag-param = if
    lf-lvalue-use-assignments @ if
      1 lf-lvalue@ lf-lassign-find 0= if -1 then
    else -1 then
    lf-lvalue-ok lf-lvalue-leave exit
  then
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
: lf-level-value-run ( root fuel use-assignments -- value status )
  dup if lf-lassign-valid? 0= if drop 2drop -1 lf-lvalue-invalid exit then then
  lf-lvalue-use-assignments !
  dup 0< if 2drop -1 lf-lvalue-invalid exit then
  over swap lf-lscope-check lf-lvalue-scope-status
  ?dup if nip -1 swap exit then
  lf-lscope-fuel @ lf-lvalue-fuel !
  0 lf-lvalue-depth ! lf-lvalue-walk
  dup 0= if over -1 = if drop lf-lvalue-unknown then then ;

\ Evaluate without assignments; symbolic parameters remain unknown.
: lf-level-value ( root fuel -- value status )
  false lf-level-value-run ;

\ Evaluate one explicit assignment instance. Missing assignments stay unknown;
\ an invalid assignment table or context never produces a concrete value.
: lf-level-value-assigned ( root fuel -- value status )
  true lf-level-value-run ;

lf-lassign-reset

\ Untrusted structural scope experiment for the bounded term prototype.
\ It checks only node shape, backward references and de Bruijn binding depth.
\ Success does not mean a term is well typed, a proof is valid, or a Lean
\ declaration can be accepted. This module is not part of a trusted kernel.
\ Storage and traversal scratch space are global and not reentrant or thread-safe.
include ../core/terms.fs

0 constant lf-scope-ok
1 constant lf-scope-invalid
2 constant lf-scope-exhausted
create lf-scope-work lf-term-capacity 2 * cells allot
variable lf-scope-pending
variable lf-scope-fuel
variable lf-scope-node
variable lf-scope-depth
variable lf-scope-tag
variable lf-scope-first
variable lf-scope-second

\ Push an index and binder depth onto the bounded work stack; false means full.
: lf-scope-push ( index depth -- flag )
  lf-scope-pending @ lf-term-capacity >= if 2drop false exit then
  lf-scope-pending @ 2 * cells lf-scope-work + >r
  r@ cell+ ! r> ! 1 lf-scope-pending +! true ;

\ Pop an existing work item into traversal scratch variables.
: lf-scope-pop ( -- )
  -1 lf-scope-pending +!
  lf-scope-pending @ 2 * cells lf-scope-work +
  dup @ lf-scope-node ! cell+ @ lf-scope-depth ! ;

\ A binary child must precede its parent, which excludes cycles and forward
\ references even if prototype storage has been corrupted after construction.
: lf-scope-child? ( index -- flag )
  dup 0< 0= swap lf-scope-node @ < and ;

\ Inspect the current node and schedule its children. Lambda and Pi bind only
\ in their second field; an application binds in neither field.
: lf-scope-visit ( -- status )
  lf-scope-node @ lf-term-read 0= if lf-scope-invalid exit then
  lf-scope-second ! lf-scope-first ! lf-scope-tag !
  lf-scope-tag @ lf-tag-sort = if
    lf-scope-first @ 0< lf-scope-second @ 0<> or if
      lf-scope-invalid else lf-scope-ok then exit
  then
  lf-scope-tag @ lf-tag-bvar = if
    lf-scope-first @ 0< lf-scope-first @ lf-scope-depth @ >= or
    lf-scope-second @ 0<> or if
      lf-scope-invalid else lf-scope-ok then exit
  then
  lf-scope-tag @ lf-tag-app = lf-scope-tag @ lf-tag-lam = or
  lf-scope-tag @ lf-tag-pi = or 0= if lf-scope-invalid exit then
  lf-scope-first @ lf-scope-child? lf-scope-second @ lf-scope-child? and
  0= if lf-scope-invalid exit then
  lf-scope-first @ lf-scope-depth @ lf-scope-push 0= if
    lf-scope-exhausted exit
  then
  lf-scope-second @ lf-scope-depth @
  lf-scope-tag @ lf-tag-app <> if 1+ then
  lf-scope-push 0= if lf-scope-exhausted exit then
  lf-scope-ok ;

\ Inspect a closed root with a caller-supplied nonnegative node-visit budget.
\ Returns one of lf-scope-ok, lf-scope-invalid, or lf-scope-exhausted. No
\ status authorizes a theorem; exhausted is distinct from malformed input.
: lf-scope-check ( root fuel -- status )
  dup 0< if 2drop lf-scope-exhausted exit then lf-scope-fuel !
  lf-term-count @ dup 0< swap lf-term-capacity > or if
    drop lf-scope-invalid exit
  then
  0 lf-scope-pending !
  0 lf-scope-push 0= if lf-scope-exhausted exit then
  begin lf-scope-pending @ 0> while
    lf-scope-fuel @ 0= if lf-scope-exhausted exit then
    -1 lf-scope-fuel +!
    lf-scope-pop lf-scope-visit ?dup if exit then
  repeat
  lf-scope-ok ;

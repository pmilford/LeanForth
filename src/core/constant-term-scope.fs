\ Untrusted scope audit for mixed constant-bearing symbolic terms. Load
\ constant-term-boundary.fs and its dependencies first. This does not check
\ types, declarations, dependencies or proofs. Mutable storage is global,
\ single-threaded and non-reentrant; raw mutation and lifecycle changes
\ during a call are excluded. Handles are forgeable diagnostics.

create lf-cts-work lf-term-capacity 2 * cells allot
variable lf-cts-pending
variable lf-cts-fuel
variable lf-cts-node
variable lf-cts-depth
variable lf-cts-tag
variable lf-cts-first
variable lf-cts-second

\ Push one reachable node and the number of available term binders.
: lf-cts-push ( node depth -- flag )
  lf-cts-pending @ lf-term-capacity >= if 2drop false exit then
  lf-cts-pending @ 2 * cells lf-cts-work + >r
  r@ cell+ ! r> ! 1 lf-cts-pending +! true ;

\ Visit an already structurally audited node. Pi/lambda bind in their body
\ only; shared DAG nodes must be revisited at each distinct binding depth.
: lf-cts-visit ( -- status )
  lf-cts-node @ lf-term-read 0= if lf-repr-invalid exit then
  lf-cts-second ! lf-cts-first ! lf-cts-tag !
  lf-cts-tag @ lf-tag-bvar = if
    lf-cts-first @ lf-cts-depth @ < if lf-repr-ok else lf-repr-invalid then exit
  then
  lf-cts-tag @ lf-tag-symbolic-sort = lf-cts-tag @ lf-tag-constant = or if
    lf-repr-ok exit
  then
  lf-cts-tag @ lf-tag-app = lf-cts-tag @ lf-tag-lam = or
  lf-cts-tag @ lf-tag-pi = or 0= if lf-repr-invalid exit then
  lf-cts-first @ lf-cts-depth @ lf-cts-push 0= if lf-repr-exhausted exit then
  lf-cts-depth @
  lf-cts-tag @ lf-tag-app <> if
    dup -1 1 rshift = if drop lf-repr-exhausted exit then 1+
  then
  lf-cts-second @ swap lf-cts-push 0= if lf-repr-exhausted exit then
  lf-repr-ok ;

\ ( index identity outer-depth fuel -- status ) Validate the complete graph
\ with lf-cterm-check, then scope-check it with the remaining shared fuel.
\ The supplied outer depth is bounded by term capacity; traversal may enter
\ further binders. Unknown names and declaration types are
\ not examined. No allocation or theorem acceptance occurs on any outcome.
: lf-constant-term-scope ( index identity depth fuel -- status )
  dup 0< if 2drop 2drop lf-repr-invalid exit then lf-cts-fuel !
  dup 0< over lf-term-capacity > or if drop 2drop lf-repr-invalid exit then >r
  2dup lf-cts-fuel @ lf-cterm-check ?dup if
    >r 2drop r> r> drop exit
  then
  lf-cterm-fuel @ lf-cts-fuel ! drop r> 0 lf-cts-pending !
  lf-cts-push 0= if lf-repr-exhausted exit then
  begin lf-cts-pending @ 0> while
    lf-cts-fuel @ 0= if lf-repr-exhausted exit then
    -1 lf-cts-fuel +! -1 lf-cts-pending +!
    lf-cts-pending @ 2 * cells lf-cts-work +
    dup @ lf-cts-node ! cell+ @ lf-cts-depth !
    lf-cts-visit ?dup if exit then
  repeat lf-repr-ok ;

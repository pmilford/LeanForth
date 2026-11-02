\ Untrusted bounded shape and parameter-context validation for level DAGs.
\ It does not compare levels, establish Lean name identity, check types, or
\ authorize a theorem. All state is mutable, global and non-reentrant. The
\ caller must load levels.fs and prevent external mutation during each check.

0 constant lf-lscope-ok
1 constant lf-lscope-invalid
2 constant lf-lscope-exhausted
create lf-lscope-context lf-level-capacity cells allot
variable lf-lscope-context-count
variable lf-lscope-generation
create lf-lscope-work lf-level-capacity cells allot
variable lf-lscope-pending
variable lf-lscope-fuel
variable lf-lscope-node
variable lf-lscope-tag
variable lf-lscope-first
variable lf-lscope-second

\ Clear the context of opaque positive parameter identifiers.
: lf-lscope-advance ( -- )
  lf-lscope-generation @ dup 0< if drop exit then
  dup -1 1 rshift = if drop -1 else 1+ then lf-lscope-generation ! ;

\ Reset or successfully extend the context, invalidating prior snapshots.
: lf-lscope-context-reset ( -- ) 0 lf-lscope-context-count ! lf-lscope-advance ;

\ Test context count before using it as an array bound.
: lf-lscope-count-valid? ( -- flag )
  lf-lscope-context-count @ dup 0< 0= swap lf-level-capacity <= and
  lf-lscope-generation @ 0< 0= and ;

\ Search a valid context for an opaque identifier; caller must validate count.
: lf-lscope-member? ( id -- flag )
  lf-lscope-context-count @ 0 ?do
    dup i cells lf-lscope-context + @ = if drop true unloop exit then
  loop drop false ;

\ Validate all context slots, including uniqueness, before searching them.
\ The quadratic work is bounded by 64 entries and is separate from visit fuel.
: lf-lscope-context-valid? ( -- flag )
  lf-lscope-count-valid? 0= if false exit then
  lf-lscope-context-count @ 0 ?do
    i cells lf-lscope-context + @ 0<= if false unloop exit then
    i 0 ?do
      i cells lf-lscope-context + @ j cells lf-lscope-context + @ = if
        false unloop unloop exit
      then
    loop
  loop true ;

\ Add a positive, unique identifier to a valid context. Failure, including
\ corrupted existing entries and generation saturation, leaves it unchanged.
: lf-lscope-context-add ( id -- flag )
  lf-lscope-context-valid? 0= if drop false exit then
  lf-lscope-generation @ -1 1 rshift = if drop false exit then
  dup 0<= lf-lscope-context-count @ lf-level-capacity >= or if drop false exit then
  dup lf-lscope-member? if drop false exit then
  lf-lscope-context-count @ cells lf-lscope-context + !
  1 lf-lscope-context-count +! lf-lscope-advance
  lf-lscope-count-valid? ;

\ Push one work item, failing if the bounded work stack is full.
: lf-lscope-push ( index -- flag )
  lf-lscope-pending @ lf-level-capacity >= if drop false exit then
  lf-lscope-pending @ cells lf-lscope-work + !
  1 lf-lscope-pending +! true ;

\ A child must be nonnegative and strictly earlier than the current node.
: lf-lscope-child? ( index -- flag )
  dup 0< 0= swap lf-lscope-node @ < and ;

\ Inspect one node and enqueue its children; raw corruption fails closed.
: lf-lscope-visit ( -- status )
  lf-lscope-node @ lf-level-read 0= if lf-lscope-invalid exit then
  lf-lscope-second ! lf-lscope-first ! lf-lscope-tag !
  lf-lscope-tag @ lf-level-tag-zero = if
    lf-lscope-node @ lf-lscope-first @ or lf-lscope-second @ or
    if lf-lscope-invalid else lf-lscope-ok then exit
  then
  lf-lscope-tag @ lf-level-tag-param = if
    lf-lscope-first @ 0<= lf-lscope-second @ 0<> or if
      lf-lscope-invalid exit
    then
    lf-lscope-first @ lf-lscope-member? if lf-lscope-ok else lf-lscope-invalid then exit
  then
  lf-lscope-tag @ lf-level-tag-succ = if
    lf-lscope-first @ lf-lscope-child? 0= lf-lscope-second @ 0<> or if
      lf-lscope-invalid exit
    then
    lf-lscope-first @ lf-lscope-push if lf-lscope-ok else lf-lscope-exhausted then exit
  then
  lf-lscope-tag @ lf-level-tag-max = lf-lscope-tag @ lf-level-tag-imax = or 0= if
    lf-lscope-invalid exit
  then
  lf-lscope-first @ lf-lscope-child? lf-lscope-second @ lf-lscope-child? and 0= if
    lf-lscope-invalid exit
  then
  lf-lscope-first @ lf-lscope-push 0= if lf-lscope-exhausted exit then
  lf-lscope-second @ lf-lscope-push if lf-lscope-ok else lf-lscope-exhausted then ;

\ Validate a root against the current context with a visit budget. Each DAG
\ occurrence consumes fuel; shared nodes are deliberately visited repeatedly.
\ Even success is only structural evidence, not a level equality judgment.
: lf-lscope-check ( root fuel -- status )
  dup 0< if 2drop lf-lscope-invalid exit then lf-lscope-fuel !
  lf-lscope-context-valid? 0= if drop lf-lscope-invalid exit then
  dup lf-level-valid? 0= if drop lf-lscope-invalid exit then
  \ Check the distinguished zero slot even when the root does not reference it.
  0 lf-level-read 0= if drop lf-lscope-invalid exit then
  or or if drop lf-lscope-invalid exit then
  0 lf-lscope-pending !
  lf-lscope-push 0= if lf-lscope-exhausted exit then
  begin lf-lscope-pending @ 0> while
    lf-lscope-fuel @ 0= if lf-lscope-exhausted exit then
    -1 lf-lscope-fuel +!
    -1 lf-lscope-pending +!
    lf-lscope-pending @ cells lf-lscope-work + @ lf-lscope-node !
    lf-lscope-visit ?dup if exit then
  repeat lf-lscope-ok ;

0 lf-lscope-generation !
lf-lscope-context-reset

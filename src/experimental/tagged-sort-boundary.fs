\ Experimental representation validation, NOT a kernel or a type checker.
\ The caller loads core/terms.fs first. Concrete Sort payloads are numbers;
\ symbolic Sort payloads are level-arena indices. A distinct tag makes the
\ representations distinguishable, but neither level validity nor lifetime,
\ context, scope, typing or proof validity is established by this module.
\ All state is mutable, global, single-threaded and not reentrant. Callers
\ must prevent concurrent mutation and treat all returned statuses as untrusted.

6 constant lf-tag-symbolic-sort
0 constant lf-repr-concrete
1 constant lf-repr-symbolic
0 constant lf-repr-ok
1 constant lf-repr-invalid
2 constant lf-repr-exhausted
create lf-repr-work lf-term-capacity cells allot
variable lf-repr-pending
variable lf-repr-mode
variable lf-repr-fuel
variable lf-repr-node
variable lf-repr-tag
variable lf-repr-first
variable lf-repr-second

\ Store only syntax. A nonnegative payload is not proof that a level exists,
\ is in scope, belongs to a live arena generation, or has Lean semantics.
: lf-term-symbolic-sort ( level-index -- index true | false )
  dup 0< if drop false exit then
  lf-tag-symbolic-sort swap 0 lf-term-add ;

\ Push an index onto the bounded worklist. The caller validates its relation
\ to the current parent; false means the worklist is full.
: lf-repr-push ( index -- flag )
  lf-repr-pending @ lf-term-capacity >= if drop false exit then
  lf-repr-pending @ cells lf-repr-work + !
  1 lf-repr-pending +! true ;

\ A child must be a strictly earlier node, ruling out cycles and forward edges.
: lf-repr-child? ( index -- flag )
  dup 0< 0= swap lf-repr-node @ < and ;

\ Inspect the current node and schedule both binary children. Variables are
\ syntax only: their binding depth is deliberately not checked here.
: lf-repr-visit ( -- status )
  lf-repr-node @ lf-term-read 0= if lf-repr-invalid exit then
  lf-repr-second ! lf-repr-first ! lf-repr-tag !
  lf-repr-tag @ lf-tag-sort = lf-repr-tag @ lf-tag-symbolic-sort = or if
    lf-repr-first @ 0< lf-repr-second @ 0<> or if lf-repr-invalid exit then
    lf-repr-tag @ lf-tag-sort = lf-repr-mode @ lf-repr-concrete = =
    if lf-repr-ok else lf-repr-invalid then exit
  then
  lf-repr-tag @ lf-tag-bvar = if
    lf-repr-first @ 0< lf-repr-second @ 0<> or
    if lf-repr-invalid else lf-repr-ok then exit
  then
  lf-repr-tag @ lf-tag-app = lf-repr-tag @ lf-tag-lam = or
  lf-repr-tag @ lf-tag-pi = or 0= if lf-repr-invalid exit then
  lf-repr-first @ lf-repr-child? lf-repr-second @ lf-repr-child? and
  0= if lf-repr-invalid exit then
  lf-repr-first @ lf-repr-push 0= if lf-repr-exhausted exit then
  lf-repr-second @ lf-repr-push 0= if lf-repr-exhausted exit then
  lf-repr-ok ;

\ Walk one validated root using the current mode and shared remaining fuel.
\ Each node visit costs one unit; shared DAG children may be visited repeatedly.
: lf-repr-walk ( root -- status )
  0 lf-repr-pending !
  lf-repr-push 0= if lf-repr-exhausted exit then
  begin lf-repr-pending @ 0> while
    lf-repr-fuel @ 0= if lf-repr-exhausted exit then
    -1 lf-repr-fuel +! -1 lf-repr-pending +!
    lf-repr-pending @ cells lf-repr-work + @ lf-repr-node !
    lf-repr-visit ?dup if exit then
  repeat lf-repr-ok ;

\ Initialize an explicit mode and budget; false leaves no state arguments.
: lf-repr-start ( mode fuel -- flag )
  dup 0< if 2drop false exit then lf-repr-fuel !
  dup lf-repr-concrete = over lf-repr-symbolic = or 0= if
    drop false exit
  then lf-repr-mode ! true ;

\ Check one reachable syntax graph. Non-success never authorizes a theorem;
\ even success establishes only representation and structural node shape.
: lf-repr-check ( root mode fuel -- status )
  lf-repr-start 0= if drop lf-repr-invalid exit then
  dup lf-term-valid? 0= if drop lf-repr-invalid exit then
  lf-repr-walk ;

\ Check both roots using the same finite budget, including when the first root
\ is Sort-free. Counts and source nodes are never changed by either check.
: lf-repr-check-pair ( root1 root2 mode fuel -- status )
  lf-repr-start 0= if 2drop lf-repr-invalid exit then
  over lf-term-valid? over lf-term-valid? and 0= if
    2drop lf-repr-invalid exit
  then
  swap lf-repr-walk ?dup if nip exit then lf-repr-walk ;

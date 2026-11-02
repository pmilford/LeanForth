\ Bounded, untrusted open-term inference. Load tagged-infer.fs and its
\ dependencies first. A context is an array of (term-index, identity) pairs,
\ oldest binder first; each domain is written in the preceding context.
\ Results are CONDITIONAL on every domain being a well-formed type in that
\ preceding context. Scope and representation checks do not establish typing,
\ Lean compatibility, or theorem validity. Handles are forgeable generation
\ stamps, not capabilities. No raw arena writes, concurrent mutation, nested
\ calls, or session changes are allowed. Caller supplies readable aligned
\ storage of 2*count cells, disjoint from ALL mutable storage of lf-tci and
\ dependent modules, including variables, scratch arrays, contexts and arenas.
\ Forth cannot validate caller addresses or disjointness.

create lf-tci-domains lf-term-capacity 2 * cells allot
create lf-tci-work lf-term-capacity 2 * cells allot
variable lf-tci-count
variable lf-tci-root
variable lf-tci-root-id
variable lf-tci-address
variable lf-tci-fuel
variable lf-tci-pending
variable lf-tci-node
variable lf-tci-depth
variable lf-tci-tag
variable lf-tci-first
variable lf-tci-second
variable lf-tci-term-start
variable lf-tci-level-start

: lf-tci-domain ( n -- addr ) 2 * cells lf-tci-domains + ;

\ Scope traversal runs only on a previously audited graph. The depth is the
\ number of available outer binders plus binders entered during this walk.
: lf-tci-push ( node depth -- flag )
  lf-tci-pending @ lf-term-capacity >= if 2drop false exit then
  lf-tci-pending @ 2 * cells lf-tci-work + >r
  r@ cell+ ! r> ! 1 lf-tci-pending +! true ;

: lf-tci-scope ( node depth -- status )
  0 lf-tci-pending ! lf-tci-push 0= if lf-tinfer-exhausted exit then
  begin lf-tci-pending @ 0> while
    lf-tci-fuel @ 0= if lf-tinfer-exhausted exit then
    -1 lf-tci-fuel +! -1 lf-tci-pending +!
    lf-tci-pending @ 2 * cells lf-tci-work +
    dup @ lf-tci-node ! cell+ @ lf-tci-depth !
    lf-tci-node @ lf-term-read 0= if lf-tinfer-invalid exit then
    lf-tci-second ! lf-tci-first ! lf-tci-tag !
    lf-tci-tag @ lf-tag-bvar = if
      lf-tci-first @ lf-tci-depth @ >= if lf-tinfer-invalid exit then
    else
      lf-tci-tag @ lf-tag-symbolic-sort <> if
        lf-tci-first @ lf-tci-depth @ lf-tci-push 0= if
          lf-tinfer-exhausted exit then
        lf-tci-depth @
        lf-tci-tag @ lf-tag-app <> if
          dup -1 1 rshift = if drop lf-tinfer-exhausted exit then 1+
        then
        lf-tci-second @ swap lf-tci-push 0= if lf-tinfer-exhausted exit then
      then
    then
  repeat lf-tinfer-ok ;

\ Map representation-audit statuses explicitly; unexpected statuses fail closed.
: lf-tci-audit-status ( status -- status )
  case
    lf-repr-ok of lf-tinfer-ok endof
    lf-repr-invalid of lf-tinfer-invalid endof
    lf-repr-exhausted of lf-tinfer-exhausted endof
    drop lf-tinfer-invalid 0
  endcase ;

\ Audit identities, session, syntax, levels and scope with one shared fuel.
: lf-tci-audit ( index identity depth -- status )
  >r 2dup lf-tci-fuel @ lf-hterm-check lf-tci-audit-status
  ?dup if >r 2drop r> r> drop 0 lf-tci-fuel ! exit then
  lf-href-fuel @ lf-tci-fuel ! drop r> lf-tci-scope ;

\ ( root identity context-address count fuel -- type identity status )
\ count must be 0..capacity; zero permits any address. Every pair is copied
\ and audited, and the root audited, before any arena allocation. All visits,
\ including repeated DAG visits and inference helpers, share fuel. Failure
\ returns -1 0 and invalid/exhausted/unknown; both arena counts roll back,
\ allocation serials do not. Success retains temporary allocations. The logical
\ inference context depth is reset after a walk; scratch cells are not erased.
\ All scratch is global and non-reentrant.
: lf-tcontext-infer ( root identity address count fuel -- type identity status )
  dup 0< if 2drop 2drop drop -1 0 lf-tinfer-invalid exit then lf-tci-fuel !
  dup 0< over lf-term-capacity > or if
    2drop 2drop -1 0 lf-tinfer-invalid exit then
  lf-tci-count ! lf-tci-address ! lf-tci-root-id ! lf-tci-root !
  lf-tci-address @
  lf-tci-count @ 0 ?do
    dup i 2 * cells + dup @ i lf-tci-domain !
    cell+ @ i lf-tci-domain cell+ !
  loop drop
  lf-term-count @ lf-tci-term-start ! lf-level-count @ lf-tci-level-start !
  lf-tci-count @ 0 ?do
    i lf-tci-domain dup @ swap cell+ @ i lf-tci-audit
    ?dup if -1 0 rot unloop exit then
  loop
  lf-tci-root @ lf-tci-root-id @ lf-tci-count @ lf-tci-audit
  ?dup if -1 0 rot exit then
  lf-tci-term-start @ lf-tinfer-term-start !
  lf-tci-level-start @ lf-tinfer-level-start !
  lf-tci-fuel @ lf-tinfer-fuel ! 0 lf-tinfer-depth !
  0 lf-tinfer-context-depth !
  lf-tci-count @ 0 ?do i lf-tci-domain @ lf-tinfer-push drop loop
  lf-tci-root @ lf-tinfer-walk
  0 lf-tinfer-context-depth !
  dup if
    >r drop lf-tci-term-start @ lf-term-count !
    lf-tci-level-start @ lf-level-count ! -1 0 r> exit
  then drop
  dup lf-term-identity 0= if
    drop lf-tci-term-start @ lf-term-count !
    lf-tci-level-start @ lf-level-count ! -1 0 lf-tinfer-invalid exit
  then lf-tinfer-ok ;

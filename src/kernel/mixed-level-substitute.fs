\ Untrusted same-session simultaneous universe substitution for mixed syntax.
\ Load constant-term-boundary.fs and level-substitute.fs and dependencies.
\ The current session context must contain every source parameter and every
\ actual parameter. Every source parameter must also occur in the formal list;
\ actuals are not recursively substituted. This is not type or proof checking.
\ Global scratch and all arenas are single-threaded and non-reentrant. Exclude
\ reset, raw mutation and callbacks during a call. Caller arrays must be aligned,
\ readable and disjoint from arenas, contexts and scratch. Handles are forgeable.
\ On failure all three arena counts roll back, but identities never rewind.

0 constant lf-mlsubst-ok
1 constant lf-mlsubst-invalid
2 constant lf-mlsubst-exhausted
variable lf-mls-root
variable lf-mls-id
variable lf-mls-formals
variable lf-mls-handles
variable lf-mls-count
variable lf-mls-fuel
variable lf-mls-terms
variable lf-mls-levels
variable lf-mls-crefs
variable lf-mls-node
variable lf-mls-tag
variable lf-mls-a
variable lf-mls-b
variable lf-mls-ref
variable lf-mls-refid
variable lf-mls-nargs
variable lf-mls-changed
create lf-mls-actuals lf-level-capacity cells allot
create lf-mls-args lf-cref-argument-capacity 2 * cells allot
create lf-mls-seen lf-term-capacity cells allot
create lf-mls-results lf-term-capacity cells allot

: lf-mls-repr-status ( status -- status )
  case lf-repr-ok of lf-mlsubst-ok endof
    lf-repr-invalid of lf-mlsubst-invalid endof
    lf-repr-exhausted of lf-mlsubst-exhausted endof
    drop lf-mlsubst-invalid 0 endcase ;
: lf-mls-level-status ( status -- status )
  case lf-lsubst-ok of lf-mlsubst-ok endof
    lf-lsubst-invalid of lf-mlsubst-invalid endof
    lf-lsubst-exhausted of lf-mlsubst-exhausted endof
    drop lf-mlsubst-invalid 0 endcase ;
: lf-mls-rollback ( status -- status )
  lf-mls-terms @ lf-term-count ! lf-mls-levels @ lf-level-count !
  lf-mls-crefs @ lf-cref-count ! ;

\ Audit each source level against the formal list without allocating. The
\ preceding mixed audit has separately checked it in its actual session scope.
: lf-mls-source ( level -- status )
  lf-lsubst-root ! lf-mls-fuel @ lf-lsubst-fuel !
  lf-lsubst-source lf-lsubst-fuel @ lf-mls-fuel ! lf-mls-level-status ;
: lf-mls-source-ref ( -- status )
  lf-mls-a @ lf-mls-ref ! lf-mls-b @ lf-mls-refid !
  lf-mls-ref @ lf-mls-refid @ lf-cref-read 0= if lf-mlsubst-invalid exit then
  lf-mls-nargs ! 2drop
  lf-mls-nargs @ 0 ?do
    lf-mls-ref @ lf-mls-refid @ i lf-cref-level 0= if
      lf-mlsubst-invalid unloop exit then
    drop lf-mls-source ?dup if unloop exit then
  loop lf-mlsubst-ok ;

\ Mark reachable terms and audit every source level before any allocation.
\ Occurrences, including repeated DAG edges, each consume fuel.
: lf-mls-audit ( -- status )
  lf-mls-seen lf-term-capacity cells erase
  0 lf-href-pending ! lf-mls-root @ lf-href-push 0= if
    lf-mlsubst-exhausted exit then
  begin lf-href-pending @ 0> while
    lf-mls-fuel @ 0= if lf-mlsubst-exhausted exit then
    -1 lf-mls-fuel +! -1 lf-href-pending +!
    lf-href-pending @ cells lf-href-work + @ lf-mls-node !
    true lf-mls-node @ cells lf-mls-seen + !
    lf-mls-node @ lf-term-read 0= if lf-mlsubst-invalid exit then
    lf-mls-b ! lf-mls-a ! lf-mls-tag !
    lf-mls-tag @ lf-tag-symbolic-sort = if
      lf-mls-a @ lf-mls-source ?dup if exit then
    else lf-mls-tag @ lf-tag-constant = if
      lf-mls-source-ref ?dup if exit then
    else lf-mls-tag @ lf-tag-bvar <> if
      lf-mls-a @ lf-href-push 0= if lf-mlsubst-exhausted exit then
      lf-mls-b @ lf-href-push 0= if lf-mlsubst-exhausted exit then
    then then then
  repeat lf-mlsubst-ok ;

: lf-mls-level ( root -- result 0 | status )
  lf-mls-formals @ lf-mls-actuals lf-mls-count @ lf-mls-fuel @ lf-lsubst
  lf-lsubst-fuel @ lf-mls-fuel ! lf-mls-level-status ;

\ Build a new reference only when at least one argument changes.
: lf-mls-constant ( -- index 0 | status )
  lf-mls-a @ lf-mls-ref ! lf-mls-b @ lf-mls-refid !
  lf-mls-ref @ lf-mls-refid @ lf-cref-read 0= if lf-mlsubst-invalid exit then
  lf-mls-nargs ! 2drop 0 lf-mls-changed !
  lf-mls-nargs @ 0 ?do
    lf-mls-ref @ lf-mls-refid @ i lf-cref-level 0= if
      lf-mlsubst-invalid unloop exit then
    drop dup lf-mls-level ?dup if nip unloop exit then
    2dup <> if true lf-mls-changed ! then nip
    dup i 2 * cells lf-mls-args + !
    lf-level-identity 0= if drop lf-mlsubst-invalid unloop exit then
    i 2 * 1+ cells lf-mls-args + !
  loop
  lf-mls-changed @ 0= if lf-mls-node @ lf-mlsubst-ok exit then
  lf-mls-ref @ lf-cref-slot dup cell+ @ swap 2 cells + @
  lf-mls-args lf-mls-nargs @ lf-cref-new 0= if lf-mlsubst-exhausted exit then
  lf-cterm-new 0= if lf-mlsubst-exhausted exit then drop lf-mlsubst-ok ;

: lf-mls-build ( -- status )
  lf-mls-root @ 1+ 0 ?do
    i cells lf-mls-seen + @ if
      i lf-mls-node ! i lf-term-read 0= if lf-mlsubst-invalid unloop exit then
      lf-mls-b ! lf-mls-a ! lf-mls-tag !
      lf-mls-tag @ lf-tag-symbolic-sort = if
        lf-mls-a @ lf-mls-level ?dup if unloop exit then
        dup lf-mls-a @ = if drop i else
          dup lf-level-identity 0= if drop lf-mlsubst-invalid unloop exit then
          lf-hterm-sort 0= if lf-mlsubst-exhausted unloop exit then drop
        then
      else lf-mls-tag @ lf-tag-constant = if
        lf-mls-constant ?dup if unloop exit then
      else lf-mls-tag @ lf-tag-bvar = if i else
        lf-mls-a @ cells lf-mls-results + @
        lf-mls-b @ cells lf-mls-results + @
        2dup lf-mls-b @ = swap lf-mls-a @ = and if 2drop i else
          lf-mls-tag @ lf-term-binary 0= if lf-mlsubst-exhausted unloop exit then
        then
      then then then
      i cells lf-mls-results + !
    then
  loop lf-mlsubst-ok ;

\ ( index id formals actual-pairs count fuel -- index id 0 | status )
\ All syntax, source levels and replacements are audited before allocation.
\ Audit and substitution share fuel; each term/level occurrence consumes fuel,
\ including repeated replacement validation. Bounded list scans, identity
\ checks and topological staging are additional bounded work. Status is invalid
\ for malformed, stale or out-of-scope input, exhausted for resource limits.
: lf-mixed-level-substitute ( index id formals actual-pairs count fuel -- index id 0 | status )
  dup 0< if 2drop 2drop 2drop lf-mlsubst-invalid exit then lf-mls-fuel !
  dup 0< over lf-level-capacity > or if 2drop 2drop drop lf-mlsubst-invalid exit then
  lf-mls-count ! lf-mls-handles ! lf-mls-formals ! lf-mls-id ! lf-mls-root !
  lf-mls-root @ lf-mls-id @ lf-hterm-valid? 0= if lf-mlsubst-invalid exit then
  lf-cref-state-valid? 0= lf-term-serial @ 0< or lf-level-serial @ 0< or if
    lf-mlsubst-invalid exit then
  lf-term-count @ lf-mls-terms ! lf-level-count @ lf-mls-levels !
  lf-cref-count @ lf-mls-crefs !
  lf-mls-count @ 0 ?do
    i 2 * cells lf-mls-handles @ + dup @ swap cell+ @
    2dup lf-hlevel-valid? 0= if 2drop lf-mlsubst-invalid unloop exit then
    drop i cells lf-mls-actuals + !
  loop
  lf-mls-formals @ lf-lsubst-formals ! lf-mls-actuals lf-lsubst-actuals !
  lf-mls-count @ lf-lsubst-count ! lf-mls-fuel @ lf-lsubst-fuel !
  lf-lsubst-inputs lf-lsubst-fuel @ lf-mls-fuel ! lf-mls-level-status ?dup if exit then
  lf-mls-root @ lf-mls-id @ lf-mls-fuel @ lf-cterm-check
  lf-cterm-fuel @ lf-mls-fuel ! lf-mls-repr-status ?dup if exit then
  lf-mls-audit ?dup if exit then
  lf-mls-build ?dup if lf-mls-rollback exit then
  lf-mls-root @ cells lf-mls-results + @ dup lf-term-identity 0= if
    drop lf-mlsubst-invalid lf-mls-rollback exit then lf-mlsubst-ok ;

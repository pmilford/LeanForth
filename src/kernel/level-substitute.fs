\ Untrusted, single-threaded simultaneous substitution over the level arena.
\ Load levels.fs and level-scope.fs first. The caller must keep the arena,
\ arrays and caller context unchanged throughout a call. Input arrays must be
\ cell-aligned and disjoint from all arena, context and module scratch storage;
\ the routine does not detect aliasing. IDs are opaque cells,
\ not Lean names; raw indices cannot detect stale references after reset.
\ This neither checks declarations nor authorizes proofs. No simplification,
\ level equality, serialization, concurrency or cross-arena handles are provided.
\ The arrays each contain count cells; their accessible memory is a caller
\ responsibility. Empty lists permit arbitrary unused addresses. The existing
\ lf-lscope context describes the caller scope, not the formal scope.

0 constant lf-lsubst-ok
1 constant lf-lsubst-invalid
2 constant lf-lsubst-exhausted
variable lf-lsubst-root
variable lf-lsubst-formals
variable lf-lsubst-actuals
variable lf-lsubst-count
variable lf-lsubst-fuel
variable lf-lsubst-node
variable lf-lsubst-tag
variable lf-lsubst-first
variable lf-lsubst-second
variable lf-lsubst-newcount
create lf-lsubst-seen lf-level-capacity cells allot
create lf-lsubst-result lf-level-capacity cells allot
create lf-lsubst-tags lf-level-capacity cells allot
create lf-lsubst-left lf-level-capacity cells allot
create lf-lsubst-right lf-level-capacity cells allot

: lf-lsubst-formal@ ( position -- id ) cells lf-lsubst-formals @ + @ ;
: lf-lsubst-actual@ ( position -- root ) cells lf-lsubst-actuals @ + @ ;
\ Return position and true, or false, for a formal ID.
: lf-lsubst-find ( id -- position true | false )
  lf-lsubst-count @ 0 ?do
    dup i lf-lsubst-formal@ = if drop i true unloop exit then
  loop drop false ;

\ Validate each actual in caller scope, sharing one occurrence fuel budget.
: lf-lsubst-inputs ( -- status )
  lf-lscope-context-valid? 0= if lf-lsubst-invalid exit then
  lf-lsubst-count @ 0 ?do
    i lf-lsubst-formal@ 0<= if lf-lsubst-invalid unloop exit then
    i 0 ?do
      i lf-lsubst-formal@ j lf-lsubst-formal@ = if
        lf-lsubst-invalid unloop unloop exit
      then
    loop
    i lf-lsubst-actual@ lf-lsubst-fuel @ lf-lscope-check
    lf-lscope-fuel @ lf-lsubst-fuel !
    ?dup if unloop exit then
  loop lf-lsubst-ok ;

\ Source traversal checks only the reachable DAG; each occurrence costs fuel.
\ The lscope work stack is scratch and is bounded independently of fuel.
: lf-lsubst-source ( -- status )
  lf-lsubst-root @ lf-level-valid? 0= if lf-lsubst-invalid exit then
  0 lf-level-read 0= if lf-lsubst-invalid exit then
  or or if lf-lsubst-invalid exit then
  lf-lsubst-seen lf-level-capacity cells erase
  0 lf-lscope-pending !
  lf-lsubst-root @ lf-lscope-push 0= if lf-lsubst-exhausted exit then
  begin lf-lscope-pending @ 0> while
    lf-lsubst-fuel @ 0= if lf-lsubst-exhausted exit then
    -1 lf-lsubst-fuel +! -1 lf-lscope-pending +!
    lf-lscope-pending @ cells lf-lscope-work + @ lf-lsubst-node !
    lf-lsubst-node @ lf-level-read 0= if lf-lsubst-invalid exit then
    lf-lsubst-second ! lf-lsubst-first ! lf-lsubst-tag !
    true lf-lsubst-node @ cells lf-lsubst-seen + !
    lf-lsubst-tag @ lf-level-tag-zero = if
      lf-lsubst-node @ lf-lsubst-first @ or lf-lsubst-second @ or
      if lf-lsubst-invalid exit then
    else lf-lsubst-tag @ lf-level-tag-param = if
      lf-lsubst-first @ 0<= lf-lsubst-second @ 0<> or if lf-lsubst-invalid exit then
      lf-lsubst-first @ lf-lsubst-find 0= if lf-lsubst-invalid exit then drop
    else
      lf-lsubst-first @ dup 0< swap lf-lsubst-node @ >= or if lf-lsubst-invalid exit then
      lf-lsubst-tag @ lf-level-tag-succ = if
        lf-lsubst-second @ 0<> if lf-lsubst-invalid exit then
      else
        lf-lsubst-tag @ lf-level-tag-max = lf-lsubst-tag @ lf-level-tag-imax = or 0= if
          lf-lsubst-invalid exit
        then
        lf-lsubst-second @ dup 0< swap lf-lsubst-node @ >= or if lf-lsubst-invalid exit then
        lf-lsubst-second @ lf-lscope-push 0= if lf-lsubst-exhausted exit then
      then
      lf-lsubst-first @ lf-lscope-push 0= if lf-lsubst-exhausted exit then
    then then
  repeat lf-lsubst-ok ;

\ Plan nodes in original index order, using future indices without allocating.
\ Reuse unchanged nodes; repeated source DAG nodes remain shared.
: lf-lsubst-plan ( -- status )
  0 lf-lsubst-newcount !
  lf-lsubst-root @ 1+ 0 ?do
    i cells lf-lsubst-seen + @ if
      i lf-level-slot dup @ lf-lsubst-tag ! dup cell+ @ lf-lsubst-first !
      2 cells + @ lf-lsubst-second !
      lf-lsubst-tag @ lf-level-tag-param = if
        lf-lsubst-first @ lf-lsubst-find 0= if
          lf-lsubst-invalid unloop exit
        then lf-lsubst-actual@
        i cells lf-lsubst-result + !
      else lf-lsubst-tag @ lf-level-tag-zero = if
        0 i cells lf-lsubst-result + !
      else
        lf-lsubst-first @ cells lf-lsubst-result + @ lf-lsubst-first !
        lf-lsubst-tag @ lf-level-tag-succ <> if
          lf-lsubst-second @ cells lf-lsubst-result + @ lf-lsubst-second !
        then
        lf-lsubst-first @ i lf-level-slot cell+ @ =
        lf-lsubst-second @ i lf-level-slot 2 cells + @ = and if
          i i cells lf-lsubst-result + !
        else
          lf-level-count @ lf-lsubst-newcount @ + lf-level-capacity >= if
            lf-lsubst-exhausted unloop exit
          then
          lf-lsubst-tag @ lf-lsubst-newcount @ cells lf-lsubst-tags + !
          lf-lsubst-first @ lf-lsubst-newcount @ cells lf-lsubst-left + !
          lf-lsubst-second @ lf-lsubst-newcount @ cells lf-lsubst-right + !
          lf-level-count @ lf-lsubst-newcount @ + i cells lf-lsubst-result + !
          1 lf-lsubst-newcount +!
        then
      then then
    then
  loop
  -1 1 rshift lf-level-serial @ - lf-lsubst-newcount @ < if
    lf-lsubst-exhausted exit
  then lf-lsubst-ok ;

\ ( root formal-addr actual-addr count fuel -- result lf-lsubst-ok | status )
\ Invalid input or scope returns invalid; fuel, work stack, arena or identity
\ exhaustion returns exhausted. Failure appends no nodes and issues no result.
\ Fuel counts every occurrence in every actual and the source; validating the
\ bounded formal list and staging nodes are additional bounded work. Scratch
\ storage and lscope scratch variables are overwritten even on failure.
: lf-lsubst ( root formal-addr actual-addr count fuel -- result lf-lsubst-ok | status )
  dup 0< if 2drop 2drop drop lf-lsubst-invalid exit then lf-lsubst-fuel !
  dup 0< over lf-level-capacity > or if 2drop 2drop lf-lsubst-invalid exit then
  lf-lsubst-count ! lf-lsubst-actuals ! lf-lsubst-formals ! lf-lsubst-root !
  lf-level-count-valid? 0= lf-level-serial @ 0< or if lf-lsubst-invalid exit then
  lf-lsubst-inputs ?dup if exit then
  lf-lsubst-source ?dup if exit then
  lf-lsubst-plan ?dup if exit then
  \ All allocation preconditions were checked; no callbacks or mutation can
  \ intervene under the stated single-threaded ownership assumption.
  lf-lsubst-newcount @ 0 ?do
    i cells lf-lsubst-tags + @ i cells lf-lsubst-left + @
    i cells lf-lsubst-right + @ lf-level-add drop drop
  loop
  lf-lsubst-root @ cells lf-lsubst-result + @ lf-lsubst-ok ;

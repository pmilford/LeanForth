\ Untrusted, bounded symbolic term/level session. Load terms.fs, levels.fs,
\ level-scope.fs and tagged-sort-boundary.fs first. This is not a type checker
\ and cannot authorize a theorem. All state is global, mutable, single-threaded
\ and non-reentrant; raw arena writes and concurrent mutation are excluded.
\ A session captures arena/context generations, but bare term OR level indices
\ reused after a NEW session are indistinguishable from stale caller handles.

variable lf-ssession-active
variable lf-ssession-term-generation
variable lf-ssession-level-generation
variable lf-ssession-context-generation
variable lf-ssession-fuel
variable lf-ssession-pending
variable lf-ssession-tag
variable lf-ssession-first
variable lf-ssession-second
create lf-ssession-work lf-term-capacity cells allot
0 lf-ssession-active !

\ Bind an empty term arena to the currently valid level arena and parameter
\ context. Failure invalidates any previous session; no arena is modified.
: lf-ssession-begin ( -- flag )
  0 lf-ssession-active !
  lf-term-count-valid? lf-level-count-valid? and
  lf-lscope-context-valid? and 0= if false exit then
  lf-term-count @ 0<> if false exit then
  lf-term-generation @ lf-ssession-term-generation !
  lf-level-generation @ lf-ssession-level-generation !
  lf-lscope-generation @ lf-ssession-context-generation !
  true dup lf-ssession-active ! ;

\ Check all captured epochs and current counts; repeated begin after a reset
\ is only permitted while the term arena is empty.
: lf-ssession-current? ( -- flag )
  lf-ssession-active @ 0= if false exit then
  lf-term-count-valid? lf-level-count-valid? and
  lf-lscope-context-valid? and 0= if false exit then
  lf-term-generation @ lf-ssession-term-generation @ =
  lf-level-generation @ lf-ssession-level-generation @ = and
  lf-lscope-generation @ lf-ssession-context-generation @ = and ;

\ Add one validated child to the session worklist, or report capacity failure.
: lf-ssession-push ( node -- flag )
  lf-ssession-pending @ lf-term-capacity >= if drop false exit then
  lf-ssession-pending @ cells lf-ssession-work + !
  1 lf-ssession-pending +! true ;

\ Visit a node already checked for shape and representation; validate each
\ reachable symbolic level using the same budget and captured context.
: lf-ssession-visit ( node -- status )
  lf-term-read 0= if lf-repr-invalid exit then
  lf-ssession-second ! lf-ssession-first ! lf-ssession-tag !
  lf-ssession-tag @ lf-tag-symbolic-sort = if
    lf-ssession-first @ lf-ssession-fuel @ lf-lscope-check
    lf-lscope-fuel @ lf-ssession-fuel !
    case
      lf-lscope-ok of lf-repr-ok endof
      lf-lscope-invalid of lf-repr-invalid endof
      lf-lscope-exhausted of lf-repr-exhausted endof
      drop lf-repr-invalid 0
    endcase exit
  then
  lf-ssession-tag @ lf-tag-bvar = if lf-repr-ok exit then
  lf-ssession-tag @ lf-tag-app = lf-ssession-tag @ lf-tag-lam = or
  lf-ssession-tag @ lf-tag-pi = or 0= if lf-repr-invalid exit then
  lf-ssession-first @ lf-ssession-push 0= if lf-repr-exhausted exit then
  lf-ssession-second @ lf-ssession-push 0= if lf-repr-exhausted exit then
  lf-repr-ok ;

\ Check one root: syntax validation first, followed by level validation for
\ every reachable Sort. Both term passes and every level visit share fuel;
\ repeated DAG visits are charged repeatedly. Unreachable nodes are ignored.
\ The result establishes no binding scope, typing, equality or proof validity.
: lf-ssession-check ( root fuel -- status )
  dup 0< if 2drop lf-repr-invalid exit then lf-ssession-fuel !
  lf-ssession-current? 0= if drop lf-repr-invalid exit then
  dup lf-repr-symbolic lf-ssession-fuel @ lf-repr-check
  lf-repr-fuel @ lf-ssession-fuel !
  ?dup if nip exit then
  0 lf-ssession-pending !
  lf-ssession-push 0= if lf-repr-exhausted exit then
  begin lf-ssession-pending @ 0> while
    lf-ssession-fuel @ 0= if lf-repr-exhausted exit then
    -1 lf-ssession-fuel +! -1 lf-ssession-pending +!
    lf-ssession-pending @ cells lf-ssession-work + @
    lf-ssession-visit ?dup if exit then
  repeat lf-repr-ok ;

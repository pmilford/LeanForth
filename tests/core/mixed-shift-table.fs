\ Finite syntax comparison with Lean; no typing or proof is asserted.
require ../../src/core/constant-references.fs
require ../../src/core/constant-term-boundary.fs
require ../../src/core/generation-handles.fs
require ../../src/core/level-scope.fs
require ../../src/core/levels.fs
require ../../src/core/names.fs
require ../../src/core/symbolic-session.fs
require ../../src/core/tagged-sort-boundary.fs
require ../../src/core/terms.fs
require ../../src/kernel/mixed-shift.fs
decimal
create actual 2 cells allot
variable mixed-root
variable case-number
variable cutoff
variable amount
variable cref-index
variable cref-id

\ Build a fresh session for every observation so output allocations cannot
\ affect later cases. The constant has one symbolic universe argument.
: build-base ( -- )
  lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
  1 lf-lscope-context-add 0= if -1 throw then
  lf-ssession-begin 0= if -1 throw then
  1 lf-hlevel-param 0= if -1 throw then actual cell+ ! actual !
  0 lf-name-generation @ actual 1 lf-cref-new 0= if -1 throw then
  2dup cref-id ! cref-index !
  lf-cterm-new 0= if -1 throw then 2drop
  0 dup lf-level-identity 0= if -1 throw then lf-hterm-sort 0= if -1 throw then 2drop
  3 0 do i lf-term-bvar 0= if -1 throw then drop loop ;

: app ( a b -- node ) lf-term-app 0= if -1 throw then ;
: lam ( a b -- node ) lf-term-lam 0= if -1 throw then ;
: make-pi ( a b -- node ) lf-term-pi 0= if -1 throw then ;

\ Nodes 0..4 are the constant, Sort 0, and variables #0, #1, #2.
: build-case ( n -- node )
  case
    0 of 0 endof
    1 of 0 2 app endof
    2 of 0 3 app 2 swap app 0 swap lam endof
    3 of 0 2 app 3 0 app make-pi endof
    4 of 3 0 app 4 swap app 0 swap lam 1 swap lam endof
    -1 throw
  endcase ;

: emit-term ( node -- )
  lf-term-read 0= if -1 throw then rot case
    lf-tag-symbolic-sort of 0<> swap 0<> or if -1 throw then s" S " type endof
    lf-tag-constant of cref-id @ <> swap cref-index @ <> or if -1 throw then s" C " type endof
    lf-tag-bvar of drop s" V " type . endof
    lf-tag-app of s" A " type swap recurse recurse endof
    lf-tag-lam of s" L " type swap recurse recurse endof
    lf-tag-pi of s" P " type swap recurse recurse endof
    -1 throw
  endcase ;

: emit-table ( -- )
  5 0 do i case-number !
    3 0 do i cutoff !
      3 0 do i amount !
        build-base case-number @ build-case mixed-root !
        case-number @ . cutoff @ . amount @ .
        mixed-root @ dup lf-term-identity 0= if -1 throw then
        cutoff @ amount @ 10000 lf-mixed-shift
        lf-mshift-ok <> if 2drop -1 throw then
        2dup 10000 lf-cterm-check lf-repr-ok <> if 2drop -1 throw then
        drop emit-term cr
      loop
    loop
  loop ;
emit-table bye

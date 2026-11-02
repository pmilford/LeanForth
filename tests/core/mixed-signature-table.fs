\ Evaluate substituted levels for finite comparison with Lean; no typing.
include ../../src/core/terms.fs
include ../../src/core/names.fs
include ../../src/core/levels.fs
include ../../src/core/level-scope.fs
include ../../src/core/level-value.fs
include ../../src/core/tagged-sort-boundary.fs
include ../../src/core/symbolic-session.fs
include ../../src/core/generation-handles.fs
include ../../src/core/constant-references.fs
include ../../src/core/constant-term-boundary.fs
include ../../src/core/level-substitute.fs
include ../../src/core/mixed-level-substitute.fs
include ../../src/core/mixed-signature-probe.fs
decimal
create formals 2 cells allot
create actuals 4 cells allot
create cargs 4 cells allot
variable result-root
: save-pair ( level addr -- ) >r dup r@ ! lf-level-identity 0= if r> drop -1 throw then r> cell+ ! ;
: stamped-sort ( level -- node )
  dup lf-level-identity 0= if -1 throw then lf-hterm-sort 0= if -1 throw then drop ;
: build-case ( case -- )
  lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
  1 lf-lscope-context-add 0= if -1 throw then
  2 lf-lscope-context-add 0= if -1 throw then
  lf-ssession-begin 0= if -1 throw then
  0 s" f" lf-name-str 0= if -1 throw then drop
  0 s" g" lf-name-str 0= if -1 throw then drop
  0 s" candidate" lf-name-str 0= if -1 throw then drop
  1 lf-level-param 0= if -1 throw then drop
  2 lf-level-param 0= if -1 throw then drop
  2 lf-level-succ 0= if -1 throw then drop
  1 3 lf-level-max 0= if -1 throw then drop
  1 lf-level-succ 0= if -1 throw then drop
  1 2 lf-level-max 0= if -1 throw then drop
  2 1 lf-level-imax 0= if -1 throw then drop
  4 stamped-sort drop 1 stamped-sort drop
  1 cargs save-pair 7 cargs 2 cells + save-pair
  1 lf-name-generation @ cargs 2 lf-cref-new 0= if -1 throw then
  lf-cterm-new 0= if -1 throw then 2drop
  2 cargs save-pair
  2 lf-name-generation @ cargs 1 lf-cref-new 0= if -1 throw then
  lf-cterm-new 0= if -1 throw then 2drop
  0 lf-term-bvar 0= if -1 throw then drop
  3 4 lf-term-app 0= if -1 throw then drop
  2 5 lf-term-app 0= if -1 throw then drop
  1 6 lf-term-lam 0= if -1 throw then drop
  0 7 lf-term-pi 0= if -1 throw then drop
  1 formals ! 2 formals cell+ !
  case
    0 of 2 actuals save-pair 1 actuals 2 cells + save-pair endof
    1 of 3 actuals save-pair 6 actuals 2 cells + save-pair endof
    2 of 2 actuals save-pair 5 actuals 2 cells + save-pair endof
    -1 throw
  endcase
  lf-msp-begin 0= if -1 throw then
  lf-msp-token 0= if -1 throw then
  3 8 dup lf-term-identity 0= if -1 throw then
  formals 2 50000 lf-msp-put lf-msp-ok <> if -1 throw then
  lf-msp-token 0= if -1 throw then
  3 actuals 2 50000 lf-msp-specialize
  lf-msp-ok <> if -1 throw then drop result-root ! ;
: emit-level ( level -- )
  50000 lf-level-value-assigned lf-lvalue-ok <> if drop -1 throw then . ;
: emit-constant ( ref id -- )
  2dup lf-cref-read 0= if 2drop -1 throw then
  >r drop case 1 of s" C " type endof 2 of s" D " type endof -1 throw endcase r@ .
  r> 0 ?do 2dup i lf-cref-level 0= if 2drop -1 throw then drop emit-level loop 2drop ;
: emit-term ( term -- )
  lf-term-read 0= if -1 throw then rot case
    lf-tag-symbolic-sort of drop s" T " type emit-level endof
    lf-tag-constant of emit-constant endof
    lf-tag-bvar of drop s" V " type . endof
    lf-tag-app of s" A " type swap recurse recurse endof
    lf-tag-lam of s" L " type swap recurse recurse endof
    lf-tag-pi of s" P " type swap recurse recurse endof
    -1 throw
  endcase ;
: emit-table ( -- )
  3 0 do i build-case
    3 0 do 3 0 do
      lf-lassign-reset 1 j lf-lassign-add 0= if -1 throw then
      2 i lf-lassign-add 0= if -1 throw then
      k . j . i . result-root @ emit-term cr
    loop loop
  loop ;
emit-table bye

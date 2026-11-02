\ lf-mixed-level-substitute on the 48 observations of
\ tests/reference/term-level-substitute-table.lean: three simultaneous
\ substitutions of u and v in a constant-free term, each evaluated at
\ u, v = 0..3. Syntax only; no type is checked.
include ../../src/main.fs
decimal
create formals 2 cells allot
create actuals 4 cells allot
variable result-root

: stamped-sort ( level -- term )
  dup lf-level-identity 0= if -1 throw then
  lf-hterm-sort 0= if -1 throw then drop ;
: save-actual ( level position -- )
  2 * cells actuals + >r dup r@ !
  lf-level-identity 0= if r> drop -1 throw then r> cell+ ! ;

\ Build Pi (Sort (max u (succ v))) (lambda (Sort u) (app #0 (Sort (imax v u)))).
: build-case ( case -- )
  lf-term-reset lf-level-reset lf-lscope-context-reset
  1 lf-lscope-context-add 0= if -1 throw then
  2 lf-lscope-context-add 0= if -1 throw then
  lf-ssession-begin 0= if -1 throw then
  1 lf-level-param 0= if -1 throw then drop
  2 lf-level-param 0= if -1 throw then drop
  2 lf-level-succ 0= if -1 throw then drop
  1 2 lf-level-max 0= if -1 throw then drop
  1 lf-level-succ 0= if -1 throw then drop
  1 3 lf-level-max 0= if -1 throw then drop
  2 1 lf-level-imax 0= if -1 throw then drop
  6 stamped-sort drop 1 stamped-sort drop
  0 lf-term-bvar 0= if -1 throw then drop
  7 stamped-sort drop
  2 3 lf-term-app 0= if -1 throw then drop
  1 4 lf-term-lam 0= if -1 throw then drop
  0 5 lf-term-pi 0= if -1 throw then drop
  1 formals ! 2 formals cell+ !
  case
    0 of 2 0 save-actual 1 1 save-actual endof
    1 of 3 0 save-actual 4 1 save-actual endof
    2 of 2 0 save-actual 5 1 save-actual endof
    -1 throw
  endcase
  6 dup lf-term-identity 0= if -1 throw then
  formals actuals 2 50000 lf-mixed-level-substitute
  lf-mlsubst-ok <> if -1 throw then drop result-root ! ;

\ Output prefix term tags, evaluating each symbolic sort in current assignment.
: emit-term ( term -- )
  lf-term-read 0= if -1 throw then rot case
    lf-tag-symbolic-sort of
      drop 1 . 50000 lf-level-value-assigned
      lf-lvalue-ok <> if drop -1 throw then .
    endof
    lf-tag-bvar of drop 2 . . endof
    lf-tag-app of 3 . swap recurse recurse endof
    lf-tag-lam of 4 . swap recurse recurse endof
    lf-tag-pi of 5 . swap recurse recurse endof
    -1 throw
  endcase ;

: emit-table ( -- )
  3 0 do i build-case
    4 0 do 4 0 do
      lf-lassign-reset
      1 j lf-lassign-add 0= if -1 throw then
      2 i lf-lassign-add 0= if -1 throw then
      k . j . i . result-root @ emit-term cr
    loop loop
  loop ;
emit-table
bye

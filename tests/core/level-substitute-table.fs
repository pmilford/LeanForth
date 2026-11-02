\ Compare finite evaluations of simultaneous symbolic substitutions to Lean.
\ These values do not establish general symbolic equality or proof validity.
include ../../src/core/levels.fs
include ../../src/core/level-scope.fs
include ../../src/kernel/level-value.fs
include ../../src/kernel/level-substitute.fs
decimal

create formal-ids 2 cells allot
create actual-roots 2 cells allot
variable source-root
variable result-root

\ Source is imax(max(succ(u),v), imax(v,u)); IDs 1 and 2 name u and v.
: build-substitution-case ( case -- )
  lf-level-reset lf-lscope-context-reset
  1 lf-lscope-context-add 0= if -1 throw then
  2 lf-lscope-context-add 0= if -1 throw then
  1 lf-level-param 0= if -1 throw then drop
  2 lf-level-param 0= if -1 throw then drop
  1 lf-level-succ 0= if -1 throw then drop
  3 2 lf-level-max 0= if -1 throw then drop
  2 1 lf-level-imax 0= if -1 throw then drop
  4 5 lf-level-imax 0= if -1 throw then source-root !
  2 lf-level-succ 0= if -1 throw then drop
  1 2 lf-level-max 0= if -1 throw then drop
  1 formal-ids ! 2 formal-ids cell+ !
  case
    0 of 2 actual-roots ! 1 actual-roots cell+ ! endof
    1 of 7 actual-roots ! 8 actual-roots cell+ ! endof
    2 of 2 actual-roots ! 3 actual-roots cell+ ! endof
    -1 throw
  endcase
  source-root @ formal-ids actual-roots 2 50000 lf-lsubst
  lf-lsubst-ok <> if -1 throw then result-root ! ;

: emit-substitution-table ( -- )
  3 0 do
    i build-substitution-case
    4 0 do 4 0 do
      lf-lassign-reset
      1 j lf-lassign-add 0= if -1 throw then
      2 i lf-lassign-add 0= if -1 throw then
      k . j . i . result-root @ 50000 lf-level-value-assigned
      lf-lvalue-ok <> if drop -1 throw then . cr
    loop loop
  loop ;
emit-substitution-table
bye

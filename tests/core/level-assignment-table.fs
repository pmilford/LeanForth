\ Emit explicit symbolic-universe instances for comparison with Lean.
\ These are untrusted evaluations, not polymorphic proof judgments.
require ../../src/core/level-scope.fs
require ../../src/core/levels.fs
require ../../src/kernel/level-value.fs
decimal

\ Build imax(max(succ(u),v), imax(v,u)) with opaque IDs 1 and 2.
: build-assignment-expression ( -- )
  lf-level-reset lf-lscope-context-reset
  1 lf-lscope-context-add 0= if -1 throw then
  2 lf-lscope-context-add 0= if -1 throw then
  1 lf-level-param 0= if -1 throw then drop
  2 lf-level-param 0= if -1 throw then drop
  1 lf-level-succ 0= if -1 throw then drop
  3 2 lf-level-max 0= if -1 throw then drop
  2 1 lf-level-imax 0= if -1 throw then drop
  4 5 lf-level-imax 0= if -1 throw then drop ;

\ Evaluate every pair of assignments in [0,5], emitting one row per pair.
: emit-assignment-table ( -- )
  build-assignment-expression
  6 0 do 6 0 do
    lf-lassign-reset
    1 j lf-lassign-add 0= if -1 throw then
    2 i lf-lassign-add 0= if -1 throw then
    j . i . 6 50000 lf-level-value-assigned
    if drop -1 throw then . cr
  loop loop ;
emit-assignment-table
bye

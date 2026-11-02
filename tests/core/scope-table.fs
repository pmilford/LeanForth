\ Emit scope statuses for the same structurally constructed cases as the Lean
\ reference. These are syntax-closure observations, not theorem judgments.
include ../../src/core/terms.fs
include ../../src/legacy/scope.fs
decimal

\ Discard an allocated node index or fail if construction could not complete.
: require-node ( index true | false -- )
  0= if -1 throw then drop ;

\ Build every pair of four base nodes as an application, lambda and Pi, then
\ add twelve nested lambdas. Order matches the Lean reference table.
: build-scope-cases ( -- )
  lf-term-reset
  0 lf-term-sort require-node
  0 lf-term-bvar require-node
  1 lf-term-bvar require-node
  2 lf-term-bvar require-node
  4 0 do 4 0 do j i lf-term-app require-node loop loop
  4 0 do 4 0 do j i lf-term-lam require-node loop loop
  4 0 do 4 0 do j i lf-term-pi require-node loop loop
  12 0 do 0 i 4 + lf-term-lam require-node loop ;

\ Print node number and scope status with a generous finite visit budget.
: emit-scope-cases ( -- )
  build-scope-cases
  64 0 do i . i 100 lf-scope-check . cr loop ;
emit-scope-cases
bye

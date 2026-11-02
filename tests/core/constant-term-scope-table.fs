\ Scope statuses of lf-constant-term-scope for the cases of
\ tests/reference/scope-table.lean (Lean's hasLooseBVars): every app, lambda
\ and Pi pair of {Sort 0, #0, #1, #2}, then twelve nested lambdas. Status 0
\ is closed, 1 has a loose variable. Syntax closure only; no typing.
require ../../src/main.fs
include ../support/plain-terms.fs

\ Nodes 0..3 are Sort 0, #0, #1, #2; 4..51 the pairs; 52..63 the lambdas.
: build-scope-cases ( -- )
  fresh-session 0 make-sort drop 3 0 do i make-var drop loop
  4 0 do 4 0 do j i make-app drop loop loop
  4 0 do 4 0 do j i make-lam drop loop loop
  4 0 do 4 0 do j i make-pi drop loop loop
  12 0 do 0 i 4 + make-lam drop loop ;

\ Depth 0: the root has no binders around it.
: emit-scope-cases ( -- )
  build-scope-cases
  64 0 do i . i handle 0 100 lf-constant-term-scope . cr loop ;
emit-scope-cases
bye

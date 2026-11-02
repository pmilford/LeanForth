\ Emit experimental comparison statuses for terms constructed independently
\ in the Lean reference. Equality is not a theorem-validity judgment.
include ../../src/legacy/compare.fs
include ../support/term-cases.fs
decimal

\ Build a fixed, well-typed set of closed roots and their shared children.
: build-compare-cases ( -- )
  lf-term-reset
  0 lf-term-sort require-test-node drop
  1 lf-term-sort require-test-node drop
  0 lf-term-bvar require-test-node drop
  1 lf-term-bvar require-test-node drop
  1 2 lf-term-lam require-test-node drop
  4 0 lf-term-app require-test-node drop
  0 2 lf-term-lam require-test-node drop
  5 2 lf-term-lam require-test-node drop
  2 3 lf-term-pi require-test-node drop
  0 8 lf-term-pi require-test-node drop
  2 2 lf-term-lam require-test-node drop
  0 10 lf-term-lam require-test-node drop ;

\ Emit a case id and comparison status with a finite shared work budget.
: emit-comparison ( number left right -- )
  rot . 2000 lf-compare . cr ;

build-compare-cases
0 0 0 emit-comparison
1 0 1 emit-comparison
2 5 0 emit-comparison
3 11 11 emit-comparison
4 0 11 emit-comparison
5 6 7 emit-comparison
bye

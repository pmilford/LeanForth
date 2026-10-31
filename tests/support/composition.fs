\ Manually reconstruct the composition fixture's expression DAG in index order.
\ This helper only builds syntax; it does not import or check a declaration.
\ The caller must load the term module and term-cases helper first.
: build-composition ( -- )
  lf-term-reset
  0 lf-term-sort require-test-node drop
  2 lf-term-bvar require-test-node drop
  1 1 lf-term-pi require-test-node drop
  4 lf-term-bvar require-test-node drop
  3 lf-term-bvar require-test-node drop
  3 4 lf-term-pi require-test-node drop
  2 5 lf-term-pi require-test-node drop
  2 6 lf-term-pi require-test-node drop
  0 7 lf-term-pi require-test-node drop
  0 8 lf-term-pi require-test-node drop
  0 9 lf-term-pi require-test-node drop
  1 lf-term-bvar require-test-node drop
  0 lf-term-bvar require-test-node drop
  1 12 lf-term-app require-test-node drop
  11 13 lf-term-app require-test-node drop
  3 14 lf-term-lam require-test-node drop
  2 15 lf-term-lam require-test-node drop
  2 16 lf-term-lam require-test-node drop
  0 17 lf-term-lam require-test-node drop
  0 18 lf-term-lam require-test-node drop
  0 19 lf-term-lam require-test-node drop ;

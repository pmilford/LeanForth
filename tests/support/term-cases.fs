\ Shared test fixtures for the small experimental Lean-shaped expression DAGs.
\ The caller must include the term module before loading this helper.

\ Return the allocated index or fail the test if a constructor fails.
: require-test-node ( index true | false -- index )
  0= if -1 throw then ;

\ Rebuild a case in a fresh arena so its indices and capacity are predictable.
: build-test-case ( number -- root )
  lf-term-reset
  case
    0 of 0 lf-term-bvar require-test-node endof
    1 of 1 lf-term-bvar require-test-node endof
    2 of
      0 lf-term-sort require-test-node drop
      0 lf-term-bvar require-test-node drop
      1 lf-term-bvar require-test-node drop
      1 2 lf-term-app require-test-node drop
      0 3 lf-term-lam require-test-node
    endof
    3 of
      0 lf-term-bvar require-test-node drop
      1 lf-term-bvar require-test-node drop
      1 0 lf-term-app require-test-node drop
      0 2 lf-term-pi require-test-node
    endof
    4 of
      0 lf-term-sort require-test-node drop
      0 lf-term-bvar require-test-node drop
      1 lf-term-bvar require-test-node drop
      2 lf-term-bvar require-test-node drop
      3 2 lf-term-app require-test-node drop
      0 4 lf-term-lam require-test-node drop
      0 5 lf-term-lam require-test-node
    endof
    -1 throw
  endcase ;

\ Print a term in a test-only prefix format with fixed arity for each tag.
\ All nodes constructed by these fixtures have backward references.
: emit-test-term ( index -- )
  lf-term-read 0= if -1 throw then
  rot case
    lf-tag-sort of drop ." S " . endof
    lf-tag-bvar of drop ." V " . endof
    lf-tag-app of ." A " swap recurse recurse endof
    lf-tag-lam of ." L " swap recurse recurse endof
    lf-tag-pi of ." P " swap recurse recurse endof
    -1 throw
  endcase ;

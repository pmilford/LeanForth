\ Emit experimental inference statuses for malformed or ill-typed terms.
\ Statuses remain untrusted and cannot authorize or reject a theorem.
include ../../src/legacy/infer.fs
include ../support/term-cases.fs
decimal

\ Construct each negative case in a fresh arena in the reference order.
: build-negative-inference-case ( number -- root )
  lf-term-reset
  case
    0 of 0 lf-term-bvar require-test-node endof
    1 of
      0 lf-term-sort require-test-node drop
      0 0 lf-term-app require-test-node
    endof
    2 of
      0 lf-term-sort require-test-node drop
      0 lf-term-bvar require-test-node drop
      0 1 lf-term-app require-test-node
    endof
    3 of
      0 lf-term-sort require-test-node drop
      0 lf-term-bvar require-test-node drop
      0 1 lf-term-lam require-test-node drop
      2 1 lf-term-pi require-test-node
    endof
    4 of
      0 lf-term-sort require-test-node drop
      0 lf-term-bvar require-test-node drop
      0 1 lf-term-lam require-test-node drop
      2 0 lf-term-app require-test-node
    endof
    5 of
      0 lf-term-sort require-test-node drop
      1 lf-term-bvar require-test-node drop
      0 1 lf-term-pi require-test-node
    endof
    -1 throw
  endcase ;

\ Print case and status; discard the optional type-index placeholder.
: emit-negative-inference-table ( -- )
  6 0 do
    i . i build-negative-inference-case 50000 lf-infer nip . cr
  loop ;
emit-negative-inference-table
bye

\ Emit untrusted inferred type syntax for comparison with Lean's kernel.
\ Neither inference nor matching output registers or validates a theorem.
include ../../src/experimental/infer.fs
include ../support/term-cases.fs
include ../support/composition.fs
decimal

\ Rebuild each reference expression in a fresh arena.
: build-inference-case ( number -- root )
  lf-term-reset
  case
    0 of 0 lf-term-sort require-test-node endof
    1 of 1 lf-term-sort require-test-node endof
    2 of
      0 lf-term-sort require-test-node drop
      0 lf-term-bvar require-test-node drop
      0 1 lf-term-pi require-test-node
    endof
    3 of
      1 lf-term-sort require-test-node drop
      0 lf-term-bvar require-test-node drop
      0 1 lf-term-pi require-test-node
    endof
    4 of
      0 lf-term-sort require-test-node drop
      0 lf-term-bvar require-test-node drop
      1 1 lf-term-lam require-test-node drop
      0 2 lf-term-lam require-test-node
    endof
    5 of
      0 lf-term-sort require-test-node drop
      1 lf-term-sort require-test-node drop
      0 lf-term-bvar require-test-node drop
      1 2 lf-term-lam require-test-node drop
      3 0 lf-term-app require-test-node
    endof
    6 of build-composition 20 endof
    -1 throw
  endcase ;

\ Infer each case with a finite budget and print its resulting type structure.
: emit-inference-table ( -- )
  7 0 do
    i . i build-inference-case 50000 lf-infer
    lf-infer-ok <> if drop -1 throw then emit-test-term cr
  loop ;
emit-inference-table
bye

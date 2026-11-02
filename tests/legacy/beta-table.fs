\ Emit untrusted Forth weak-head beta results for direct comparison with Lean.
\ The shared prefix renderer is test-only and is not a proof serialization.
include ../../src/legacy/beta.fs
include ../support/term-cases.fs
decimal
variable beta-chain-input
variable beta-chain-identity

\ Rebuild each closed expression from the Lean oracle in a fresh arena.
: build-beta-case ( number -- root )
  lf-term-reset
  case
    0 of 0 lf-term-sort require-test-node endof
    1 of
      0 lf-term-sort require-test-node drop
      0 lf-term-bvar require-test-node drop
      0 1 lf-term-pi require-test-node
    endof
    2 of
      0 lf-term-sort require-test-node drop
      1 lf-term-sort require-test-node drop
      0 lf-term-bvar require-test-node drop
      1 2 lf-term-lam require-test-node drop
      3 0 lf-term-app require-test-node
    endof
    3 of
      0 lf-term-sort require-test-node drop
      1 lf-term-sort require-test-node drop
      0 lf-term-bvar require-test-node drop
      2 2 lf-term-lam require-test-node drop
      1 3 lf-term-lam require-test-node drop
      4 0 lf-term-app require-test-node
    endof
    4 of
      0 lf-term-sort require-test-node drop
      1 lf-term-sort require-test-node drop
      2 lf-term-sort require-test-node drop
      0 lf-term-bvar require-test-node drop
      3 3 lf-term-lam require-test-node drop
      2 4 lf-term-lam require-test-node drop
      5 1 lf-term-app require-test-node drop
      6 0 lf-term-app require-test-node
    endof
    5 of
      1 lf-term-sort require-test-node drop
      0 lf-term-bvar require-test-node drop
      0 1 lf-term-lam require-test-node drop
      2 1 lf-term-app require-test-node drop
      0 3 lf-term-lam require-test-node
    endof
    -1 throw
  endcase ;

\ Normalize each case with a finite budget and emit its prefix structure.
: emit-beta-table ( -- )
  6 0 do
    i . i build-beta-case 4000 lf-beta-whnf
    lf-beta-ok <> if drop -1 throw then emit-test-term cr
  loop
  3 0 do
    3 0 do
      6 j 3 * + i + .
      lf-term-reset
      j lf-term-sort require-test-node beta-chain-input !
      j 1+ lf-term-sort require-test-node
      0 lf-term-bvar require-test-node
      lf-term-lam require-test-node beta-chain-identity !
      i 1+ 0 do
        beta-chain-identity @ beta-chain-input @ lf-term-app require-test-node
        beta-chain-input !
      loop
      beta-chain-input @ 4000 lf-beta-whnf
      lf-beta-ok <> if drop -1 throw then emit-test-term cr
    loop
  loop ;
emit-beta-table
bye

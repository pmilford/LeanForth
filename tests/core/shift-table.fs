\ Emit deterministic prefix-form syntax after experimental de Bruijn shifts.
\ This output is a test representation, not a proof certificate or API format.
include ../../src/experimental/shift.fs
include ../support/term-cases.fs
decimal
variable shift-case
variable shift-cutoff
variable shift-amount

\ Print all five expressions with four cutoffs and four shift amounts.
: emit-shift-table ( -- )
  5 0 do i shift-case !
    4 0 do i shift-cutoff !
      4 0 do i shift-amount !
        shift-case @ . shift-cutoff @ . shift-amount @ .
        shift-case @ build-test-case shift-cutoff @ shift-amount @ 100 lf-shift
        lf-shift-ok <> if drop -1 throw then emit-test-term cr
      loop
    loop
  loop ;
emit-shift-table
bye

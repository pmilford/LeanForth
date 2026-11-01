\ Emit development analyzer results for finite comparison with pinned Lean.
\ Inputs are opcode data, not executed Forth or proofs of program behavior.
include ../../src/experimental/program-depth.fs
decimal
create program-depth-table 6 cells allot
variable program-depth-length
variable program-depth-number
variable program-depth-cases

\ Decode the least-significant base-three digits into the opcode array.
: build-program-depth-row ( number -- )
  program-depth-number !
  program-depth-length @ 0 ?do
    program-depth-number @ 3 /mod program-depth-number !
    program-depth-table i cells + !
  loop ;

\ Print length, encoding and minimum depth, in the same order as Lean.
: emit-program-depth-table ( -- )
  1 program-depth-cases !
  7 0 do
    i program-depth-length !
    program-depth-cases @ 0 ?do
      program-depth-length @ . i .
      i build-program-depth-row
      program-depth-table 6 program-depth-length @ program-depth-length @
      lf-program-required-depth 0= abort" analyzer failure" . cr
    loop
    program-depth-cases @ 3 * program-depth-cases !
  loop ;
emit-program-depth-table
bye

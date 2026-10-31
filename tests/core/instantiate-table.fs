\ Emit test-only prefix representations of instantiations for Lean comparison.
\ This is neither a serialized proof format nor a theorem acceptance test.
include ../../src/experimental/instantiate.fs
include ../support/term-cases.fs
decimal
variable inst-case
variable inst-replacement-case

\ Build one of five replacement expressions in the current fixture arena.
: build-test-replacement ( number -- root )
  case
    0 of 0 lf-term-bvar require-test-node endof
    1 of 1 lf-term-bvar require-test-node endof
    2 of 2 lf-term-bvar require-test-node endof
    3 of 0 lf-term-sort require-test-node endof
    4 of
      0 lf-term-sort require-test-node
      0 lf-term-bvar require-test-node
      lf-term-lam require-test-node
    endof
    -1 throw
  endcase ;

\ Compare five open expressions with five replacements, rebuilding the arena
\ for every row to avoid dependencies on earlier allocations or reset handles.
: emit-inst-table ( -- )
  5 0 do i inst-case !
    5 0 do i inst-replacement-case !
      inst-case @ . inst-replacement-case @ .
      inst-case @ build-test-case
      inst-replacement-case @ build-test-replacement
      200 lf-instantiate lf-inst-ok <> if drop -1 throw then
      emit-test-term cr
    loop
  loop ;
emit-inst-table
bye

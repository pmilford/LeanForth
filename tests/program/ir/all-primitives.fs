\ Every primitive of IR 0.1 once, in the order of Prim in
\ tests/reference/program-ir.lean, so that make reference-program-ir
\ compares every spelling the reader writes with the one Lean prints. The
\ reader reads this file; it is not meant to be run.
: all-primitives
  dup drop swap over nip tuck rot 2dup 2drop >r r> r@
  + - * / mod negate abs 1+ 1- = <> < > 0= 0<> 0< 0>
  and or xor invert rshift max min true false ;

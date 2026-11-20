\ lf-mixed-shift on the five terms of tests/reference/shift-table.lean
\ (Lean's liftLooseBVars) for cutoffs and amounts 0..3: 80 rows of case,
\ cutoff, amount and the shifted syntax. Syntax only; no typing.
require ../../src/load/kernel.fs
include ../support/plain-terms.fs
include ../support/plain-cases.fs

: emit-shift ( case cutoff amount -- )
  rot dup . build-plain-case handle 2swap over . dup .
  10000 lf-mixed-shift ok? must drop emit-term cr ;
: emit-shift-table ( -- )
  5 0 do 4 0 do 4 0 do k j i emit-shift loop loop loop ;
emit-shift-table
bye

\ lf-mixed-instantiate on the 25 cases of tests/reference/instantiate-table.lean
\ (Lean's instantiate1): five open sources, including bare variables and a
\ loose variable lowered under a binder, times the replacements #0, #1, #2,
\ Sort 0 and fun _ : Sort 0 => #0. Syntax only; no typing.
include ../../src/main.fs
include ../support/plain-terms.fs
include ../support/plain-cases.fs

: build-replacement ( n -- root )
  case
    0 of 0 make-var endof
    1 of 1 make-var endof
    2 of 2 make-var endof
    3 of 0 make-sort endof
    4 of 0 make-sort 0 make-var make-lam endof
    -1 throw
  endcase ;
: emit-instantiation ( case replacement -- )
  over . dup . swap build-plain-case handle rot build-replacement handle
  10000 lf-mixed-instantiate ok? must drop emit-term cr ;
: emit-instantiate-table ( -- ) 5 0 do 5 0 do j i emit-instantiation loop loop ;
emit-instantiate-table
bye

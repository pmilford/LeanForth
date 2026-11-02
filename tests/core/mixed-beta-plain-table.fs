\ lf-mixed-beta (weak-head beta) on the 15 closed cases of
\ tests/reference/beta-table.lean (Lean's Kernel.whnf): Prop, a Pi root,
\ simple, dependent and nested polymorphic identity redexes, a lambda whose
\ body is a redex, and identity chains of depth 1..3 at Sorts 0..2.
require ../../src/main.fs
include ../support/plain-terms.fs

\ fun _ : Sort level => #0
: identity-at ( level -- node ) make-sort 0 make-var make-lam ;
: build-beta-case ( n -- root )
  fresh-session case
    0 of 0 make-sort endof
    1 of 0 make-sort 0 make-var make-pi endof
    2 of 1 identity-at 0 make-sort make-app endof
    3 of 1 make-sort 0 make-var 0 make-var make-lam make-lam 0 make-sort make-app endof
    4 of
      2 make-sort 0 make-var 0 make-var make-lam make-lam
      1 make-sort make-app 0 make-sort make-app
    endof
    5 of 1 make-sort 1 identity-at 0 make-var make-app make-lam endof
    -1 throw
  endcase ;
\ Identity at Sort level+1 applied depth times to Sort level.
: build-chain ( level depth -- root )
  fresh-session swap dup 1+ identity-at swap make-sort
  rot 0 ?do over swap make-app loop nip ;
: emit-beta ( n root -- ) swap . handle 4000 lf-mixed-beta ok? must drop emit-term cr ;
: emit-beta-table ( -- )
  6 0 do i i build-beta-case emit-beta loop
  3 0 do 3 0 do 6 j 3 * + i + j i 1+ build-chain emit-beta loop loop ;
emit-beta-table
bye

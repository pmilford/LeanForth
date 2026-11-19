\ The first or last index of a linear search by a caller's test (review F4 of
\ 2026-11-18 and the author review's R3: the linear finds of a store, slab
\ or table by index). A general tool with no Lean knowledge; untrusted.
\
\ find-index ( x n xt -- k true | false ) runs xt ( x k -- x flag ) for
\ k = 0, 1, ... n-1 and gives the first k for which it answers true (any
\ nonzero flag), after which none runs; else false. x, one value the test
\ reads (a key, a record), is dropped either way; n <= 0 gives false. It
\ is any? of outcome.fs that keeps the place. Cost: one call of xt per
\ index up to the first hit; no memory; the return stack holds two loop
\ frames, so xt may use it but must leave it as it found it.
\
\ find-last-index ( x n xt -- k true | false ) is the same search from
\ k = n-1 down to 0: the last k for which xt answers true (Lean's
\ findRev?, findDeclRevM?), at the same cost from the end.
\
\ Example: the first negative cell of a table 5 -2 -7 is at index 1; a
\ search of no cells finds none.
\   create sample 5 , -2 , -7 ,
\   : cell-neg? ( addr k -- addr flag ) cells over + @ 0< ;
\   sample 3 ' cell-neg? find-index . .
\   sample 0 ' cell-neg? find-index .   \ prints: -1 1 0
\   sample 3 ' cell-neg? find-last-index . .   \ prints: -1 2
\
\ Interface: find-index, find-last-index.
\ State: none. Requires module.fs (ADR 0010). Loads in decimal whatever
\ BASE is.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ./module.fs

lf-lib-private module-open
lf-lib set-current
\ The first k < n for which xt ( x k -- x flag ) answers true, x dropped.
\ (The outer loop runs once, with xt as its index, so that j gives xt to
\ the inner loop without a return-stack operation of its own.)
: find-index ( x n xt -- k true | false )
  dup 1+ swap ?do 0 max 0 ?do i j execute if drop i true unloop unloop exit then
  loop loop drop false ;
\ The last k < n for which xt ( x k -- x flag ) answers true, x dropped.
: find-last-index ( x n xt -- k true | false )
  over 1 < if 2drop drop false exit then
  dup 1+ swap ?do 1- 0 swap do i j execute if drop i true unloop unloop exit then
  -1 +loop loop drop false ;
module-close
base !   \ the BASE this file was loaded with

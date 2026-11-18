\ The first index of a linear search by a caller's test (review F4 of
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
\ Example, the first negative cell of a table 5 -2 -7:
\   create table 5 , -2 , -7 ,
\   : cell-neg? ( addr k -- addr flag ) cells over + @ 0< ;
\   table 3 ' cell-neg? find-index   \ 1 true
\
\ Interface: find-index.
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
module-close
base !   \ the BASE this file was loaded with

\ Shared fixtures without constants, with Sort 0 symbolic. Requires
\ plain-terms.fs. Test-only.

\ The composition fixture's 21-node DAG (tests/reference/composition.lean,
\ node for node): fun A B C (f : B -> C) (g : A -> B) (x : A) => f (g x).
\ Node 10 is its claim and node 20, returned, its value.
: build-composition ( -- root )
  fresh-session 0 make-sort drop 2 make-var drop 1 1 make-pi drop
  4 make-var drop 3 make-var drop 3 4 make-pi drop 2 5 make-pi drop
  2 6 make-pi drop 0 7 make-pi drop 0 8 make-pi drop 0 9 make-pi drop
  1 make-var drop 0 make-var drop 1 12 make-app drop 11 13 make-app drop
  3 14 make-lam drop 2 15 make-lam drop 2 16 make-lam drop
  0 17 make-lam drop 0 18 make-lam drop 0 19 make-lam ;

\ The five open source terms of the Lean shift and instantiation tables
\ (tests/reference/shift-table.lean, instantiate-table.lean).

\ Build case n in a fresh session and return its root.
: build-plain-case ( n -- root )
  fresh-session case
    0 of 0 make-var endof
    1 of 1 make-var endof
    2 of 0 make-sort 0 make-var 1 make-var make-app make-lam endof
    3 of 0 make-var 1 make-var 0 make-var make-app make-pi endof
    4 of
      0 make-sort dup 2 make-var 1 make-var make-app make-lam make-lam
    endof
    -1 throw
  endcase ;

\ lf-mixed-infer on terms without constants, for comparison with five Lean
\ tables. Each row starts with its section letter, which the differential
\ driver strips before comparing the section with its Lean table:
\   P  tests/reference/infer-table.lean: 7 closed terms and their types;
\   N  infer-negative-table.lean: 6 terms Lean rejects (status printed);
\   O  symbolic-infer-oracle.lean: Sort u, Pi (A : Sort u), Sort u, and
\      Sort u applied to itself, with universes compared symbolically;
\   B  tagged-binder-table.lean: 6 binder terms over Sort u, u = 0..2;
\   A  tagged-application-table.lean: 6 application terms, u = 0..2.
\ Inferred types are untrusted observations, never theorem acceptance.
require ../../src/main.fs
include ../support/plain-terms.fs
include ../support/plain-cases.fs

: infer ( root -- type identity status ) >r empty-token r> handle 50000 lf-mixed-infer ;
: infer-ok ( root -- type ) infer ok? must drop ;
\ Rejected input must be invalid, or unknown where the caller allows it.
: rejected? ( status unknown-allowed -- flag )
  over outcome-unknown = and swap outcome-invalid = or ;

\ fun _ : Sort 0 => fun x : #0 => x
: prop-identity ( -- node ) 0 make-sort 0 make-var 0 make-var make-lam make-lam ;
: build-positive ( n -- root )
  dup 6 = if drop build-composition exit then
  fresh-session case
    0 of 0 make-sort endof
    1 of 1 make-sort endof
    2 of 0 make-sort 0 make-var make-pi endof
    3 of 1 make-sort 0 make-var make-pi endof
    4 of prop-identity endof
    5 of 1 make-sort 0 make-var make-lam 0 make-sort make-app endof
    -1 throw
  endcase ;
: build-negative ( n -- root )
  fresh-session case
    0 of 0 make-var endof
    1 of 0 make-sort dup make-app endof
    2 of 0 make-sort 0 make-var make-app endof
    3 of 0 make-sort 0 make-var make-lam 0 make-var make-pi endof
    4 of 0 make-sort 0 make-var make-lam 0 make-sort make-app endof
    5 of 0 make-sort 1 make-var make-pi endof
    -1 throw
  endcase ;
\ Unbound variables (cases 0, 2 and 5) must be invalid; the other ill-typed
\ terms may also be unknown.
: negative-status ( n -- status ) build-negative infer nip nip ;
: emit-positive ( n -- ) ." P " dup . build-positive infer-ok emit-term cr ;
: emit-negative ( n -- ) ." N " dup . negative-status . cr ;

\ Section O: the type of Sort u must be a Sort of a level equal to succ u,
\ that of Pi (A : Sort u), Sort u one of imax (succ u) (succ u).
: sort-level ( node -- level ) lf-term-read must rot lf-tag-symbolic-sort = must drop ;
: same-level? ( left right -- flag ) 10000 lf-level-compare ok? ;
: succ-u ( -- level ) level-u lf-level-succ must ;
: oracle-sort ( -- flag )
  fresh-session level-u make-sort infer-ok sort-level succ-u same-level? ;
: oracle-pi ( -- flag )
  fresh-session level-u make-sort dup make-pi infer-ok sort-level
  succ-u succ-u lf-level-imax must same-level? ;
: oracle-app ( -- flag )
  fresh-session level-u make-sort dup make-app infer nip nip true rejected? ;
: emit-oracle ( n flag word-addr word-len -- )
  rot must ." O " rot . type cr ;
: emit-oracles ( -- )
  0 oracle-sort s" OK" emit-oracle
  1 oracle-pi s" OK" emit-oracle
  2 oracle-app s" REJECT" emit-oracle ;

\ Sections B and A: Sort u is node 0, #0 node 1, #1 node 2.
: u-base ( -- ) fresh-session level-u make-sort drop 0 make-var drop 1 make-var drop ;
: build-binder ( n -- root )
  u-base case
    0 of 1 1 make-lam 0 swap make-lam endof
    1 of 2 2 make-lam 1 swap make-lam 0 swap make-lam endof
    2 of 1 2 make-pi 0 swap make-pi endof
    3 of 1 2 make-pi 2 2 make-lam make-lam 0 swap make-lam endof
    4 of 1 endof
    5 of 0 2 make-lam endof
    -1 throw
  endcase ;
: sort-max-zero ( -- node ) level-u 0 lf-level-max must make-sort ;
: build-application ( n -- root )
  u-base case
    0 of 2 1 make-lam 1 make-app 1 swap make-lam 0 swap make-lam endof
    1 of 0 1 make-lam 1 make-app 0 swap make-lam endof
    2 of
      0 1 make-lam 2 make-app 1 make-lam 1 make-app 1 swap make-lam 0 swap make-lam
    endof
    3 of sort-max-zero 0 1 make-lam 1 make-app make-lam endof
    4 of 1 1 make-app 0 swap make-lam endof
    5 of 0 1 make-lam 1 make-app 1 swap make-lam 0 swap make-lam endof
    -1 throw
  endcase ;
\ Lean's inferred types may be more reduced than the Forth result, so the
\ application section prints the weak-head normal form at every node.
: emit-whnf ( node -- )
  handle 10000 lf-mixed-beta ok? must drop
  lf-term-read must rot case
    lf-tag-symbolic-sort of drop ." S " emit-level endof
    lf-tag-bvar of drop ." V " . endof
    lf-tag-app of ." A " swap recurse recurse endof
    lf-tag-lam of ." L " swap recurse recurse endof
    lf-tag-pi of ." P " swap recurse recurse endof
    -1 throw
  endcase ;
\ Cases 0..3 must infer; 4 and 5 must be rejected (invalid, or unknown for
\ the application section's type mismatch).
: emit-u-case ( u n root unknown-allowed xt -- )
  >r >r rot dup . -rot over . swap 4 < if
    r> drop infer ok? must drop swap assign-u ." OK " r> execute
  else
    infer nip nip r> rejected? must r> 2drop ." REJECT "
  then cr ;
: emit-binder ( u n -- )
  ." B " dup build-binder false ['] emit-term emit-u-case ;
: emit-application ( u n -- )
  ." A " dup build-application true ['] emit-whnf emit-u-case ;

: emit-infer-table ( -- )
  7 0 do i emit-positive loop
  6 0 do i emit-negative loop
  emit-oracles
  3 0 do 6 0 do j i emit-binder loop loop
  3 0 do 6 0 do j i emit-application loop loop ;
emit-infer-table
bye

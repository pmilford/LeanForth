\ The head of a term in weak-head beta normal form, as ADR 0011's rules
\ name it: rigid when the head is a Sort, a Pi, a lambda or a variable
\ (Lean's whnf leaves such a term as it is, fact 3), flexible when it is a
\ constant (Lean may unfold it, fact 2). A variable is a bound variable
\ or a free variable of the local context (core/local-context.fs), the
\ form the checker's terms have since plan task 4.2.2a; a let variable,
\ which Lean's whnf replaces by its value, does not occur before plan
\ task 4.2.3 and must then not count as rigid. The caller reduces the
\ term first (mixed-beta); this module only reads the reduced node and its
\ application spine. Untrusted; part of the first checker's [kernel] path,
\ not yet through the review gate.
\ State: none. The tag constants are shared and read-only.

require ../lib/lib.fs
require ../core/constant-term-boundary.fs
require ../core/local-context.fs
require ../core/tagged-sort-boundary.fs
require ../core/terms.fs

\ Head kinds. A Sort or Pi applied to arguments is rigid but none of the
\ shapes rules D2-D5 compare; it is ill typed, so no checked term has it.
0 constant lf-head-none        \ no rule applies: a concrete Sort, a lambda
                               \ applied to arguments, an unreadable node
1 constant lf-head-sort        \ a symbolic Sort
2 constant lf-head-pi
3 constant lf-head-lam
4 constant lf-head-var         \ a bound or free variable, with or without arguments
5 constant lf-head-applied     \ a Sort or Pi applied to arguments
6 constant lf-head-constant    \ a constant, with or without arguments

\ The head of a node's application spine and the number of arguments.
\ Unchecked: node is valid. Children come earlier in the store, so the
\ spine ends within lf-term-capacity steps (the bound only guards a
\ corrupted store).
: lf-mhead-app? ( node -- flag ) lf-term-tag@ lf-tag-app = ;
: lf-mhead-more? ( node count -- flag ) lf-term-capacity < swap lf-mhead-app? and ;
: lf-mhead-spine ( node -- head count )
  0 begin 2dup lf-mhead-more? while 1+ swap lf-term-first@ swap repeat ;

\ The kind of a spine's head node alone, then with its arguments.
: lf-mhead-leaf ( head -- kind )
  lf-term-tag@ case
    lf-tag-symbolic-sort of lf-head-sort endof  lf-tag-pi of lf-head-pi endof
    lf-tag-lam of lf-head-lam endof  lf-tag-bvar of lf-head-var endof
    lf-tag-fvar of lf-head-var endof
    lf-tag-constant of lf-head-constant endof  lf-head-none swap endcase ;
: lf-mhead-applied ( kind -- kind' )
  case lf-head-sort of lf-head-applied endof
    lf-head-pi of lf-head-applied endof
    lf-head-lam of lf-head-none endof dup endcase ;

\ The kind of a reduced node; an invalid index is lf-head-none.
: lf-mhead-kind ( node -- kind )
  dup lf-term-valid? 0= if drop lf-head-none exit then
  lf-mhead-spine >r lf-mhead-leaf r> if lf-mhead-applied then ;

\ Rigid kinds, and the two tests of rules F1 and S1/S2: rigid and not a
\ Pi (Lean's ensure_pi fails), rigid and not a Sort (ensure_sort fails).
: lf-mhead-rigid? ( kind -- flag ) lf-head-sort lf-head-applied 1+ within ;
: lf-mhead-not-pi? ( kind -- flag ) dup lf-mhead-rigid? swap lf-head-pi <> and ;
: lf-mhead-not-sort? ( kind -- flag ) dup lf-mhead-rigid? swap lf-head-sort <> and ;
\ The shapes rules D1-D5 compare: a Sort, a Pi, a lambda or a bound
\ variable with or without arguments.
: lf-mhead-shape? ( kind -- flag ) lf-head-sort lf-head-var 1+ within ;

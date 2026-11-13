\ Structural term equality and eta shapes for the front end's unifier
\ (plan FE1c; ADR 0021 D6), ports of Lean 4.35.0's Expr.eqv (Lean/Expr
\ .lean, the `==` of Expr: alpha equivalence, binder names and binder
\ information ignored), Expr.etaExpanded? and Lean's LBool.
\ - lf-meta-eqv ( a b -- flag outcome ): two terms equal node for node: a
\   bound variable by its index, a Sort by its level and a constant by
\   its name and universe arguments (Level.beq, level-simp.fs), a literal
\   by its value, a projection by its structure's name and index, a free
\   variable or metavariable only as the same node; the store may hold
\   equal terms twice when it does not share (core/terms.fs), so equal
\   leaves of two nodes are compared by content.
\ - lf-meta-eta-expanded ( e -- f flag outcome ): etaExpanded?: e is
\   fun x1 .. xn => f x1 .. xn (n >= 0) with no xi in f: flag true and f;
\   else false and e. Lean assumes e closed; so does this.
\ - LBool, Lean's three-valued answer: lf-lb-false, lf-lb-true,
\   lf-lb-undef, and lf-lb ( flag -- lbool ).
\ - lf-meta-name? ( c-addr u name -- flag ): the name is the dotted text
\   of one or two string parts ("Nat.succ"; Lean's match_expr);
\   lf-meta-const-named? ( t c-addr u -- flag ): t is that constant
\   (isConstOf); lf-meta-head ( t -- head ): getAppFn.
\ The pairs still to compare wait on a heap stack (plan task 6.2.0).
\ Outcomes: ok; full when the heap has no room; invalid for a term that
\ is not live. Untrusted front-end code.
\ State: the slab eq-pairs, a member of the checker context (ADR 0009);
\ one comparison at a time.

require ../lib/lib.fs
require ../core/terms.fs
require ../core/names.fs
require ../core/name-equal.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/tagged-sort-boundary.fs
require ../core/literals.fs
require ../core/projections.fs
require ../core/local-context.fs
require ../core/mvar-leaves.fs
require ./level-simp.fs
require ./instantiate.fs

0 constant lf-lb-false  1 constant lf-lb-true  2 constant lf-lb-undef
: lf-lb ( flag -- lbool ) if lf-lb-true else lf-lb-false then ;

2 cells context-slab: eq-pairs
: eq-push ( a b -- outcome )
  1 eq-pairs slab-claim dup ok? if drop eq-pairs slab-at 2! outcome-ok else nip nip nip
  then ;
: eq-pop ( -- a b ) eq-pairs dup slab-count 1- swap slab-at 2@ -1 eq-pairs slab-commit ;
: eq-tag ( t -- tag ) lf-term-tag@ ;


\ Leaves by content: names by their parts, constants with their levels.
: eq-name= ( a b -- flag ) 2dup = if 2drop true else lf-name-same? then ;
: eq-slot ( const -- slot ) lf-term-first@ lf-cref-slot ;
: eq-level@ ( addr i -- level ) lf-cref-pair@ drop ;
: eq-arity= ( s1 s2 -- flag ) lf-cref-pairs nip swap lf-cref-pairs nip = ;
: eq-names= ( s1 s2 -- flag ) lf-cref-name@ drop swap lf-cref-name@ drop eq-name= ;
: eq-level-of ( slot i -- level ) swap lf-cref-pairs drop swap eq-level@ ;
: eq-level-at ( s1 s2 i -- flag outcome )
  tuck eq-level-of >r eq-level-of r> lf-meta-level= ;
\ Each pair of universe arguments, in order, until one differs.
: eq-levels ( s1 s2 -- flag outcome )
  over lf-cref-pairs nip 0 ?do
    2dup i eq-level-at ok-then? 0= if nip nip false swap unloop exit then
    0= if 2drop false outcome-ok unloop exit then
  loop 2drop true outcome-ok ;
: eq-const ( a b -- flag outcome )
  eq-slot swap eq-slot 2dup eq-arity= 0= if 2drop false outcome-ok exit then
  2dup eq-names= if eq-levels else 2drop false outcome-ok then ;
: eq-fields ( a b -- flag )
  over lf-term-first@ over lf-term-first@ = if lf-term-second@ swap lf-term-second@ =
  else 2drop false then ;
: eq-proj ( a b -- flag )
  over lf-term-second@ over lf-term-second@ = if lf-term-first@ swap lf-term-first@
  eq-name=
  else 2drop false then ;
: eq-unshared? ( a -- flag ) eq-tag dup lf-tag-fvar = swap lf-tag-mvar = or ;
: eq-sorts ( a b -- flag outcome ) lf-term-first@ swap lf-term-first@ lf-meta-level= ;
\ A literal, a projection's leaf or any other leaf.
: eq-plain ( a b -- flag outcome )
  over eq-tag lf-tag-lit = if lf-lit-same? outcome-ok exit then
  over eq-tag lf-tag-proj = if eq-proj else eq-fields then outcome-ok ;
: eq-leaf ( a b -- flag outcome )
  over eq-unshared? if 2drop false outcome-ok exit then
  over eq-tag lf-tag-symbolic-sort = if eq-sorts exit then
  over eq-tag lf-tag-constant = if eq-const else eq-plain then ;

\ One pair: the same node, a binary node's parts pushed, or two leaves.
: eq-parts ( a b -- flag outcome )
  2dup lf-term-second@ swap lf-term-second@ eq-push dup ok? 0= if nip nip false swap exit
  then
  drop lf-term-first@ swap lf-term-first@ eq-push true swap ;
: eq-step ( a b -- flag outcome )
  2dup = if 2drop true outcome-ok exit then
  over eq-tag over eq-tag <> if 2drop false outcome-ok exit then
  over eq-tag lf-term-binary-tag? if eq-parts else eq-leaf then ;
: eq-more? ( -- flag ) eq-pairs slab-count 0> ;
: eq-run ( -- flag outcome )
  begin eq-more? while eq-pop eq-step dup ok? 0= if nip false swap exit then drop
  0= if false outcome-ok exit then repeat true outcome-ok ;
: lf-meta-eqv ( a b -- flag outcome )
  2dup lf-term-pair-valid? 0= if 2drop false outcome-invalid exit then
  2dup = if 2drop true outcome-ok exit then
  eq-pairs slab-clear eq-push dup ok? if drop eq-run else false swap then ;

\ A name against a dotted text of one or two string parts (Lean's
\ match_expr and isConstOf compare names so); the anonymous name is 0.
: eq-dot ( c-addr u -- i ) -1 swap 0 ?do over i + c@ [char] . = if drop i then loop nip ;
: eq-part ( c-addr u -- part u2 ) 2dup eq-dot 1+ /string ;
: eq-rest ( c-addr u -- c-addr i ) 2dup eq-dot nip ;
\ The name is one string part, the text.
: eq-text= ( c-addr u name -- flag )
  dup lf-name-tag@ lf-name-tag-str = if lf-name-text compare 0= else drop 2drop false then
  ;
: eq-top? ( c-addr u name -- flag ) dup lf-name-prefix@ 0= if eq-text= else drop 2drop
  false then ;
: eq-two ( c-addr u name -- flag )
  >r 2dup eq-part r@ eq-text= if eq-rest r> lf-name-prefix@ eq-top? else r> drop 2drop
  false then ;
: lf-meta-name? ( c-addr u name -- flag ) >r 2dup eq-dot 0< if r> eq-top? else r> eq-two
  then ;
\ A term that is the constant of that name (Lean's isConstOf).
: lf-meta-const-named? ( t c-addr u -- flag )
  rot dup eq-tag lf-tag-constant = if eq-slot lf-cref-name@ drop lf-meta-name?
  else drop 2drop false then ;
: lf-meta-head ( t -- head ) begin dup eq-tag lf-tag-app = while lf-term-first@ repeat ;


\ etaExpanded?: the lambdas taken off, then the body's arguments, from the
\ last, must be #0, #1, ... and what is left must have no loose variable.
: eq-lam? ( t -- flag ) eq-tag lf-tag-lam = ;
: eq-lams ( e -- body n ) 0 swap begin dup eq-lam? while lf-term-second@ swap 1+ swap
  repeat swap ;
: eq-bvar? ( t i -- flag ) over eq-tag lf-tag-bvar = if swap lf-term-first@ = else 2drop
  false then ;
: eq-arg-i? ( body i -- flag )
  over eq-tag lf-tag-app = if swap lf-term-second@ swap eq-bvar? else 2drop false then ;
: eq-peel ( body n -- f flag )
  0 ?do dup i eq-arg-i? 0= if false unloop exit then lf-term-first@ loop true ;
: eq-closed ( e f -- f' flag outcome )
  dup lf-meta-loose ok-then? 0= if nip false swap exit then
  if drop false else nip true then outcome-ok ;
: lf-meta-eta-expanded ( e -- f flag outcome )
  dup eq-lams eq-peel if eq-closed else drop false outcome-ok then ;

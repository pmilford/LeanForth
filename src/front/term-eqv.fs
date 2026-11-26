\ Structural term equality and eta shapes for the front end's unifier
\ (plan FE1c; ADR 0021 D6), ports of Lean 4.35.0's Expr.eqv (Lean/Expr
\ .lean, the `==` of Expr: alpha equivalence, binder names and binder
\ information ignored), Expr.etaExpanded? and Lean's LBool.
\ - lf-meta-eqv ( a b -- flag outcome ): two terms equal node for node: a
\   bound variable by its index, a Sort by its level and a constant by
\   its name and universe arguments (Level.beq, level-simp.fs), a natural
\   or string literal by its value or text, a projection by its
\   structure's name and index, a free
\   variable or metavariable only as the same node; the store may hold
\   equal terms twice when it does not share (core/terms.fs), so equal
\   leaves of two nodes are compared by content.
\ - lf-meta-equal? ( a b -- flag outcome ): Expr.equal, which also
\   compares binder names and binder information: the same node, or two
\   terms lf-meta-eqv finds equal that hold no lambda, pi or let (two
\   that do, as different nodes, answer unsupported: the binder table's
\   names are not compared yet); replaceLocalDeclDefEq's test
\   (meta-tactic/assert.fs).
\ - lf-meta-eta-expanded ( e -- f flag outcome ): etaExpanded?: e is
\   fun x1 .. xn => f x1 .. xn (n >= 0) with no xi in f: flag true and f;
\   else false and e. Lean assumes e closed; so does this.
\ - LBool, Lean's three-valued answer: lf-lb-false, lf-lb-true,
\   lf-lb-undef, and lf-lb ( flag -- lbool ).
\ - lf-meta-name? ( c-addr u name -- flag ): the name is the dotted text
\   ("Nat.succ"; Lean's match_expr), core/statement-match.fs's
\   lf-name-dotted? with the text first: names of any number of parts,
\   as Lean compares them (until 2026-11-13 the front end's own copy
\   took at most two parts, and no caller passes more; defeq.fs tests
\   three);
\   lf-meta-const-named? ( t c-addr u -- flag ): t is that constant
\   (isConstOf); lf-meta-head ( t -- head ): getAppFn; lf-meta-head-name
\   ( t -- name true | false ): getAppFn.constName?;
\   lf-meta-app-of? ( t n c-addr u -- flag ): t has n arguments and the
\   constant of the dotted name at its head (Lean's match_expr shapes);
\   lf-meta-nth-arg ( t i n -- a ): argument i, the first 0, of such a t;
\   lf-meta-app-arg ( t i -- a ): the same, n t's own count (getArg!:
\   unchecked, i below the count);
\   lf-meta-succ? ( t -- flag ): t is Nat.succ x; lf-and-app?, lf-iff-app?
\   lf-not-app? ( t -- flag ): t is And p q, Iff p q, Not p (Lean's and?,
\   iff?, not?).
\ - Type annotations (Expr.lean:1716-1745): lf-meta-opt-auto? ( t -- flag )
\   t is optParam a b or autoParam a b (isOptParam, isAutoParam);
\   lf-meta-out-param? ( t -- flag ) t is outParam a or semiOutParam a;
\   lf-meta-consume-annotations ( t -- t' ) consumeTypeAnnotations: from
\   optParam a b and autoParam a b a, from outParam a and semiOutParam a
\   a, again while one is at the top (nested ones stay).
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
require ../core/string-literals.fs
require ../core/projections.fs
require ../core/local-context.fs
require ../core/mvar-leaves.fs
require ../core/statement-match.fs
require ./level-simp.fs
require ./instantiate.fs
require ./meta-spine.fs
require ./term-find.fs

0 constant lf-lb-false  1 constant lf-lb-true  2 constant lf-lb-undef
: lf-lb ( flag -- lbool ) if lf-lb-true else lf-lb-false then ;

2 cells context-slab: eq-pairs
: eq-push ( a b -- outcome ) eq-pairs slab-2push ;

\ Leaves by content: names by their parts, constants with their levels.
: eq-name= ( a b -- flag ) 2dup = if 2drop true else lf-name-same? then ;
: eq-level@ ( addr i -- level ) lf-cref-pair@ drop ;
: eq-arity= ( s1 s2 -- flag ) lf-cref-pairs nip swap lf-cref-pairs nip = ;
: eq-names= ( s1 s2 -- flag ) lf-cref-name@ drop swap lf-cref-name@ drop eq-name= ;
: eq-level-of ( slot i -- level ) swap lf-cref-pairs drop swap eq-level@ ;
: eq-level-at ( s1 s2 k -- s1 s2 flag outcome )
  >r 2dup r@ eq-level-of swap r> eq-level-of swap lf-meta-level= ;
\ Each pair of universe arguments, in order, until one differs.
: eq-levels ( s1 s2 -- flag outcome )
  over lf-cref-pairs nip ['] eq-level-at ok-all? 2swap 2drop ;
: eq-const ( a b -- flag outcome )
  lf-const-slot swap lf-const-slot 2dup eq-arity= 0= if 2drop false outcome-ok exit then
  2dup eq-names= if eq-levels else 2drop false outcome-ok then ;
: eq-fields ( a b -- flag )
  over lf-term-first@ over lf-term-first@ = if lf-term-second@ swap lf-term-second@ =
  else 2drop false then ;
: eq-proj ( a b -- flag )
  over lf-term-second@ over lf-term-second@ =
  if lf-term-first@ swap lf-term-first@ eq-name=
  else 2drop false then ;
: eq-unshared? ( a -- flag ) lf-fvar-mvar-tags lf-term-in? ;
: eq-sorts ( a b -- flag outcome ) lf-term-first@ swap lf-term-first@ lf-meta-level= ;
\ A literal, a projection's leaf or any other leaf.
: eq-plain ( a b -- flag outcome )
  over lf-lit-leaf? if lf-lit-same? outcome-ok exit then
  over lf-str-leaf? if lf-str-same? outcome-ok exit then
  over lf-proj-leaf? if eq-proj else eq-fields then outcome-ok ;
: eq-leaf ( a b -- flag outcome )
  over eq-unshared? if 2drop false outcome-ok exit then
  over lf-tag-symbolic-sort lf-term-tag? if eq-sorts exit then
  over lf-term-const? if eq-const else eq-plain then ;

\ One pair: the same node, a binary node's parts pushed, or two leaves.
: eq-parts ( a b -- flag outcome )
  2dup lf-term-second@ swap lf-term-second@ eq-push dup ok? 0=
  if nip nip false swap exit then
  drop lf-term-first@ swap lf-term-first@ eq-push true swap ;
: eq-step ( a b -- flag outcome )
  2dup = if 2drop true outcome-ok exit then
  over lf-term-tag@ over lf-term-tag@ <> if 2drop false outcome-ok exit then
  over lf-term-binary? if eq-parts else eq-leaf then ;
: eq-run ( -- flag outcome ) eq-pairs ['] eq-step slab-2all? ;
: lf-meta-eqv ( a b -- flag outcome )
  2dup lf-term-pair-valid? 0= if 2drop false outcome-invalid exit then
  2dup = if 2drop true outcome-ok exit then
  eq-pairs slab-clear eq-push dup ok? if drop eq-run else false swap then ;
\ Expr.equal: equal terms as above that are different nodes and hold a
\ binder (whose names the binder table keeps) are not compared yet.
lf-tag-lam lf-tag-pi lf-tag-let lf-tag-let-nondep 4 lf-tags constant eq-named-tags
: eq-named? ( node -- flag ) lf-term-tag@ eq-named-tags lf-tag-in? ;
: eq-unnamed? ( t -- outcome )   \ ok: t holds no binder
  ['] eq-named? lf-term-holds-node? ok-then?
  if if outcome-unsupported else outcome-ok then then ;
: eq-both-unnamed ( a b -- flag outcome )
  eq-unnamed? dup ok? if drop eq-unnamed? else nip then true swap ;
: lf-meta-equal? ( a b -- flag outcome )
  2dup = if 2drop true outcome-ok exit then
  2dup lf-meta-eqv ok-then? 0= if nip nip false swap exit then
  if eq-both-unnamed else 2drop false outcome-ok then ;

\ A name against a dotted text (Lean's match_expr and isConstOf compare
\ names so; the anonymous name is 0 and the empty text).
: lf-meta-name? ( c-addr u name -- flag ) -rot lf-name-dotted? ;
\ A term that is the constant of that name (Lean's isConstOf).
: lf-meta-const-named? ( t c-addr u -- flag )
  rot dup lf-term-const? if lf-const-name lf-meta-name?
  else drop 2drop false then ;
: lf-meta-head ( t -- head ) lf-meta-head-args drop ;
\ The name of the constant at t's head (Lean's getAppFn.constName?).
: lf-meta-head-name ( t -- name true | false )
  lf-meta-head dup lf-term-const? if lf-const-name true else drop false then ;
\ Shapes: n arguments and a constant of the name at the head (Lean's
\ match_expr); argument i, the first 0, of t with n arguments.
: lf-meta-app-of? ( t n c-addr u -- flag )
  2>r over lf-meta-args# = if lf-meta-head 2r> lf-meta-const-named?
  else drop 2r> 2drop false then ;
: lf-meta-nth-arg ( t i n -- a ) swap lf-term-arg ;
: lf-meta-app-arg ( t i -- a ) over lf-meta-args# lf-meta-nth-arg ;
\ Nat.succ x (Lean's match_expr Nat.succ _): toNatLit?, isOffset,
\ evalNat and getFunInfo's shapes.
: lf-meta-succ? ( t -- flag ) 1 s" Nat.succ" lf-meta-app-of? ;
: lf-and-app? ( t -- flag ) 2 s" And" lf-meta-app-of? ;
: lf-iff-app? ( t -- flag ) 2 s" Iff" lf-meta-app-of? ;
: lf-not-app? ( t -- flag ) 1 s" Not" lf-meta-app-of? ;
: lf-meta-opt-auto? ( t -- flag )
  dup 2 s" optParam" lf-meta-app-of? swap 2 s" autoParam" lf-meta-app-of? or ;
: lf-meta-out-param? ( t -- flag )
  dup 1 s" outParam" lf-meta-app-of? swap 1 s" semiOutParam" lf-meta-app-of? or ;
: eq-unwrapped ( t -- t' more? )
  dup lf-meta-opt-auto? if lf-term-first@ lf-term-second@ true exit then
  dup lf-meta-out-param? if lf-term-second@ true else false then ;
: lf-meta-consume-annotations ( t -- t' ) begin eq-unwrapped 0= until ;


\ etaExpanded?: the lambdas taken off, then the body's arguments, from the
\ last, must be #0, #1, ... and what is left must have no loose variable.
: eq-lams ( e -- body n )
  0 swap begin dup lf-term-lam? while lf-term-second@ swap 1+ swap repeat swap ;
: eq-arg-i? ( body i -- flag )
  over lf-term-app? if swap lf-term-second@ swap lf-term-bvar-is? else 2drop false then ;
: eq-peel ( body n -- f flag )
  0 ?do dup i eq-arg-i? 0= if false unloop exit then lf-term-first@ loop true ;
: eq-closed ( e f -- f' flag outcome )
  dup lf-meta-loose ok-then? 0= if nip false swap exit then
  if drop false else nip true then outcome-ok ;
: lf-meta-eta-expanded ( e -- f flag outcome )
  dup eq-lams eq-peel if eq-closed else drop false outcome-ok then ;

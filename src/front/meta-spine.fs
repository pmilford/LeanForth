\ Application spines, constants' declarations and universe-argument lists
\ for the front end's Meta files (plan FE1c; front/whnf.fs, infer.fs,
\ beta-inst.fs), one copy of what each needed (Forth review of fe1c-2,
\ S2). Untrusted.
\ - lf-meta-app? ( term -- flag ): an application.
\ - lf-meta-spine ( term slab -- head outcome ): the arguments of
\   f a1 .. an into the slab, emptied first, an first; the head f. A
\   refused cell gives -1 and full.
\ - lf-meta-arg ( i slab -- term ): argument i, a0 the first, of a spine;
\   lf-meta-arg-at ( i slab -- addr ): its cell (a(i+1)'s the cell below).
\ - lf-meta-const-decl ( const -- d outcome ): the declaration of a
\   constant's name (Lean's find?), through front/meta-env.fs in either
\   mode: ok; invalid when no declaration has the name (an unknown
\   constant); full or unsupported, passed on, when a library
\   declaration could not be decoded (never read as an unknown constant,
\   plan S2); -1 for d when not ok.
\ - lf-meta-const-known ( const -- d true outcome | false outcome ): the
\   same with an unknown constant as false and ok (Lean's find? giving
\   none); every other failure passed on with false (review F8 of
\   2026-11-18: the one "unknown constant" test of whnf, defeq, infer,
\   fun-info).
\ - lf-meta-kind-or ( const kind -- kind' outcome ): the constant's
\   declaration kind (meta-env.fs's lf-menv-kind); kind itself for an
\   unknown constant, and with a failure's outcome.
\ - lf-meta-firm-const? ( const -- flag outcome ): neither a definition nor
\   an unknown constant, so whnf cannot unfold it (false with a failure's
\   outcome): infer's firm head and fun-info's final one.
\ - lf-meta-tags ( tag1 .. tagn n -- mask ): the set of n term tags as a
\   mask of core/terms.fs's lf-tag-bit (kept as a constant);
\   lf-meta-tag-of? ( tag mask -- flag ) and lf-meta-tag-in? ( term mask
\   -- flag ): a tag, a term's tag, in the set (review F3 of 2026-11-18:
\   one test in place of the OR chains of tag comparisons).
\ - lf-meta-under ( e tag -- e' true | e false ): a let's body (Lean's
\   letE passed with its body instantiated: core/let-terms.fs keeps it as
\   a binder) or, for a binder of the tag (lambda or pi), its body; e and
\   false for any other term (review F7 of 2026-11-18).
\ - lf-meta-levels-fill ( const slab -- outcome ): a constant's universe
\   arguments, as levels, into the slab, emptied first.
\ - lf-meta-arity? ( d const -- flag ): the constant has as many universe
\   arguments as the declaration d has universe parameters (the test of
\   Lean's deltaDefinition, inferConstant and reduceRec).
\ - lf-meta-named ( new old -- new outcome ): a rebuilt binder gets the
\   old one's name and kind (present/binder-table.fs), when it has them;
\   full when the table has no room for them (a rebuilt node that is an
\   input node keeps its record's: ok).
\ - lf-meta-mvar-free? ( term -- flag ): no metavariable in the term, as
\   far as the term store tells: a binary node's data word is known only
\   then (core/terms.fs), a leaf is no metavariable (Lean's !hasExprMVar;
\   a node whose word is unknown is taken to hold one).
\ - lf-meta-fvar-free? ( term -- flag ): the term's data word shows no
\   free variable (false when the store keeps no word for it);
\   lf-meta-has-fvar? ( term -- flag ): it certainly holds one (a free
\   variable leaf, or a data word that shows one).
\ - lf-meta-tag? ( term tag -- flag ): the term's tag is tag;
\   lf-meta-fvar? ( term -- flag ): a free variable.
\ - lf-meta-head-args ( term -- head n ): the head of its spine and the number
\   of its arguments (Lean's getAppFn and getAppNumArgs);
\   lf-meta-args# ( term -- n ): that number alone.
\ - lf-meta-forall-body ( term -- body ): what is under its leading pis
\   (the term itself when it is no pi), its loose bound variables those
\   binders' (Lean's getForallBody of each, unreduced).
\ - lf-meta-app ( f a -- f' outcome ): the application f a (Lean's
\   mkApp); full, with -1, when the term store has no room.
\ - lf-meta-apply-all ( f slab -- f' outcome ): f applied to a spine's
\   arguments, a0 first (Lean's mkAppN f args); full as above.
\   lf-meta-apply-from ( f n from slab -- f' outcome ): f applied to the
\   n arguments from from on (Lean's mkAppRange f from (from+n); none
\   when n <= 0).
\ Unchecked: the terms are live, the constant is one, the slab is a cell
\ slab, from .. from+n-1 within it. State: none of its own; every word takes
\ its slab. Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/slab.fs
require ../core/terms.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ./meta-env.fs
require ../core/local-context.fs
require ../core/mvar-leaves.fs
require ../present/binder-table.fs
require ../core/let-terms.fs

: lf-meta-app? ( term -- flag ) lf-term-tag@ lf-tag-app = ;
: ms-peel ( term slab -- f outcome )
  over lf-term-second@ swap slab-push swap lf-term-first@ swap ;
: lf-meta-spine ( term slab -- head outcome )
  dup slab-clear swap begin dup lf-meta-app? while
    over ms-peel ok-then? 0= if nip -1 swap exit then
  repeat nip outcome-ok ;
: lf-meta-arg-at ( i slab -- addr ) tuck slab-count 1- swap - swap slab-at ;
: lf-meta-arg ( i slab -- term ) lf-meta-arg-at @ ;
: lf-meta-const-decl ( const -- d outcome )
  lf-const-name lf-menv-find ;
: ms-unknown-ok ( outcome -- outcome' ) dup outcome-invalid = if drop outcome-ok then ;
: lf-meta-const-known ( const -- d true outcome | false outcome )
  lf-meta-const-decl dup ok? if true swap exit then nip ms-unknown-ok false swap ;
: lf-meta-kind-or ( const kind -- kind' outcome )
  swap lf-meta-const-known ok-then? 0= if exit then if nip lf-menv-kind then outcome-ok ;
: lf-meta-firm-const? ( const -- flag outcome )
  lf-kind-definition lf-meta-kind-or swap lf-kind-definition <> swap ;
: lf-meta-arity? ( d const -- flag ) lf-const-levels# swap lf-menv-params nip = ;
: ms-level ( slot i -- level ) swap lf-cref-pairs drop swap lf-cref-pair@ drop ;
: lf-meta-levels-fill ( const slab -- outcome )
  dup slab-clear swap lf-const-slot dup lf-cref-pairs nip 0 ?do
    2dup i ms-level swap slab-push dup ok? 0= if nip nip unloop exit then drop
  loop 2drop outcome-ok ;
: ms-full ( outcome -- outcome' ) outcome-full = if outcome-full else outcome-ok then ;
: lf-meta-named ( new old -- new outcome )
  lf-pres-binder@ if 2>r dup 2r> lf-pres-binder! ms-full else outcome-ok then ;
: ms-binary? ( term -- flag ) lf-term-tag@ lf-term-binary-tag? ;
: lf-meta-mvar-free? ( term -- flag )
  dup ms-binary? if lf-term-data@ dup if nip then exit then lf-term-tag@ lf-tag-mvar <> ;
: lf-meta-fvar-free? ( term -- flag ) lf-term-data@ if lf-data-fvar? 0= else false then ;
: lf-meta-has-fvar? ( term -- flag )
  dup ms-binary? if lf-term-data@ if lf-data-fvar? else false then exit then
  lf-term-tag@ lf-tag-fvar = ;
: lf-meta-tag? ( term tag -- flag ) swap lf-term-tag@ = ;
: lf-meta-tags ( tag1 .. tagn n -- mask ) 0 swap 0 ?do swap lf-tag-bit or loop ;
: lf-meta-tag-of? ( tag mask -- flag ) swap lf-tag-bit and 0<> ;
: lf-meta-tag-in? ( term mask -- flag ) swap lf-term-tag@ swap lf-meta-tag-of? ;
: lf-meta-under ( e tag -- e' true | e false )
  over lf-let? if drop lf-let-body true exit then
  over swap lf-meta-tag? if lf-term-second@ true else false then ;
: lf-meta-fvar? ( term -- flag ) lf-tag-fvar lf-meta-tag? ;
: lf-meta-head-args ( term -- head n )
  0 swap begin dup lf-meta-app? while lf-term-first@ swap 1+ swap repeat swap ;
: lf-meta-args# ( term -- n ) lf-meta-head-args nip ;
: lf-meta-forall-body ( term -- body )
  begin dup lf-term-pi? while lf-term-second@ repeat ;
: lf-meta-app ( f a -- f' outcome ) lf-term-app if outcome-ok else -1 outcome-full then ;
: ms-app-down ( f k addr -- f' outcome ) swap cells - @ lf-meta-app ;
: lf-meta-apply-from ( f n from slab -- f' outcome )
  lf-meta-arg-at ['] ms-app-down ok-fold ;
: lf-meta-apply-all ( f slab -- f' outcome )
  dup slab-count swap 0 swap lf-meta-apply-from ;

base !   \ the BASE this file was loaded with

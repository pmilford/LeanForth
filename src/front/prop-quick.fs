\ The quick proposition and proof tests of the front end (plan FE1c; ADR
\ 0021 D6), ports of Lean 4.35.0's isPropQuick, isProofQuick and their
\ helpers isArrowProp and isArrowProposition (Lean/Meta/InferType.lean)
\ and Level.isAlwaysZero: approximate tests that look only at the shape
\ of a term and the types of its head, answering LBool (term-eqv.fs).
\ - lf-meta-prop-quick ( e -- lbool outcome ): isPropQuick: a literal,
\   Sort or lambda is no proposition; a pi or let its body's answer; a
\   bound variable or projection undef; a constant, free variable or
\   metavariable, alone or at the head of n arguments (a lambda or let
\   at the head passes one argument or none to its body; a lambda with
\   none left is no proposition) asks isArrowProp of its type: past n
\   pis (and any lets), Sort u is a proposition when u, its
\   metavariables instantiated, is zero whatever its parameters are; a
\   pi or another Sort false; anything else undef.
\ - lf-meta-proof-quick ( e -- lbool outcome ): isProofQuick: a literal,
\   Sort or pi is no proof; a lambda or let its body's answer; a bound
\   variable or projection undef; a head as above asks
\   isArrowProposition of its type: past n pis (and any lets), a bound
\   variable naming one of them is a proof when that binder's type is
\   Prop (false for a Sort never zero, also under outParam; else undef);
\   any other end isPropQuick's answer.
\ - lf-meta-always-zero? ( level -- flag outcome ): Level.isAlwaysZero.
\ A constant's type is inferType's (infer.fs: its universe parameters
\ instantiated). Pending binder types and levels wait on heap stacks
\ (plan task 6.2.0). Outcomes: ok; invalid for an unknown constant or a
\ stale leaf; full when a store or the heap has no room. Untrusted.
\ State: the slabs pq-binders and pq-levels, in the checker context (ADR
\ 0009); one test at a time.

require ../lib/lib.fs
require ../core/terms.fs
require ../core/levels.fs
require ../core/let-terms.fs
require ../core/local-context.fs
require ../core/mvar-leaves.fs
require ../core/constant-references.fs
require ./mvars.fs
require ./level-simp.fs
require ./meta-spine.fs
require ./infer.fs
require ./term-eqv.fs

1 cells context-slab: pq-binders   \ isArrowProposition's binder types, outermost first
1 cells context-slab: pq-levels    \ isAlwaysZero's pending levels

\ ---- isAlwaysZero: every level reached through both sides of a max and
\ the second of an imax is zero.
: pq-lpush ( level -- outcome ) pq-levels slab-push ;
: pq-lsides ( level -- outcome )
  dup lf-level-first@ pq-lpush dup ok? 0=
  if nip exit then drop lf-level-second@ pq-lpush ;
: pq-lstep ( level -- zero? outcome )
  dup lf-level-tag@ case lf-level-tag-zero of drop true outcome-ok endof
    lf-level-tag-max of pq-lsides true swap endof
    lf-level-tag-imax of lf-level-second@ pq-lpush true swap endof
    >r drop false outcome-ok r> endcase ;
: lf-meta-always-zero? ( level -- flag outcome )
  pq-levels slab-clear pq-lpush dup ok? if drop pq-levels ['] pq-lstep slab-all?
  else false swap then ;

\ ---- The type of a head: a constant's (inferConstType), a free
\ variable's or a metavariable's.
: pq-head? ( t -- flag )
  lf-term-tag@ dup lf-tag-constant = over lf-tag-fvar = or swap lf-tag-mvar = or ;
: pq-type ( head -- type outcome )
  dup lf-term-tag@ case lf-tag-constant of lf-infer endof
    lf-tag-fvar of lf-fvar-type outcome-ok endof
    lf-tag-mvar of lf-mvar-type if outcome-ok else -1 outcome-invalid then endof
    >r drop -1 outcome-invalid r> endcase ;
: pq-undef ( x outcome -- lbool outcome ) nip lf-lb-undef swap ;

\ ---- isArrowProp ( type n ): n pis (lets passed), then a Sort.
: pq-sort-zero ( sort -- lbool outcome )
  lf-term-first@ lf-level-instantiate-mvars ok-then? 0= if lf-lb-undef swap exit then
  lf-meta-always-zero? ok-then? if lf-lb outcome-ok else lf-lb-undef swap then ;
: pq-arrow-next ( type n -- type' n' flag )
  over lf-let? if swap lf-let-body swap true exit then
  over lf-term-pi? over 0> and if 1- swap lf-term-second@ swap true else false then ;
: pq-arrow-end ( type n -- lbool outcome )
  if drop lf-lb-undef outcome-ok exit then
  dup lf-tag-symbolic-sort lf-term-tag? if pq-sort-zero exit then
  lf-term-pi? if lf-lb-false else lf-lb-undef then outcome-ok ;
: pq-arrow-prop ( type n -- lbool outcome ) begin pq-arrow-next 0= until pq-arrow-end ;
: pq-head-arrow ( head n -- lbool outcome )
  swap pq-type ok-then? if swap pq-arrow-prop else pq-undef then ;

\ ---- The head of f a1 .. an: an application passes to its function, a
\ let to its body, a lambda with an argument left to its body.
: pq-app-next ( f n -- f' n' flag )
  over lf-term-app? if 1+ swap lf-term-first@ swap true exit then
  over lf-let? if swap lf-let-body swap true exit then
  over lf-term-lam? over 0> and if 1- swap lf-term-second@ swap true else false then ;
: pq-app-head ( e -- f n ) lf-term-first@ 1 begin pq-app-next 0= until ;

\ ---- isPropQuick.
: pq-prop-app ( e -- lbool outcome )
  pq-app-head over pq-head? if pq-head-arrow exit then
  drop lf-term-lam? if lf-lb-false else lf-lb-undef then outcome-ok ;
: pq-no-prop? ( e -- flag )
  lf-term-tag@ dup lf-tag-lit = over lf-tag-sort = or over lf-tag-symbolic-sort = or
  swap lf-tag-lam = or ;
: pq-prop-leaf ( e -- lbool outcome )
  dup pq-head? if 0 pq-head-arrow exit then
  pq-no-prop? if lf-lb-false else lf-lb-undef then outcome-ok ;
: pq-into ( e -- e' flag )
  dup lf-let? if lf-let-body true exit then dup lf-term-pi? if lf-term-second@ true
  else false then ;
: lf-meta-prop-quick ( e -- lbool outcome )
  begin pq-into 0= until dup lf-term-app? if pq-prop-app else pq-prop-leaf then ;

\ ---- isArrowProposition: its result an LBool or a bound variable k, as
\ pq-bvar + k; each binder passed on the way back turns #0 into its
\ type's checkProp and #k+1 into #k.
3 constant pq-bvar
: pq-zero? ( level -- flag ) lf-level-tag@ lf-level-tag-zero = ;
: pq-sort-prop ( sort -- r outcome )
  lf-term-first@ dup lf-meta-never-zero? ok-then? 0= if nip lf-lb-undef swap exit then
  if drop lf-lb-false else pq-zero? if lf-lb-true else lf-lb-undef then then outcome-ok ;
: pq-check-prop ( type -- r outcome )
  begin dup 1 s" outParam" lf-meta-app-of? while lf-term-second@ repeat
  dup lf-tag-symbolic-sort lf-term-tag?
  if pq-sort-prop else drop lf-lb-undef outcome-ok then ;
: pq-process ( r type -- r' outcome )
  over pq-bvar = if nip pq-check-prop exit then
  drop dup pq-bvar > if 1- then outcome-ok ;
: pq-binder ( type n -- type' n' flag outcome )
  over lf-let? if
  over lf-let-type pq-binders slab-push >r swap lf-let-body swap true r> exit then
  over lf-term-pi? over 0> and 0= if false outcome-ok exit then
  over lf-term-first@ pq-binders slab-push >r 1- swap lf-term-second@ swap true r> ;
: pq-binders-in ( type n -- type' n' outcome )
  pq-binders slab-clear begin pq-binder ok-then? 0= if nip nip -1 0 rot exit then
  0= until outcome-ok ;
: pq-prop-end ( type n -- r outcome )
  if drop lf-lb-undef outcome-ok exit then
  dup lf-term-bvar? if lf-term-first@ pq-bvar + outcome-ok
  else lf-meta-prop-quick then ;
: pq-back ( r -- r' outcome )
  begin pq-binders slab-count 0> while pq-binders slab-pop pq-process
    dup ok? 0= if exit then drop repeat outcome-ok ;
: pq-lbool ( r -- lbool ) dup pq-bvar < 0= if drop lf-lb-undef then ;
: pq-arrow-proposition ( type n -- lbool outcome )
  pq-binders-in ok-then? 0= if pq-undef exit then
  pq-prop-end dup ok? if drop pq-back then dup ok? if drop pq-lbool outcome-ok
  else pq-undef then ;
: pq-proof-arrow ( head n -- lbool outcome )
  swap pq-type ok-then? if swap pq-arrow-proposition else pq-undef then ;

\ ---- isProofQuick: lambdas and lets passed to their bodies; an
\ application's head as above, where a lambda with no argument left goes
\ on as isProofQuick of its body.
: pq-no-proof? ( e -- flag )
  lf-term-tag@ dup lf-tag-lit = over lf-tag-sort = or over lf-tag-symbolic-sort = or
  swap lf-tag-pi = or ;
: pq-proof-leaf ( e -- lbool outcome )
  dup pq-head? if 0 pq-proof-arrow exit then
  pq-no-proof? if lf-lb-false else lf-lb-undef then outcome-ok ;
: pq-proof-app ( e -- e' true | lbool outcome false )
  pq-app-head over pq-head? if pq-proof-arrow false exit then
  over lf-term-lam? if drop lf-term-second@ true exit then
  2drop lf-lb-undef outcome-ok false ;
: pq-proof-round ( e -- e' true | lbool outcome false )
  dup lf-term-lam? over lf-let? or if dup lf-let? if lf-let-body
  else lf-term-second@ then true exit then
  dup lf-term-app? if pq-proof-app else pq-proof-leaf false then ;
: lf-meta-proof-quick ( e -- lbool outcome ) begin pq-proof-round 0= until ;

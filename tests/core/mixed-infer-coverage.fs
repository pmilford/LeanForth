\ Coverage of lf-mixed-infer, lf-mixed-compare and lf-mixed-convert cases
\ that only the retired legacy tests exercised (gap list T1 and T5.3-T5.4 of
\ the legacy coverage map). Public words only; candidate signatures are
\ assumptions and no result is a checked theorem. Expected behaviour that is
\ more conservative than Lean (unknown) is marked as such.
include ../support/tester.fs
include ../support/checks.fs
require ../../src/main.fs
include ../support/plain-terms.fs
include ../support/plain-cases.fs

: infer ( root -- type identity status ) >r empty-token r> handle 50000 lf-mixed-infer ;
: inferred ( root -- type ) infer ok? must drop ;
: status-of ( root -- status ) infer nip nip ;
\ The level of a Sort node; fails unless the node is a Sort.
: sort-level ( node -- level ) lf-term-read must rot lf-tag-symbolic-sort = must drop ;
: universe ( root -- level ) inferred sort-level ;
: nat-of ( level -- n ) 50000 lf-level-value-assigned ok? must ;
: level= ( left right -- flag ) 10000 lf-level-compare ok? ;
: succ-of ( level -- level' ) lf-level-succ must ;
: convert-terms ( left right -- status ) >r handle r> handle 10000 lf-mixed-convert ;
: compare-terms ( left right -- status ) >r handle r> handle 10000 lf-mixed-compare ;
: counts ( -- terms levels crefs ) lf-term-count @ lf-level-count @ lf-cref-count @ ;
variable saved-terms variable saved-levels variable saved-crefs
: save-counts ( -- ) counts saved-crefs ! saved-levels ! saved-terms ! ;
: counts-kept? ( -- flag )
  counts saved-crefs @ = swap saved-levels @ = and swap saved-terms @ = and ;

\ T1.1 Inferred universes of Sort and Pi, including the impredicative case,
\ whose Sort is the zero level itself (no imax node).
fresh-session
T{ level-u make-sort universe level-u succ-of level= -> true }T
T{ level-u make-sort dup make-pi universe level-u succ-of dup lf-level-imax must level=
  -> true }T
T{ level-u make-sort 0 make-var make-pi universe
  level-u succ-of level-u lf-level-imax must
  level= -> true }T
T{ 1 make-sort 0 make-var make-pi universe nat-of -> 2 }T
T{ 0 make-sort 0 make-var make-pi universe -> 0 }T

\ T1.2 Heads that are not constants: a lambda head, and the composition
\ fixture, whose applications have bound-variable heads; its value has the
\ type of its claim (node 10).
fresh-session
T{ 1 make-sort 0 make-var make-lam 0 make-sort make-app universe nat-of -> 1 }T
T{ build-composition inferred 10 convert-terms -> outcome-ok }T
\ A binder domain that is a redex whose type is a Sort is accepted. So,
\ since plan task 4.2.2c, is a domain whose type is itself an unreduced
\ redex: its type is put in whnf, as Lean's ensure_sort_core does (until
\ then this was unknown, a known gap of tests/core/lean-differential.py).
: beta-prop ( -- node ) 1 make-sort 0 make-var make-lam 0 make-sort make-app ;
fresh-session
T{ beta-prop 0 make-sort make-pi universe nat-of -> 1 }T
T{ beta-prop 0 make-var 0 make-var make-lam make-lam status-of -> outcome-ok }T
\ A fuel sweep over fun A : Sort 1 => (fun B : Sort 1 => B) A in one session,
\ retrying after each exhaustion without a reset: every failure keeps the
\ counts, and the call finally succeeds with type Pi (A : Sort 1), Sort 1.
variable sweep-root variable sweep-result
: sweep-term ( -- node )
  1 make-sort 1 make-sort 0 make-var make-lam 0 make-var make-app make-lam ;
: sweep ( -- flag )
  fresh-session sweep-term sweep-root ! save-counts
  2000 0 do
    empty-token sweep-root @ handle i lf-mixed-infer
    dup outcome-exhausted = if
      drop 2drop counts-kept? 0= if false unloop exit then
    else
      ok? 0= if 2drop false unloop exit then drop sweep-result ! true unloop exit
    then
  loop false ;
T{ sweep -> true }T
T{ sweep-result @ 1 make-sort 1 make-sort make-pi convert-terms -> outcome-ok }T

\ T1.3 Capacity. A full term store, room for two nodes (the composition
\ then fails after it has allocated), a full level store and a corrupted
\ term count: each fails (full for the three capacity limits, invalid for
\ the corrupted count), keeps all counts and leaves an earlier result
\ readable. A rolled-back identity is not revived by reusing its slot.
: fill-terms ( room -- )
  lf-term-capacity swap - begin dup lf-term-count @ > while 0 make-var drop repeat drop ;
: fill-levels ( -- )
  begin lf-level-count @ lf-level-capacity < while 0 succ-of drop repeat ;
variable earlier variable earlier-id variable token variable before-serial
: keep-earlier ( -- ) 0 make-sort inferred handle earlier-id ! earlier ! ;
: earlier-ok? ( -- flag ) earlier @ earlier-id @ 1000 lf-cterm-check ok? ;
: crowded ( room -- root ) >r build-composition keep-earlier r> fill-terms ;
T{ 0 crowded save-counts status-of counts-kept? earlier-ok?
  -> outcome-full true true }T
2 crowded sweep-root ! save-counts lf-term-serial @ before-serial !
T{ sweep-root @ status-of counts-kept? earlier-ok? -> outcome-full true true }T
T{ lf-term-serial @ before-serial @ > -> true }T
0 make-var drop
T{ saved-terms @ before-serial @ 1+ lf-hterm-valid? -> false }T
T{ fresh-session keep-earlier 0 make-sort fill-levels save-counts status-of counts-kept?
  earlier-ok? -> outcome-full true true }T
\ Room for one more level only: Pi (A : Sort u), A takes it for the
\ domain's type (succ u), and its universe imax (succ u) u is then full.
: fill-levels-but-one ( -- )
  begin lf-level-count @ lf-level-capacity 1- < while 0 succ-of drop repeat ;
T{ fresh-session keep-earlier level-u make-sort 0 make-var make-pi fill-levels-but-one
  save-counts status-of counts-kept? earlier-ok? -> outcome-full true true }T
fresh-session keep-earlier 0 make-sort handle sweep-result ! sweep-root !
empty-token token !
lf-term-count @ saved-terms ! -1 lf-term-count !
T{ token @ sweep-root @ sweep-result @ 50000 lf-mixed-infer -> -1 0 outcome-invalid }T
saved-terms @ lf-term-count !
T{ earlier-ok? -> true }T
\ The definition probe in a full term store: full, counts kept.
: probe ( claim value -- status )
  >r handle empty-token -rot r> handle 50000 lf-mixed-definition-probe ;
T{ fresh-session 1 make-sort 0 make-sort 0 fill-terms save-counts probe counts-kept?
  -> outcome-full true }T

\ T1.4 Constants through candidate signatures (assumptions). c has formals
\ u, v and type Pi (_ : Sort u), Sort v; k has none and type Sort 0.
create formals 2 cells allot
create args 4 cells allot
: intern ( addr len -- name ) 0 -rot lf-name-str must ;
: arg! ( level position -- )
  2* cells args + >r dup r@ ! lf-level-identity must r> cell+ ! ;
: reference ( addr len count -- node )
  >r intern lf-name-generation @ args r> lf-cref-new must lf-cterm-new must drop ;
: put ( token addr len root count -- )
  >r >r intern r> handle formals r> 50000 lf-msp-put ok? must ;
: signatures ( -- token )
  fresh-session u-name formals ! v-name formals cell+ !
  empty-token dup s" c" level-u make-sort level-v make-sort make-pi 2 put
  dup s" k" 0 make-sort 0 put ;
: infer-with ( token root -- type identity status ) handle 50000 lf-mixed-infer ;
: inferred-with ( token root -- type ) infer-with ok? must drop ;
\ Arity 0, and arity 2 with the arguments in both orders.
T{ signatures s" k" 0 reference inferred-with sort-level nat-of -> 0 }T
T{ signatures 0 0 arg! 1 1 arg! s" c" 2 reference inferred-with
  0 make-sort 1 make-sort make-pi convert-terms -> outcome-ok }T
T{ signatures 1 0 arg! 0 1 arg! s" c" 2 reference inferred-with
  1 make-sort 0 make-sort make-pi convert-terms -> outcome-ok }T
\ Too few arguments, or none, is invalid rather than unknown, with nothing
\ kept; a name without a signature is unknown only with a live level.
T{ signatures 0 0 arg! s" c" 1 reference save-counts infer-with nip nip counts-kept?
  -> outcome-invalid true }T
T{ signatures s" c" 0 reference infer-with nip nip -> outcome-invalid }T
T{ signatures 0 0 arg! s" missing" 1 reference infer-with nip nip -> outcome-unknown }T
: stale-level-reference ( -- token root )
  signatures level-u succ-of 0 arg! s" missing" 1 reference
  lf-level-count @ 1- lf-level-count ! 0 succ-of drop ;
T{ stale-level-reference infer-with nip nip -> outcome-invalid }T
\ A parameter outside the session's level context is invalid as well.
T{ signatures 99 lf-level-param must 0 arg! s" missing" 1 reference infer-with nip nip
  -> outcome-invalid }T

\ T1.5 Application shapes with id : Pi (A : Sort u), A -> A (assumed).
: id-signature ( -- token )
  fresh-session u-name formals ! empty-token dup s" id"
  level-u make-sort 0 make-var 1 make-var make-pi make-pi 1 put ;
: id-at ( level -- node ) 0 arg! s" id" 1 reference ;
\ id.{1} Prop : Prop -> Prop (a partial application as the result).
T{ id-signature 1 id-at 0 make-sort make-app inferred-with
  0 make-sort 0 make-sort make-pi convert-terms -> outcome-ok }T
\ id.{1} Prop (forall P : Prop, P -> P) : Prop.
: prop-target ( -- node ) 0 make-sort 0 make-var 1 make-var make-pi make-pi ;
T{ id-signature 1 id-at 0 make-sort make-app prop-target make-app inferred-with
  sort-level nat-of -> 0 }T
\ fun A : Sort u => fun x : A => id.{u} A : Pi A, A -> A -> A, under binders.
T{ id-signature level-u id-at 1 make-var make-app 0 make-var swap make-lam
  level-u make-sort swap make-lam inferred-with
  level-u make-sort 0 make-var 1 make-var 2 make-var make-pi make-pi make-pi convert-terms
  -> outcome-ok }T
\ second : Pi (A : Sort 1) (B : Sort 1), B -> B; the result type depends on
\ the second argument: second Prop (Prop -> Prop) : (Prop -> Prop) -> Prop -> Prop.
: second-signature ( -- token )
  fresh-session empty-token dup s" second"
  1 make-sort 1 make-sort 0 make-var 1 make-var make-pi make-pi make-pi 0 put ;
: prop-arrow ( -- node ) 0 make-sort 0 make-sort make-pi ;
T{ second-signature s" second" 0 reference 0 make-sort make-app prop-arrow make-app
  inferred-with prop-arrow prop-arrow make-pi convert-terms -> outcome-ok }T

\ T1.6 A binder domain that is a proof rather than a type is rejected (rule
\ S2 of ADR 0011: its type A is a variable, rigid and not a Sort; Lean's
\ typeExpected); a variable two binders up is the right one
\ (open-context-oracle.lean's Valid) and the wrong binder is rejected
\ (Wrong: D3 under D4, Lean's declTypeMismatch).
fresh-session
T{ 0 make-sort 0 make-var 0 make-var 0 make-var make-lam make-lam make-lam status-of
  -> outcome-rejected }T
: context-claim ( -- node )
  1 make-sort 0 make-var 1 make-sort 0 make-var 3 make-var
  make-pi make-pi make-pi make-pi ;
: context-value ( result -- node )
  >r 1 make-sort 0 make-var 1 make-sort 0 make-var r> make-var make-lam make-lam
  make-lam make-lam ;
fresh-session
T{ context-claim 2 context-value probe -> outcome-ok }T
T{ context-claim 0 context-value probe -> outcome-rejected }T

\ T5.3 lf-mixed-compare is syntactic: different Sort levels and a redex
\ against its reduct are unknown, never equal.
fresh-session
T{ 0 make-sort 1 make-sort compare-terms -> outcome-unknown }T
T{ 0 make-sort 0 make-var make-lam 0 make-sort make-app 0 make-sort compare-terms
  -> outcome-unknown }T
\ T5.1 for compare: a failed audit (stale handle) or negative fuel leaves
\ zero fuel.
T{ 0 make-sort handle 1+ 0 make-sort handle 100 lf-mixed-compare lf-mcompare-fuel @
  -> outcome-invalid 0 }T
T{ 0 make-sort handle 0 make-sort handle -1 lf-mixed-compare lf-mcompare-fuel @
  -> outcome-invalid 0 }T

\ T5.4 lf-mixed-convert on symbolic Sorts, with counts kept, and a fuel
\ sweep that gives only equal or exhausted. Since plan task 4.2.2d Lean's
\ no is rejected: two Sorts of inequivalent levels, and a Sort against a
\ bound variable; a bound variable on the left is unknown (a bare
\ conversion has no typer to tell whether it is a proof, step 4), and so
\ is a lambda against a Sort. A Sort against a lambda is Lean's no (plan
\ task 4.2.4): a Sort is no proof, and its type, a Sort, no Pi to eta-
\ expand it with (step 11).
fresh-session
: sort-pair ( left right -- l r ) >r make-sort r> make-sort ;
T{ level-u level-u 0 lf-level-max must sort-pair save-counts convert-terms counts-kept?
  -> outcome-ok true }T
T{ level-u 0 lf-level-imax must 0 sort-pair convert-terms -> outcome-ok }T
T{ level-u level-v sort-pair save-counts convert-terms counts-kept?
  -> outcome-rejected true }T
variable convert-left variable convert-right
: convert-sweep ( -- flag )
  level-u level-u 0 lf-level-max must sort-pair convert-right ! convert-left !
  200 0 do
    convert-left @ handle convert-right @ handle i lf-mixed-convert
    dup outcome-exhausted = if drop else
      outcome-ok = unloop exit then
  loop false ;
T{ convert-sweep -> true }T
fresh-session
T{ 0 make-sort 0 make-var convert-terms -> outcome-rejected }T
T{ 0 make-var 0 make-sort convert-terms -> outcome-unknown }T
T{ 0 make-sort 0 make-sort 0 make-var make-lam convert-terms -> outcome-rejected }T
T{ 0 make-sort 0 make-var make-lam 0 make-sort convert-terms -> outcome-unknown }T

\ T1.3 (last, because a spent serial poisons the level store): when the
\ level serial is spent, inferring Sort 0 is full and keeps the counts.
fresh-session keep-earlier 0 make-sort sweep-root ! save-counts
lf-level-serial @ max-n lf-level-serial !
T{ sweep-root @ status-of counts-kept? earlier-ok? -> outcome-full true true }T
lf-level-serial !
bye

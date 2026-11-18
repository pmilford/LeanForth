\ Unit tests of the front end's type inference (plan FE1c;
\ src/front/infer.fs) over the Init slice, with the variables of
\ tests/front/whnf-cases.fs: constants with their universe arguments, free
\ variables, let variables, metavariables, sorts and applications, each
\ with its type; every outcome -- unsupported (lambda, pi, let and
\ projection terms and heads, a lambda argument, a type whnf would have to
\ unfold), invalid (no term, a loose bound variable, an unknown or
\ stale leaf, a wrong number of levels, a function expected), full (a
\ refused allocation), exhausted (whnfCore's fuel). Every T{ }T checks the
\ data stack's depth. tests/front/check_whnf.py compares the types with
\ pinned Lean's.
include ../support/tester.fs
include ../support/heap-watch.fs
require ./whnf-cases.fs

: leaf= ( t1 t2 -- flag )
  over lf-term-first@ over lf-term-first@ = >r lf-term-second@ swap lf-term-second@ = r> and ;
: same? ( t1 t2 -- flag )
  2dup = if 2drop true exit then
  over lf-term-tag@ over lf-term-tag@ <> if 2drop false exit then
  over lf-term-tag@ lf-term-binary-tag? 0= if leaf= exit then
  over lf-term-first@ over lf-term-first@ recurse 0= if 2drop false exit then
  lf-term-second@ swap lf-term-second@ recurse ;
: infer= ( term expected -- flag outcome ) >r lf-infer r> swap >r same? r> ;
: add ( -- t ) 0 s" Nat.add" cn ;
: pair ( a b -- t ) >r >r l0 l0 2 s" Prod.mk" cn nat app nat app r> app r> app ;
nat nat lf-term-pi must constant nat>nat

\ ---- Full: the first call's first allocation refused; then it works.
T{ 1 heap-refusals ! add fk app fk app lf-infer heap-refusals @ -> -1 outcome-full 0 }T
T{ add fk app fk app nat infer= -> true outcome-ok }T

\ ---- Leaves and applications.
T{ add nat nat nat lf-term-pi must lf-term-pi must infer= -> true outcome-ok }T
T{ add fk app nat nat lf-term-pi must infer= -> true outcome-ok }T
T{ fk nat infer= ?n nat infer= fg nat infer= -> true outcome-ok true outcome-ok true outcome-ok }T
T{ rec fm app fz app fs app fk app fm fk app infer= -> true outcome-ok }T
T{ succ fk app nat infer= -> true outcome-ok }T
T{ nat lv1 sort infer= -> true outcome-ok }T
T{ l0 sort lv1 sort infer= -> true outcome-ok }T

nat nat>nat lf-lctx-let made constant ftype
nat mv-natural lf-mvar-new made constant ?t
0 ?t ftype lf-mvar-assign made drop
nat ?t lf-lctx-local made constant fh

\ ---- Lambdas: the body's type closed over the binders.
T{ nat 0 bv lam nat>nat infer= -> true outcome-ok }T
T{ nat nat 1 bv lam lam nat nat>nat lf-term-pi must infer= -> true outcome-ok }T
: eq-refl ( a -- t ) >r lv1 1 s" Eq.refl" cn nat app r> app ;
: eq ( a b -- t ) >r >r lv1 1 s" Eq" cn nat app r> app r> app ;
T{ nat 0 bv eq-refl lam  nat 0 bv 0 bv eq lf-term-pi must infer= -> true outcome-ok }T
T{ nat ?n lam nat>nat infer= -> true outcome-ok }T
\ A later binder's domain over an earlier one: fun a (h : a = a) => h.
T{ nat 0 bv 0 bv eq 0 bv lam lam
   nat 0 bv 0 bv eq 1 bv 1 bv eq lf-term-pi must lf-term-pi must infer= -> true outcome-ok }T
\ A lambda's type with a metavariable, a body of no inferable kind, a
\ body that is no function applied: unsupported, unsupported, invalid.
T{ nat fh lam lf-infer nat nat fk 0 bv let lam lf-infer
   -> -1 outcome-unsupported -1 outcome-unsupported }T
T{ nat fs 0 bv app lam lf-infer -> -1 outcome-invalid }T

\ A constant whose universe arguments differ: each parameter gets its own
\ (Quot.lift.{1,2}: alpha : Sort 1, beta : Sort 2).
: qlift-type ( -- type ) lv1 lv2 2 s" Quot.lift" cn lf-infer drop ;
T{ qlift-type lf-term-first@ lv1 sort same? -> true }T
T{ qlift-type lf-term-second@ lf-term-second@ lf-term-first@ lv2 sort same? -> true }T

\ ---- Unsupported.
\ Pis: Sort of imax of the domains' levels and the body's, normalized.
T{ nat>nat lv1 sort infer= nat 0 bv 0 bv eq lf-term-pi must l0 sort infer=
   -> true outcome-ok true outcome-ok }T
T{ l0 sort l0 sort lf-term-pi must lv1 sort infer= -> true outcome-ok }T
T{ lv1 sort nat lf-term-pi must lv1 lf-level-succ drop sort infer= -> true outcome-ok }T
\ A domain whose type is no sort (Lean: type expected); a domain that is
\ itself a pi (its level needs a nested telescope: unsupported).
T{ fk fk lf-term-pi must lf-infer -> -1 outcome-invalid }T
T{ nat>nat nat lf-term-pi must lf-infer -> -1 outcome-unsupported }T
\ A domain whose type of type is a metavariable (Lean would assign it
\ Sort ?u), a definition alone or an application whnf would unfold.
nat mv-natural lf-mvar-new made constant ?x
?x lf-lctx-local made constant fdom
lv1 1 s" outParam" cn lf-lctx-local made constant fo
\ (outParam.{1} alone: getLevel's whnfD unfolds it to a lambda, no sort:
\ invalid, Lean's "type expected"; branch s2-tactics.)
T{ fdom nat lf-term-pi must lf-infer fo nat lf-term-pi must lf-infer
   -> -1 outcome-unsupported -1 outcome-invalid }T
T{ nat fk 0 bv let lf-infer -> -1 outcome-unsupported }T
T{ nat 0 bv lam fk app lf-infer -> -1 outcome-unsupported }T
\ A lambda argument put in for a bound variable at an application's head
\ is applied by a beta step: Nat.rec's type `motive t` with a lambda
\ motive; under a binder of the type the argument is that binder's loose
\ variable, put in as it is (Lean's instantiateBetaRevRange: (t : Nat) ->
\ Nat); where the motive's own binders would need it lifted, unsupported.
T{ rec nat nat lam app fz app fs app fk app nat infer= -> true outcome-ok }T
T{ rec nat 0 bv 0 bv eq lam app fz app fs app fk app fk fk eq infer= -> true outcome-ok }T
T{ rec nat nat lam app fz app fs app nat>nat infer= -> true outcome-ok }T
T{ rec nat nat 1 bv 0 bv eq tpi lam app fz app fs app lf-infer -> -1 outcome-unsupported }T
\ A whnf point inside the spine (inferAppType's j): `motive k` is no pi
\ until beta makes it one, and the argument after it is put in last.
T{ rec nat nat 0 bv 0 bv eq tpi lam app fz app fs app fk app fa app fa fa eq infer=
   -> true outcome-ok }T
\ The type is no pi and whnfD unfolds it, as Lean's inferAppType does:
\ fq : outParam (Nat -> Nat), fq k : Nat (branch s2-tactics).
lv1 1 s" outParam" cn nat>nat app lf-lctx-local made constant fq
T{ fq fk app nat infer= -> true outcome-ok }T
T{ 0 lf-term-sort must lf-infer -> -1 outcome-unsupported }T

\ ---- Invalid: no term, a loose bound variable, a wrong number of
\ levels, a function expected (a type with a constant, a free variable
\ or a sort at the head that no whnf makes a pi).
T{ -1 lf-infer 0 bv lf-infer -> -1 outcome-invalid -1 outcome-invalid }T
T{ lv1 1 s" Nat.add" cn lf-infer 0 s" Nat.rec" cn lf-infer -> -1 outcome-invalid -1 outcome-invalid }T
T{ fs fk app lf-infer nat fk app lf-infer -> -1 outcome-invalid -1 outcome-invalid }T
T{ fm fk app lf-infer -> -1 outcome-invalid }T
\ A function whose type is a lambda: whnf leaves it, so no function
\ either (Lean: function expected; review fe1c-2 L2).
nat 0 bv lam lf-lctx-local made constant fl
T{ fl fk app lf-infer -> -1 outcome-invalid }T
\ A type with an inductive type's application at the head (Nat Nat:
\ ill-typed, but inference does not check) is no function either; a
\ constant no declaration has is invalid (Lean: unknown constant).
nat nat app lf-lctx-local made constant fw
T{ fw fk app lf-infer -> -1 outcome-invalid }T
: unknown ( -- t ) 0 s" motive" menv-part lf-name-generation @ lv-pairs 0 lf-cref-new must
  lf-cterm-new must drop ;
T{ unknown lf-infer unknown fk app lf-infer -> -1 outcome-invalid -1 outcome-invalid }T
\ A type that is a definition alone: whnfD unfolds it to a lambda, no pi:
\ invalid, Lean's "function expected" (branch s2-tactics).
lv1 1 s" outParam" cn lf-lctx-local made constant ft
T{ ft fk app lf-infer -> -1 outcome-invalid }T
T{ 0 bv fk app lf-infer -> -1 outcome-invalid }T

\ ---- Projections (inferProjType; S2 merge B). check_whnf.py compares
\ the accepted cases with pinned Lean's; here every other outcome.
: fin-mk ( -- t ) 0 s" Fin.mk" cn fk app fa app fb app ;
: add-nat ( -- t ) 0 s" instAddNat" cn ;
T{ fa fb pair 0 proj nat infer= fa fb pair 1 proj nat infer= -> true outcome-ok true outcome-ok }T
T{ fp 0 proj nat infer= add-nat 0 s" Add" projn fk app fx app nat infer=
   -> true outcome-ok true outcome-ok }T
\ The field after val names it as fin-mk.0 (Lean's mkProj).
: lt ( a b -- t ) >r >r l0 1 s" LT.lt" cn nat app 0 s" instLTNat" cn app r> app r> app ;
T{ fin-mk 1 s" Fin" projn fin-mk 0 s" Fin" projn fk lt infer= -> true outcome-ok }T
\ The structure's type is whnf'd first: outParam (Prod Nat Nat).
lv1 1 s" outParam" cn l0 l0 2 s" Prod" cn nat app nat app app char r local constant fop
T{ fop 1 proj nat infer= -> true outcome-ok }T
\ Invalid ("invalid projection"): a structure of another name, a type
\ that is no structure (two constructors, Or's first with a field; no
\ constant at the head), a field index past the constructor's fields,
\ an unknown constant.
T{ fp 0 s" Fin" projn lf-infer fk 0 proj lf-infer -> -1 outcome-invalid -1 outcome-invalid }T
0 s" True" cn constant tru
0 s" Or" cn tru app tru app char o local constant f-or
T{ f-or 0 s" Or" projn lf-infer -> -1 outcome-invalid }T
lv1 1 s" List" cn nat app char l local constant fls
T{ fls 0 s" List" projn lf-infer fl 0 proj lf-infer -> -1 outcome-invalid -1 outcome-invalid }T
T{ fp 2 proj lf-infer unknown 0 proj lf-infer -> -1 outcome-invalid -1 outcome-invalid }T
\ Unsupported: a structure with an index (Eq's one constructor), a
\ projection of a projection, of a let, of a lambda applied.
lv1 1 s" Eq" cn nat app fk app fk app char e local constant feq
T{ feq 0 s" Eq" projn lf-infer fp 0 proj 0 proj lf-infer
   -> -1 outcome-unsupported -1 outcome-unsupported }T
T{ nat fp 0 bv let 0 proj lf-infer nat fp lam fk app 0 proj lf-infer
   -> -1 outcome-unsupported -1 outcome-unsupported }T
\ Invalid answers of the steps: an ill-typed structure (Nat Nat) has no
\ type; a free variable of no structure type at all.
T{ nat nat app 0 proj lf-infer fs 0 proj lf-infer -> -1 outcome-invalid -1 outcome-invalid }T
\ Full: each allocation refused in turn gives full, never another answer.
: proj-at ( k -- outcome )
  fin-mk 1 s" Fin" projn swap heap-refusals ! lf-infer nip 0 heap-refusals ! ;
: ok-or-full? ( outcome -- flag ) dup ok? swap outcome-full = or ;
: proj-sweep ( -- flag ) true 12 1 do i proj-at ok-or-full? and loop ;
T{ proj-sweep 1 proj-at -> true outcome-full }T

\ ---- Exhausted: whnfCore's fuel runs out on a type that is no pi.
T{ 1 lf-whnf-fuel! fh fk app lf-infer 0 lf-whnf-fuel! -> -1 outcome-exhausted }T
T{ fh fk app nat infer= -> true outcome-ok }T

\ ---- lf-meta-instantiate-rev-beta (src/front/beta-inst.fs): #k below m
\ is argument k, a larger one m less, below the depth itself; a bound
\ variable at an application's head takes its arguments by a beta step.
create xs 4 cells allot
: x1 ( a -- addr 1 ) xs ! xs 1 ;
: x2 ( a0 a1 -- addr 2 ) xs cell+ ! xs ! xs 2 ;
: rb= ( body addr m expected -- flag outcome )
  >r lf-meta-instantiate-rev-beta r> swap >r same? r> ;
T{ 0 bv fk x1 fk rb= 1 bv fk x1 0 bv rb= -> true outcome-ok true outcome-ok }T
\ Loose indices beyond the arguments are m less, under binders too
\ (review fe1c-2 re-check N1).
T{ 2 bv fk x1 1 bv rb= 5 bv fk fa x2 3 bv rb= -> true outcome-ok true outcome-ok }T
T{ nat 3 bv lam fk x1 nat 2 bv lam rb= 3 bv fk x1 2 bv rb= -> true outcome-ok true outcome-ok }T
T{ nat 1 bv lam fk x1 nat fk lam rb= nat 0 bv lam fk x1 nat 0 bv lam rb=
   -> true outcome-ok true outcome-ok }T
T{ 0 bv fa app sfun x1 fs fa app rb= -> true outcome-ok }T
T{ 1 bv 0 bv app fa sfun x2 fs fa app rb= -> true outcome-ok }T
T{ 1 bv 0 bv app sfun fa x2 fa sfun app rb= -> true outcome-ok }T
T{ fk xs 0 fk rb= 1 bv fk x1 0 bv rb= -> true outcome-ok true outcome-ok }T
\ A head bound inside the body stays; a node holding a metavariable is
\ visited and kept when nothing in it changes; a body with many nodes to
\ make grows the memo's table.
T{ nat 0 bv 1 bv app lam sfun x1 nat 0 bv sfun app lam rb= -> true outcome-ok }T
T{ ?n fk app fa x1 ?n fk app rb= -> true outcome-ok }T
: chain ( x -- t ) fa 6 0 do over app loop nip ;
T{ 0 bv chain fk x1 fk chain rb= -> true outcome-ok }T
\ Unsupported: an argument with a loose bound variable. A beta step under
\ a binder (its argument #0 is loose there) is done where the lambda's
\ body has no binder around its variable (plan FE1g-4), else unsupported.
T{ 0 bv 0 bv x1 lf-meta-instantiate-rev-beta -> -1 outcome-unsupported }T
T{ nat 1 bv 0 bv app lam sfun x1 sfun rb= -> true outcome-ok }T
\ An annotation (core/annotations.fs, S2 merge B) keeps its key around its
\ child's image, and is the same node when the child stays.
: ann ( t -- t' ) lf-annot-match lf-annot ok? 0= abort" annotation" ;
T{ 0 bv ann fk x1 fk ann rb= fk ann dup fa x1 lf-meta-instantiate-rev-beta drop =
   -> true outcome-ok true }T
: deep-fun ( -- t ) nat nat 1 bv tpi lam ;   \ fun x => Nat -> x, a binder around x
T{ nat 1 bv 0 bv app lam deep-fun x1 lf-meta-instantiate-rev-beta -> -1 outcome-unsupported }T
\ Invalid: no body, no argument, a negative m.
T{ -1 fk x1 lf-meta-instantiate-rev-beta 0 bv -1 x1 lf-meta-instantiate-rev-beta
   -> -1 outcome-invalid -1 outcome-invalid }T
T{ 0 bv xs -1 lf-meta-instantiate-rev-beta -> -1 outcome-invalid }T
\ Full: the memo's table refused; then the same call works.
T{ 1 heap-refusals ! 0 bv fk x1 lf-meta-instantiate-rev-beta heap-refusals @
   -> -1 outcome-full 0 }T
T{ 0 bv fk x1 fk rb= -> true outcome-ok }T

\ ---- Stale leaves: after the contexts are emptied, a metavariable and a
\ free variable made before are invalid.
lf-mctx-reset
T{ ?n lf-infer ?n fk app lf-infer -> -1 outcome-invalid -1 outcome-invalid }T
lf-lctx-reset
T{ fk lf-infer fs fk app lf-infer -> -1 outcome-invalid -1 outcome-invalid }T
\ The fed input as loading left it (S1 §1, trust point 3).
T{ lf-input-intact? -> true }T

bye

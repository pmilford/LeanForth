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

\ ---- Unsupported.
T{ nat 0 bv lam lf-infer -> -1 outcome-unsupported }T
T{ nat nat lf-term-pi must lf-infer -> -1 outcome-unsupported }T
T{ nat fk 0 bv let lf-infer -> -1 outcome-unsupported }T
T{ fa fb pair 0 proj lf-infer -> -1 outcome-unsupported }T
T{ nat 0 bv lam fk app lf-infer -> -1 outcome-unsupported }T
T{ rec nat nat lam app fz app fs app fk app lf-infer -> -1 outcome-unsupported }T
\ The type is no pi and whnf would unfold it: fq : outParam (Nat -> Nat).
lv1 1 s" outParam" cn nat>nat app lf-lctx-local made constant fq
T{ fq fk app lf-infer -> -1 outcome-unsupported }T
T{ 0 lf-term-sort must lf-infer -> -1 outcome-unsupported }T

\ ---- Invalid: no term, a loose bound variable, a wrong number of
\ levels, a function expected (a type with a constant, a free variable
\ or a sort at the head that no whnf makes a pi).
T{ -1 lf-infer 0 bv lf-infer -> -1 outcome-invalid -1 outcome-invalid }T
T{ lv1 1 s" Nat.add" cn lf-infer 0 s" Nat.rec" cn lf-infer -> -1 outcome-invalid -1 outcome-invalid }T
T{ fs fk app lf-infer nat fk app lf-infer -> -1 outcome-invalid -1 outcome-invalid }T
T{ fm fk app lf-infer -> -1 outcome-invalid }T
T{ 0 bv fk app lf-infer -> -1 outcome-invalid }T

\ ---- Exhausted: whnfCore's fuel runs out on a type that is no pi.
nat nat>nat lf-lctx-let made constant ftype
nat mv-natural lf-mvar-new made constant ?t
0 ?t ftype lf-mvar-assign made drop
nat ?t lf-lctx-local made constant fh
T{ 1 lf-whnf-fuel! fh fk app lf-infer 0 lf-whnf-fuel! -> -1 outcome-exhausted }T
T{ fh fk app nat infer= -> true outcome-ok }T

bye

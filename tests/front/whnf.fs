\ Unit tests of the front end's whnfCore and getStuckMVar? (plan FE1c;
\ src/front/whnf.fs) over the Init slice, with the variables of
\ tests/front/whnf-cases.fs: every step (beta, zeta, metavariable and let
\ variable heads, iota) with its result; every outcome -- ok, unsupported
\ (definition, projection, quotient and K-like heads, literal and
\ non-inert major premises), invalid (no term, a loose bound variable, a
\ malformed let), exhausted (the fuel), full (a refused allocation) --
\ and that a failed call leaves nothing that changes the next one.
\ Every T{ }T checks the data stack's depth. tests/front/check_whnf.py
\ compares the results with pinned Lean's.
include ../support/tester.fs
include ../support/heap-watch.fs
require ./whnf-cases.fs

\ Terms equal node for node (test only: recursion on the host stack).
: leaf= ( t1 t2 -- flag )
  over lf-term-first@ over lf-term-first@ = >r lf-term-second@ swap lf-term-second@ = r> and ;
: same? ( t1 t2 -- flag )
  2dup = if 2drop true exit then
  over lf-term-tag@ over lf-term-tag@ <> if 2drop false exit then
  over lf-term-tag@ lf-term-binary-tag? 0= if leaf= exit then
  over lf-term-first@ over lf-term-first@ recurse 0= if 2drop false exit then
  lf-term-second@ swap lf-term-second@ recurse ;
: whnf= ( term expected -- flag outcome ) >r lf-whnf-core r> swap >r same? r> ;
: recm ( major -- t ) >r rec fm app fz app fs app r> app ;

\ ---- Full: the first call's first allocation (its spine's slab)
\ refused; the same call again works.
T{ 1 heap-refusals ! fk succ swap app recm lf-whnf-core heap-refusals @ -> -1 outcome-full 0 }T
T{ fk succ swap app recm lf-whnf-core nip -> outcome-ok }T

\ ---- Iota: Nat.rec on Nat.succ k and Nat.zero, extra arguments, stuck.
T{ fk succ swap app recm  fs fk app fk recm app whnf= -> true outcome-ok }T
T{ zero recm fz whnf= -> true outcome-ok }T
T{ zero recm fx app  fz fx app whnf= -> true outcome-ok }T
T{ fk recm dup whnf= -> true outcome-ok }T
T{ rec fm app fz app fs app dup whnf= -> true outcome-ok }T
T{ ?n recm dup whnf= -> true outcome-ok }T
\ Beta, zeta, heads.
T{ nat 0 bv lam fk app fk whnf= -> true outcome-ok }T
T{ nat fk fs 0 bv app let fs fk app whnf= -> true outcome-ok }T
T{ ?f fk app fs fk app whnf= ?h fk app dup whnf= -> true outcome-ok true outcome-ok }T
T{ fg fk app fs fk app whnf= fg sfun whnf= -> true outcome-ok true outcome-ok }T
T{ succ fk app dup whnf= -> true outcome-ok }T
\ A have (Lean's ldecl with nondep := true; plan FE1g-1): its value is
\ hidden, so whnf leaves the variable and its application as they are
\ (Lean's whnfEasyCases unfolds only a let with nondep := false).
nat sfun lf-lctx-have made constant fh
T{ fh lf-fvar-let? fh lf-fvar-nondep? fg lf-fvar-let? fg lf-fvar-nondep? -> false true true false }T
T{ fh lf-fvar-value fg lf-fvar-value fk lf-fvar-value fk lf-fvar-nondep? -> sfun sfun -1 false }T
T{ nat zero lf-lctx-have made lf-fvar-value -> zero }T
T{ fh dup whnf= fh fk app dup whnf= -> true outcome-ok true outcome-ok }T

\ ---- Frames: the major premise and a projection's structure are
\ reduced first (a let, a beta step, an assigned metavariable, an inner
\ recursor), then the step resumes.
: pair ( a b -- t ) >r >r l0 l0 2 s" Prod.mk" cn nat app nat app r> app r> app ;
T{ fa fb pair 0 proj fa whnf= fa fb pair 1 proj fb whnf= -> true outcome-ok true outcome-ok }T
T{ fp 0 proj dup whnf= fa fb pair 2 proj dup whnf= -> true outcome-ok true outcome-ok }T
T{ sfun fb pair 0 proj fk app fs fk app whnf= -> true outcome-ok }T
T{ nat fk succ 0 bv app let recm  fs fk app fk recm app whnf= -> true outcome-ok }T
T{ nat 0 bv lam fk app recm dup whnf= -> true outcome-ok }T
T{ rec fm app fz succ swap app app fs app zero app recm  fs fz app fz recm app whnf=
   -> true outcome-ok }T
T{ fk succ swap app 0 proj fk whnf= -> true outcome-ok }T
\ The structure or major premise needs what whnf would do next.
T{ 0 s" Nat.add" cn fa fb pair app 0 proj lf-whnf-core -> -1 outcome-unsupported }T
T{ 0 s" Nat.add" cn 0 proj lf-whnf-core -> -1 outcome-unsupported }T
T{ 0 s" Nat.add" cn recm lf-whnf-core -> -1 outcome-unsupported }T

\ ---- Unsupported: a definition, a quotient's lift, a K-like recursor, a
\ structure's eta, a Nat.succ that whnf may fold.
T{ 0 s" Nat.add" cn fk app fk app lf-whnf-core -> -1 outcome-unsupported }T
: quot ( -- t ) lv1 lv1 2 s" Quot.lift" cn nat app fx app nat app fs app fb app ;
T{ quot lv1 1 s" Quot.mk" cn nat app fx app fa app app lf-whnf-core
   -> -1 outcome-unsupported }T
T{ lv1 lv1 2 s" Eq.rec" cn nat app fa app fm app fx app fa app fk app lf-whnf-core
   -> -1 outcome-unsupported }T
: prod-rec ( -- t ) lv1 l0 l0 3 s" Prod.rec" cn nat app nat app fm app fs app ;
T{ prod-rec fp app lf-whnf-core -> -1 outcome-unsupported }T
T{ fk succ swap app succ swap app recm lf-whnf-core -> -1 outcome-unsupported }T

\ ---- Invalid: no term, a loose bound variable, a malformed let.
T{ -1 lf-whnf-core 0 bv lf-whnf-core -> -1 outcome-invalid -1 outcome-invalid }T
T{ fk fs 0 lf-let-make must lf-whnf-core -> -1 outcome-invalid }T
T{ 0 bv fk app lf-whnf-core -> -1 outcome-invalid }T

\ ---- Fuel: each step spends one; none left is exhausted.
: twice ( -- t ) nat 0 bv lam  nat 0 bv lam fk app app ;
T{ 2 lf-whnf-fuel! twice lf-whnf-core -> -1 outcome-exhausted }T
T{ 3 lf-whnf-fuel! twice fk whnf= -> true outcome-ok }T
T{ 0 lf-whnf-fuel! twice fk whnf= -> true outcome-ok }T

\ ---- getStuckMVar?.
T{ ?n lf-whnf-stuck -> ?n true outcome-ok }T
T{ ?n recm lf-whnf-stuck ?h fk app lf-whnf-stuck -> ?n true outcome-ok ?h true outcome-ok }T
T{ fk recm lf-whnf-stuck fs fk app lf-whnf-stuck -> false outcome-ok false outcome-ok }T
T{ ?n succ swap app recm lf-whnf-stuck -> false outcome-ok }T
T{ 0 s" Nat.add" cn fk app fk app lf-whnf-stuck -> false outcome-ok }T
T{ 0 s" Nat.add" cn ?n app fk app lf-whnf-stuck -> false outcome-unsupported }T
T{ ?f lf-whnf-stuck fp s" Prod" menv-name 0 lf-proj-of made lf-whnf-stuck
   -> false outcome-unsupported false outcome-unsupported }T
T{ -1 lf-whnf-stuck fk lf-whnf-stuck -> false outcome-invalid false outcome-ok }T
\ A K-like recursor is never stuck (isRecStuck?).
: eq-rec ( major -- t ) >r lv1 lv1 2 s" Eq.rec" cn nat app fa app fm app fx app fa app r> app ;
T{ ?h eq-rec lf-whnf-stuck ?h eq-rec lf-whnf-core -> false outcome-ok -1 outcome-unsupported }T

\ ---- A delayed-assigned metavariable at the head: unsupported (Lean's
\ whnfDelayedAssigned? is not ported).
nat mv-natural lf-mvar-new made constant ?d
0 fx lf-delay-fvar made drop  0 ?d ?n 1 lf-mvar-delay made drop
T{ ?d fk app lf-whnf-core ?d lf-whnf-stuck -> -1 outcome-unsupported false outcome-unsupported }T
T{ ?d fk app recm lf-whnf-core -> -1 outcome-unsupported }T

\ ---- More heads: a let, a pi (done), a constant no declaration has
\ (Lean's find? none: done); leaves alone.
: unknown ( -- t ) 0 s" motive" menv-part lf-name-generation @ lv-pairs 0 lf-cref-new must
  lf-cterm-new must drop ;
T{ nat fs 0 bv let fk app fs fk app whnf= -> true outcome-ok }T
T{ nat nat lf-term-pi must fk app dup whnf= unknown fk app dup whnf=
   -> true outcome-ok true outcome-ok }T
T{ ?f sfun whnf= fk dup whnf= -> true outcome-ok true outcome-ok }T
\ More major premises: another type's constructor (no rule), a wrong
\ number of levels (Lean's failK), a structure's constructor applied to
\ exactly its parameters and fields.
T{ fa fb pair recm dup whnf= -> true outcome-ok }T
T{ 0 s" Nat.rec" cn fm app fz app fs app zero app dup whnf= -> true outcome-ok }T
T{ prod-rec fa fb pair app fs fa app fb app whnf= -> true outcome-ok }T
\ More of getStuckMVar?: a constant no declaration has, a quotient's
\ lift, a constructor at the head, a Nat.succ whnf may fold.
T{ unknown fk app lf-whnf-stuck succ fk app lf-whnf-stuck -> false outcome-ok false outcome-ok }T

\ ---- Review fe1c-2 L1: a projection of a literal or of a constant no
\ declaration has (whnf would go on: toCtorIfLit; Lean throws), Nat.succ
\ alone as a major premise (fewer arguments than the rule's fields: the
\ rule's right side takes none), a malformed let whose binder is an
\ application, and a recursor of a nested block (Lean.Syntax.rec, three
\ motives).
: three ( -- t ) s" 3" lf-hterm-decimal must drop ;
T{ three 0 proj lf-whnf-core unknown 0 proj lf-whnf-core
   -> -1 outcome-unsupported -1 outcome-unsupported }T
T{ succ recm  nat fs 0 bv app rec fm app fz app fs app 0 bv app app lam whnf=
   -> true outcome-ok }T
T{ fk fs fk app 0 lf-let-make must lf-whnf-core -> -1 outcome-invalid }T
: syntax-rec ( n -- t ) >r lv1 1 s" Lean.Syntax.rec" cn r> 0 ?do fk app loop ;
T{ 11 syntax-rec lf-whnf-core 10 syntax-rec dup whnf= -> -1 outcome-unsupported true outcome-ok }T
T{ quot fa app lf-whnf-stuck -> false outcome-unsupported }T
T{ ?n succ swap app succ swap app recm lf-whnf-stuck -> false outcome-unsupported }T
\ A projection of a metavariable, alone or applied, is stuck on it (review
\ fe1c-2 M1); of anything else it would need whnf.
T{ ?q 0 proj fk app lf-whnf-stuck ?q 0 proj lf-whnf-stuck -> ?q true outcome-ok ?q true outcome-ok }T
T{ fa fb pair 0 proj fk app lf-whnf-stuck -> false outcome-unsupported }T
\ A major premise whose head is no constant is never read as one (review
\ M2): a lambda; a free variable whose number is Nat.succ's reference's.
T{ nat 0 bv lam recm lf-whnf-stuck -> false outcome-ok }T
variable want
: fvar-at ( n -- fvar ) want ! begin nat lf-lctx-local made dup lf-term-first@ want @ < while
  drop repeat ;
succ lf-term-first@ fvar-at constant ftwin
T{ ftwin lf-term-first@ succ lf-term-first@ = -> true }T
T{ ftwin zero app recm lf-whnf-stuck -> false outcome-ok }T

\ ---- Stale leaves: after the contexts are emptied, every metavariable
\ and free variable made before is invalid.
lf-mctx-reset
T{ ?n lf-whnf-core ?n fk app lf-whnf-core ?n lf-whnf-stuck
   -> -1 outcome-invalid -1 outcome-invalid false outcome-invalid }T
lf-lctx-reset
T{ fk lf-whnf-core fk fa app lf-whnf-core -> -1 outcome-invalid -1 outcome-invalid }T

bye

\ Unit tests of the front end's isDefEq (plan FE1c; src/front/defeq.fs)
\ and its helpers (term-eqv.fs, prop-quick.fs, assign-check.fs,
\ nat-offset.fs, fun-info.fs) over the Init slice, with the variables of
\ tests/front/defeq-cases.fs: every outcome of lf-meta-defeq -- ok with
\ true and false, unsupported, invalid (no term, a loose bound variable,
\ an ill-typed term), exhausted (the fuel), full (each heap allocation
\ refused in turn) -- what each helper answers, and that a call leaves
\ no mark open, no new depth and no assignment when its answer is not
\ true. Every T{ }T checks the data stack's depth.
\ tests/front/check_defeq.py compares the answers with pinned Lean's.
include ../support/tester.fs
include ../support/heap-watch.fs
require ./defeq-cases.fs

: dq ( t s -- flag outcome ) lf-meta-defeq ;
: inst ( t -- t' ) lf-instantiate-mvars drop ;
: same ( a b -- flag ) lf-meta-eqv drop ;
\ A mark of the test's own around a case that assigns, and its rollback.
: own-mark ( -- ) lf-mctx-mark 2drop ;
: own-back ( -- ) lf-mctx-latest lf-mctx-rollback drop ;
: clean? ( -- flag ) lf-mctx-marks 0= lf-mctx-depth 0= and ;
: free? ( mvar -- flag ) lf-mvar-value dup if nip 0= else drop true then ;
: ofnat ( n -- t ) >r l0 1 s" OfNat.ofNat" cn nat app r@ nlit app
  0 s" instOfNatNat" cn r> nlit app app ;
: hadd ( a b -- t ) >r >r l0 l0 l0 3 s" HAdd.hAdd" cn nat app nat app nat app
  l0 1 s" instHAdd" cn nat app 0 s" instAddNat" cn app app r> app r> app ;
: pair ( a b -- t ) >r >r l0 l0 2 s" Prod.mk" cn nat app nat app r> app r> app ;
: nat-add ( a b -- t ) >r >r 0 s" Nat.add" cn r> app r> app ;
lf-defeq-elab lf-defeq-flags!

\ ---- Every outcome.
T{ fk fk dq fk fx dq -> true outcome-ok false outcome-ok }T
T{ fp 0 proj fa dq -> false outcome-unsupported }T
T{ -1 fk dq fk -1 dq -> false outcome-invalid false outcome-invalid }T
T{ 0 bv fk dq -> false outcome-invalid }T
T{ fs fk app fx dq -> false outcome-invalid }T
T{ 1 lf-defeq-fuel! succ fk app succ fx app dq 0 lf-defeq-fuel! -> false outcome-exhausted }T
T{ 2 lf-defeq-fuel! fk fk dq 0 lf-defeq-fuel! -> true outcome-ok }T
T{ clean? -> true }T

\ ---- Answers kept or rolled back: a true answer keeps its assignments,
\ a false or failed one none (checkpointDefEq).
T{ own-mark ?n fk dq ?n inst fk = own-back -> true outcome-ok true }T
T{ own-mark fa fb pair fa ?n pair dq ?n free? own-back -> true outcome-ok false }T
T{ ?n free? ?n fa pair fb fb pair dq ?n free? -> true false outcome-ok true }T
T{ own-mark ?n fb pair fa fb pair dq ?n inst own-back -> true outcome-ok fa }T
T{ ?n fp 0 proj pair fa fb pair dq ?n free? clean? -> false outcome-unsupported true true }T
T{ own-mark lf-mctx-marks fk ?n dq 2drop lf-mctx-marks own-back -> 1 1 }T
T{ ?n succ ?n app dq ?n free? -> false outcome-ok true }T

\ ---- Quick checks, binders, eta, proof irrelevance.
T{ l0 sort l0 sort dq l0 sort lv1 sort dq -> true outcome-ok false outcome-ok }T
T{ 2 nlit 2 nlit dq 2 nlit 3 nlit dq -> true outcome-ok false outcome-ok }T
T{ punit lv2 1 s" PUnit" cn dq -> false outcome-ok }T
T{ nat 0 bv lam l0 sort 0 bv lam dq -> false outcome-ok }T
T{ nat>nat nat>nat dq nat>nat nat l0 sort tpi dq -> true outcome-ok false outcome-ok }T
T{ nat fu 0 bv app lam fu dq fu nat fu 0 bv app lam dq -> true outcome-ok true outcome-ok }T
T{ own-mark nat ?t 0 bv app lam succ dq ?t inst succ = own-back -> true outcome-ok true }T
T{ fe fc dq fe lv1 1 s" Eq.refl" cn nat app fa app dq -> true outcome-ok false outcome-ok }T
T{ nat fk fx let fx dq fg nat fs 0 bv app lam dq -> true outcome-ok true outcome-ok }T
T{ fv fw dq fv lv1 1 s" PUnit.unit" cn dq -> true outcome-ok true outcome-ok }T

\ ---- Assignment: scope, types, patterns, first-order approximation.
T{ ?n fj dq ?r fj dq ?n nat dq -> false outcome-ok false outcome-ok false outcome-ok }T
T{ own-mark ?t fj app succ fj app dq ?t inst succ = own-back -> true outcome-ok true }T
T{ own-mark ?t fj app succ fk app dq ?t inst nat succ fk app lam same own-back
   -> true outcome-ok true }T
T{ ?t fj app fu fj app dq nat ?t 0 bv app lam fu dq -> false outcome-ok false outcome-ok }T
T{ own-mark ?y fk app fk app fk fk nat-add dq ?y inst 0 s" Nat.add" cn same own-back
   -> true outcome-ok true }T
T{ 0 lf-defeq-flags! ?t fk app succ fk app dq lf-defeq-elab lf-defeq-flags! -> false outcome-ok }T
T{ ?t fk app ?t fx app dq ?t 2 nlit app succ fk app dq -> false outcome-ok false outcome-ok }T
\ ?o, synthetic opaque and made after ?n, is out of ?n's scope (Lean: false).
T{ own-mark ?n ?h dq ?n inst own-back ?n ?o dq -> true outcome-ok ?h false outcome-ok }T
T{ ?o fk dq -> false outcome-ok }T
T{ own-mark ?n 2 nlit dq ?n inst 2 nlit same own-back -> true outcome-ok true }T
T{ lf-mctx-deeper ?n fk dq lf-mctx-shallower -> false outcome-ok }T

\ ---- whnfCore and Nat offsets (Lean's mkOffset: k + 1, not Nat.succ k).
T{ 0 s" Nat" cn fk lam fk app fk dq -> true outcome-ok }T
T{ own-mark succ ?h app succ succ fk app app dq ?h inst fk 1 ofnat hadd same own-back
   -> true outcome-ok true }T
T{ succ fk app 0 nlit dq 0 nlit zero dq 1 nlit zero dq
   -> false outcome-ok true outcome-ok false outcome-ok }T
T{ own-mark succ ?h app 3 nlit dq ?h inst 2 ofnat same own-back clean? -> true outcome-ok true true }T
T{ 3 nlit succ succ succ zero app app app dq -> false outcome-unsupported }T
T{ succ ?h app 0 ofnat fk 1 ofnat hadd hadd dq ?h free? -> false outcome-unsupported true }T

\ ---- Transparency: a definition is a delta candidate at default only.
T{ lf-tr-reducible lf-defeq-mode! 0 s" Nat.add" cn 0 s" Nat.mul" cn dq
   lf-tr-default lf-defeq-mode! -> false outcome-ok }T
T{ 0 s" Nat.add" cn 0 s" Nat.mul" cn dq -> false outcome-unsupported }T

\ ---- Helpers. Lean's ==, etaExpanded?, names.
T{ 0 s" Nat" cn nat lf-meta-eqv punit lv2 1 s" PUnit" cn lf-meta-eqv
   -> true outcome-ok false outcome-ok }T
T{ fk fx lf-meta-eqv -1 fk lf-meta-eqv -> false outcome-ok false outcome-invalid }T
T{ nat fu 0 bv app lam lf-meta-eta-expanded -> fu true outcome-ok }T
T{ nat 0 bv lam lf-meta-eta-expanded rot drop -> false outcome-ok }T
T{ succ s" Nat.succ" lf-meta-const-named? succ s" Nat" lf-meta-const-named? -> true false }T
T{ fk s" Nat" lf-meta-const-named? succ s" succ" lf-meta-const-named? -> false false }T
T{ fu fk app fx app lf-meta-head lf-lb-undef lf-lb-true lf-lb-false -> fu 2 1 0 }T
\ isPropQuick, isProofQuick, isAlwaysZero.
T{ fe lf-meta-proof-quick fk lf-meta-proof-quick 0 bv lf-meta-proof-quick
   -> lf-lb-true outcome-ok lf-lb-false outcome-ok lf-lb-undef outcome-ok }T
T{ eqab lf-meta-prop-quick nat lf-meta-prop-quick nat 0 bv lam lf-meta-prop-quick
   -> lf-lb-true outcome-ok lf-lb-false outcome-ok lf-lb-false outcome-ok }T
T{ l0 lf-meta-always-zero? lv1 lf-meta-always-zero? -> true outcome-ok false outcome-ok }T
\ checkAssignment and mkLambdaFVars.
create xs 2 cells allot  fj xs !  fk xs cell+ !
T{ ?n xs 0 fk lf-meta-check-assignment ?n xs 0 fj lf-meta-check-assignment
   -> fk true outcome-ok fj false outcome-ok }T
T{ ?n xs 0 succ ?n app lf-meta-check-assignment rot drop ?r xs 1 fj lf-meta-check-assignment
   -> false outcome-ok fj true outcome-ok }T
T{ xs 1 succ fj app lf-meta-mk-lambda xs 1 fk lf-meta-mk-lambda swap nat fk lam same
   -> succ outcome-ok outcome-ok true }T
T{ ?n fk lf-meta-sees? ?n fj lf-meta-sees? -> true false }T
\ evalNat, isOffset?, mkOffset.
T{ 3 nlit lf-meta-eval-nat zero succ swap app lf-meta-eval-nat -> 3 true outcome-ok 1 true outcome-ok }T
T{ 2 ofnat 3 ofnat hadd lf-meta-eval-nat fk lf-meta-eval-nat -> 5 true outcome-ok 0 false outcome-ok }T
T{ 2 nlit 1 nlit >r >r 0 s" Nat.sub" cn r> app r> app lf-meta-eval-nat -> 0 false outcome-unsupported }T
T{ succ fk app lf-meta-offset fk 2 ofnat hadd lf-meta-offset -> fk 1 true outcome-ok fk 2 true outcome-ok }T
T{ fk lf-meta-offset 2swap 2drop -> false outcome-ok }T
T{ fk 0 lf-meta-mk-offset zero 3 lf-meta-mk-offset >r 3 ofnat same r> -> fk outcome-ok true outcome-ok }T
\ whnf's fixed points, isProp, getFunInfoNArgs, isClassQuick?.
T{ fk lf-meta-whnf-final? succ fk app lf-meta-whnf-final? succ 2 nlit app lf-meta-whnf-final?
   -> true true false }T
T{ fk fk nat-add lf-meta-whnf-final? l0 sort lf-meta-whnf-final? -> false true }T
T{ eqab lf-meta-is-prop nat lf-meta-is-prop -> true outcome-ok false outcome-ok }T
T{ succ 1 lf-meta-fun-info 0 lf-meta-param -> 1 outcome-ok lf-binder-default false }T
T{ nat l0 sort lf-meta-class-none? fk lf-meta-class-none? -> nat true true }T
T{ nat lf-meta-class-none? -> false }T

\ ---- Resources: each allocation refused in turn gives full or the
\ answer, and leaves nothing behind.
: refused ( t s k -- flag outcome ) heap-refusals ! dq 0 heap-refusals ! ;
: offset-pair ( -- t s ) succ ?h app succ succ fk app app ;
: eta-pair ( -- t s ) nat ?t 0 bv app lam succ ;
variable fulls  variable pair-xt
: answer-sound? ( flag outcome -- ok? )
  dup outcome-full = if 2drop 1 fulls +! true else outcome-ok = and then ;
\ The k-th allocation refused: full or the true answer; once the test's
\ mark is rolled back, no mark, no depth and ?h and ?t free.
: refusal-sound? ( k -- flag )
  own-mark >r pair-xt @ execute r> refused answer-sound? own-back
  clean? and ?h free? and ?t free? and ;
: refusals-sound? ( xt -- flag )
  pair-xt ! 0 fulls ! true 300 1 do i refusal-sound? and loop ;
T{ ' offset-pair refusals-sound? fulls @ 0> -> true true }T
T{ ' eta-pair refusals-sound? fulls @ 0> -> true true }T
T{ own-mark offset-pair dq ?h free? own-back -> true outcome-ok false }T
\ A call frees what it allocates (its slabs keep their room).
T{ own-mark live-blocks @ offset-pair dq 2drop live-blocks @ = own-back clean? -> true true }T

bye

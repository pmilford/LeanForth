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
: free? ( mvar -- flag ) lf-mvar-value dup if nip 0= else drop true then ;
: chk ( mvar addr n v -- v' flag outcome ) >r lf-meta-pattern! r> lf-meta-check-assignment ;

\ More variables: a let out of ?n's scope, a free variable whose type
\ holds ?n, metavariables in ?n's context whose type holds ?n (?w) or
\ that is delayed (?d), one whose context adds j (?z), a level
\ metavariable ?u and ?M : Sort (?u + 1), a dead free variable.
: anon ( type -- fvar ) lf-lctx-local made in-view ;
nat fk lf-lctx-let made in-view constant fl
lv1 1 s" Eq" cn nat app ?n app ?n app anon constant fq
: n-view ( -- view ) ?n lf-mvar-view drop ;
: at-n ( type -- mvar ) mv-natural n-view lf-mvar-new-at made ;
0 s" Fin" cn ?n app at-n constant ?w
nat at-n constant ?d
: j-local ( -- local ) lf-mctx-view dup fj lf-view-find drop lf-view-local ;
: view+j ( -- view ) n-view j-local lf-view-push made ;
nat mv-natural view+j lf-mvar-new-at made constant ?z
lf-level-mvar-new made constant ?u
?u lf-level-succ must sort mv-natural lf-mvar-new made constant ?M
: dead-fvar ( -- fvar ) lf-term-base lf-term-count @ + nat lf-lctx-local made swap lf-lctx-drop ;
dead-fvar constant fdead
create xs 2 cells allot  fj xs !  fk xs cell+ !
create xk 1 cells allot  fk xk !
create xq 1 cells allot  fq xq !
create xaj 2 cells allot  fa xaj !  fj xaj cell+ !
lf-lctx-count @ constant lctx0  lf-mctx-view constant view0
\ No mark open, no new depth, the local context as before.
: clean? ( -- flag )
  lf-mctx-marks 0= lf-mctx-depth 0= and lf-lctx-count @ lctx0 = and lf-mctx-view view0 = and ;
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
\ Implicit arguments are compared after the explicit ones, but compared.
: refl ( type -- t ) lv1 1 s" Eq.refl" cn swap app fa app ;
T{ nat refl l0 l0 2 s" Prod" cn nat app nat app refl dq -> false outcome-ok }T

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
T{ deeper ?n fk dq shallower -> false outcome-ok }T

\ ---- whnfCore and Nat offsets (Lean's mkOffset: k + 1, not Nat.succ k).
T{ 0 s" Nat" cn fk lam fk app fk dq -> true outcome-ok }T
T{ own-mark succ ?h app succ succ fk app app dq ?h inst fk 1 ofnat hadd same own-back
   -> true outcome-ok true }T
T{ succ fk app 0 nlit dq 0 nlit zero dq 1 nlit zero dq
   -> false outcome-ok true outcome-ok false outcome-ok }T
T{ own-mark succ ?h app 3 nlit dq ?h inst 2 ofnat same own-back clean? -> true outcome-ok true true }T
T{ 3 nlit succ succ succ zero app app app dq -> false outcome-unsupported }T
\ FE1's acceptance case (S2 merge B's smart unfolding after lazy delta):
\ Nat.succ ?h against 0 + (k + 1) assigns ?h := Nat.add 0 k, as Lean.
T{ own-mark succ ?h app 0 ofnat fk 1 ofnat hadd hadd dq ?h inst
   0 s" Nat.add" cn 0 ofnat app fk app same own-back -> true outcome-ok true }T

\ ---- Transparency: a definition is a delta candidate at default only;
\ there lazy delta (S2 merge A) finds that neither constant unfolds (each
\ has a `_sunfold`, so a constant alone stays) and they differ.
T{ lf-tr-reducible lf-defeq-mode! 0 s" Nat.add" cn 0 s" Nat.mul" cn dq
   lf-tr-default lf-defeq-mode! -> false outcome-ok }T
T{ 0 s" Nat.add" cn 0 s" Nat.mul" cn dq -> false outcome-ok }T
\ isDefEqProjInst at instances transparency might unfold a definition.
T{ lf-tr-instances lf-defeq-mode! 0 s" Nat.add" cn fk dq lf-tr-default lf-defeq-mode!
   -> false outcome-unsupported }T
T{ own-mark lf-tr-none lf-defeq-mode! ?n fk dq own-back own-mark lf-tr-all lf-defeq-mode!
   ?n fk dq own-back lf-tr-default lf-defeq-mode! -> true outcome-ok true outcome-ok }T

\ ---- Flags: constApprox answers unsupported where Lean would act;
\ isDefEqStuckEx raises the stuck signal where Lean throws it (two heads
\ neither side assigns, ExprDefEq.lean:2118), every mark rolled back;
\ isDefEqGuarded answers false for it alone; outcome-sane, at the Meta
\ layer's exits, makes it invalid. A read-only metavariable's arguments.
: with-flags ( t s flags -- flag outcome )
  lf-defeq-flags! dq lf-defeq-elab lf-defeq-flags! ;
: guarded ( t s -- flag outcome )
  lf-defeq-elab lf-defeq-stuck or lf-defeq-flags! lf-meta-defeq-guarded
  lf-defeq-elab lf-defeq-flags! ;
T{ ?t fk app ?t fx app lf-defeq-elab lf-defeq-const or with-flags
   -> false outcome-unsupported }T
T{ ?t fk app succ fk app lf-defeq-const with-flags -> false outcome-unsupported }T
T{ ?o fk lf-defeq-elab lf-defeq-stuck or with-flags -> false lf-meta-stuck }T
T{ ?o fk lf-defeq-elab lf-defeq-stuck or with-flags outcome-sane -> false outcome-invalid }T
T{ ?o fk guarded clean? own-mark ?n fk guarded ?n lf-mvar-value nip own-back
   -> false outcome-ok true true outcome-ok true }T
T{ fp 0 proj fa guarded -1 fk guarded -> false outcome-unsupported false outcome-invalid }T
\ A configuration scope (meta-config.fs, Lean's withConfig): saved and
\ given back whole.
T{ lf-meta-config lf-tr-none lf-defeq-mode! 0 lf-defeq-flags! lf-defeq-flags lf-defeq-mode
   2swap lf-meta-config! lf-meta-config -> 0 lf-tr-none lf-defeq-elab lf-tr-default }T
T{ lf-defeq-univ lf-meta-flag? lf-defeq-opaque lf-meta-flag? lf-meta-default lf-defeq-univ =
   -> true false true }T
\ The budget (meta-config.fs): each comparison spends a step; none left
\ is exhausted.
T{ 1 lf-meta-budget! succ fk app succ fx app dq lf-meta-budget
   lf-meta-default-budget lf-meta-budget! -> false outcome-exhausted 0 }T
T{ deeper ?t fk app ?t fx app dq shallower -> false outcome-ok }T
\ processAssignment' retries with whnf: ?n =?= Nat.rec _ ?n _ Nat.zero
\ fails the occurs check, but its whnf is ?n itself.
: rec-n ( -- t ) rec nat nat lam app ?n app nat nat 0 bv lam lam app zero app ;
T{ ?n rec-n dq ?n free? -> true outcome-ok true }T
\ Eta: fun y => k against k, whose type is no pi.
T{ nat fk lam fk dq -> false outcome-ok }T

\ ---- Helpers. Lean's ==, etaExpanded?, names.
T{ 0 s" Nat" cn nat lf-meta-eqv punit lv2 1 s" PUnit" cn lf-meta-eqv
   -> true outcome-ok false outcome-ok }T
T{ fk fx lf-meta-eqv -1 fk lf-meta-eqv -> false outcome-ok false outcome-invalid }T
T{ 0 s" Nat.add" cn 0 s" Nat.mul" cn lf-meta-eqv -> false outcome-ok }T
T{ nat fu 0 bv app lam lf-meta-eta-expanded -> fu true outcome-ok }T
T{ nat 0 bv lam lf-meta-eta-expanded rot drop -> false outcome-ok }T
T{ succ s" Nat.succ" lf-meta-const-named? succ s" Nat" lf-meta-const-named? -> true false }T
T{ fk s" Nat" lf-meta-const-named? succ s" succ" lf-meta-const-named? -> false false }T
\ Names of any number of parts (core/statement-match.fs's lf-name-dotted?).
: abc ( -- id )
  0 s" A" lf-name-str drop s" B" lf-name-str drop s" C" lf-name-str drop ;
T{ s" A.B.C" abc lf-meta-name? s" B.C" abc lf-meta-name? s" X.A.B.C" abc lf-meta-name?
   -> true false false }T
T{ fu fk app fx app lf-meta-head lf-lb-undef lf-lb-true lf-lb-false -> fu 2 1 0 }T
\ isPropQuick, isProofQuick, isAlwaysZero.
T{ fe lf-meta-proof-quick fk lf-meta-proof-quick 0 bv lf-meta-proof-quick
   -> lf-lb-true outcome-ok lf-lb-false outcome-ok lf-lb-undef outcome-ok }T
T{ eqab lf-meta-prop-quick nat lf-meta-prop-quick nat 0 bv lam lf-meta-prop-quick
   -> lf-lb-true outcome-ok lf-lb-false outcome-ok lf-lb-false outcome-ok }T
T{ l0 lf-meta-always-zero? lv1 lf-meta-always-zero? -> true outcome-ok false outcome-ok }T
\ checkAssignment and mkLambdaFVars.
T{ ?n xs 0 fk chk ?n xs 0 fj chk
   -> fk true outcome-ok fj false outcome-ok }T
T{ ?n xs 0 succ ?n app chk rot drop ?r xs 1 fj chk
   -> false outcome-ok fj true outcome-ok }T
T{ xs 1 succ fj app lf-meta-mk-lambda xs 1 fk lf-meta-mk-lambda swap nat fk lam same
   -> succ outcome-ok outcome-ok true }T
T{ ?n fk lf-mvar-sees? ?n fj lf-mvar-sees? -> true false }T
\ evalNat, isOffset?, mkOffset.
T{ 3 nlit lf-meta-eval-nat zero succ swap app lf-meta-eval-nat -> 3 true outcome-ok 1 true outcome-ok }T
T{ 2 ofnat 3 ofnat hadd lf-meta-eval-nat fk lf-meta-eval-nat -> 5 true outcome-ok 0 false outcome-ok }T
T{ l0 1 s" OfNat.ofNat" cn nat app 2 nlit app fk app lf-meta-eval-nat -> 0 false outcome-ok }T
: nat-op ( a b c-addr u -- t ) 0 -rot cn rot app swap app ;
T{ 2 nlit 1 nlit s" Nat.sub" nat-op lf-meta-eval-nat -> 0 false outcome-unsupported }T
T{ 2 nlit 3 nlit s" Nat.mul" nat-op lf-meta-eval-nat -> 0 false outcome-unsupported }T
T{ succ fk app lf-meta-offset fk 2 ofnat hadd lf-meta-offset -> fk 1 true outcome-ok fk 2 true outcome-ok }T
T{ fk lf-meta-offset 2swap 2drop -> false outcome-ok }T
T{ fk 0 lf-meta-mk-offset zero 3 lf-meta-mk-offset swap 3 ofnat same
   -> fk outcome-ok outcome-ok true }T
: add-nat ( a b -- t ) l0 1 s" Add.add" cn nat app 0 s" instAddNat" cn app
  rot app swap app ;
T{ 2 nlit 3 nlit add-nat lf-meta-eval-nat fk 2 nlit s" Nat.add" nat-op lf-meta-offset
   -> 5 true outcome-ok fk 2 true outcome-ok }T
T{ fk 2 nlit add-nat succ swap app lf-meta-offset -> fk 3 true outcome-ok }T
\ An inner addition without a value is the offset's base.
: off-sk ( e -- s k ) lf-meta-offset 2drop ;
T{ fk fx s" Nat.add" nat-op dup succ swap app off-sk rot rot = -> 1 true }T
\ An instance that is not Nat's node for node: Lean asks isDefEq.
: hadd-by ( inst a b -- t ) >r >r >r l0 l0 l0 3 s" HAdd.hAdd" cn nat app nat app nat app
  r> app r> app r> app ;
T{ fx fk 2 nlit hadd-by lf-meta-offset 2swap 2drop -> false outcome-unsupported }T
\ whnf's fixed points, isProp, getFunInfoNArgs, isClassQuick?.
T{ fk lf-meta-whnf-final? succ fk app lf-meta-whnf-final? succ 2 nlit app lf-meta-whnf-final?
   -> true outcome-ok true outcome-ok false outcome-ok }T
T{ fk fk nat-add lf-meta-whnf-final? l0 sort lf-meta-whnf-final?
   -> false outcome-ok true outcome-ok }T
T{ eqab lf-meta-is-prop nat lf-meta-is-prop -> true outcome-ok false outcome-ok }T
T{ succ 1 lf-meta-fun-info 0 lf-meta-param -> 1 outcome-ok lf-binder-default false }T
T{ nat l0 sort lf-meta-class-none? fk lf-meta-class-none? -> nat true true }T
T{ nat lf-meta-class-none? -> false }T
\ (A projection's type is inferred since S2 merge B: p.0 : Nat is no proof.)
T{ fk lf-meta-is-prop fp 0 proj lf-meta-is-prop -> false outcome-ok false outcome-ok }T
T{ fs 1 lf-meta-fun-info ?t 1 lf-meta-fun-info fp 0 proj 1 lf-meta-fun-info
   -> 0 outcome-ok 1 outcome-ok 0 outcome-ok }T
: hadd3 ( -- f ) l0 l0 l0 3 s" HAdd.hAdd" cn ;
T{ hadd3 6 lf-meta-fun-info 0 lf-meta-param 3 lf-meta-param 5 lf-meta-param
   -> 6 outcome-ok lf-binder-implicit false lf-binder-instance false lf-binder-default false }T
\ A higher-order out-parameter is unsupported (review reuse-1a M2): no
\ constant of the slice has one (Init's Functor.map would: [Functor f],
\ f : Type u -> Type v), so the telescope's records are filled by hand:
\ fu : Nat -> Nat explicit, then an implicit h : Eq fu fu, whose type's
\ head might be a class and has fu, a function, as an argument; h leaves
\ the local context at the end.
: ho-params ( h -- )
  fi-params slab-clear fu lf-binder-default 0 fi-push drop lf-binder-implicit 0 fi-push drop ;
: ho-run ( -- outcome outcome outcome )
  fi-mark >r lv1 1 s" Eq" cn nat>nat app fu app fu app lf-lctx-local made ho-params
  0 fi-ho-free 1 fi-ho-free fi-props r> lf-lctx-drop ;
T{ ho-run lf-lctx-count @ -> outcome-ok outcome-unsupported outcome-unsupported lctx0 }T
\ isProofQuick through a head's arguments: Eq.refl's type ends in Prop,
\ id's in its type argument (Nat, never zero), HAdd.hAdd's in an outParam.
: id-k ( -- t ) lv1 1 s" id" cn nat app fk app ;
T{ nat refl lf-meta-proof-quick id-k lf-meta-proof-quick fk fx hadd lf-meta-proof-quick
   -> lf-lb-true outcome-ok lf-lb-false outcome-ok lf-lb-false outcome-ok }T
T{ fu fk app lf-meta-proof-quick nat fe lam fk app lf-meta-proof-quick ?h lf-meta-proof-quick
   -> lf-lb-false outcome-ok lf-lb-true outcome-ok lf-lb-false outcome-ok }T
T{ nat eqab tpi lf-meta-prop-quick nat fk eqab let lf-meta-prop-quick fu fk app lf-meta-prop-quick
   -> lf-lb-true outcome-ok lf-lb-true outcome-ok lf-lb-undef outcome-ok }T
\ The tag sets (review F3 of 2026-11-18): a pi or a sort is no proof, a
\ lambda or a sort no proposition; a let and a lambda are passed to their
\ bodies by isProofQuick.
T{ nat nat tpi lf-meta-proof-quick nat lf-meta-proof-quick
   -> lf-lb-false outcome-ok lf-lb-false outcome-ok }T
T{ nat lf-meta-prop-quick nat fk lam lf-meta-prop-quick
   -> lf-lb-false outcome-ok lf-lb-false outcome-ok }T
T{ nat fk fe let lf-meta-proof-quick nat fe lam lf-meta-proof-quick
   -> lf-lb-true outcome-ok lf-lb-true outcome-ok }T
\ evalNat's unported operations, a table per number of arguments
\ (nat-offset.fs, review F10): each count's table, a known name with a
\ count of no table, and a term with no arguments.
: k-args ( f n -- t ) 0 ?do fk app loop ;
T{ 0 s" Nat.sub" cn 2 k-args no-unported? 0 s" Sub.sub" cn 4 k-args no-unported?
   0 s" Pow.pow" cn 5 k-args no-unported? 0 s" HPow.hPow" cn 6 k-args no-unported?
   -> true true true true }T
T{ 0 s" Pow.pow" cn 4 k-args no-unported? 0 s" Nat.sub" cn 9 k-args no-unported?
   fk no-unported? -> false false false }T
: lmax ( a b -- l ) lf-level-tag-max lf-level-binary drop ;
: limax ( a b -- l ) lf-level-tag-imax lf-level-binary drop ;
T{ l0 l0 lmax lf-meta-always-zero? lv1 l0 limax lf-meta-always-zero? l0 lv1 lmax lf-meta-always-zero?
   -> true outcome-ok true outcome-ok false outcome-ok }T
\ Lean's == by content: the slice's Nat and Sort 1 against the store's.
: input-nat ( -- t ) s" Nat.succ" menv-decl lf-menv-type lf-term-first@ ;
: input-type ( -- t ) s" Nat" menv-decl lf-menv-type ;
T{ input-nat nat lf-meta-eqv input-type lv1 sort lf-meta-eqv input-type l0 sort lf-meta-eqv
   -> true outcome-ok true outcome-ok false outcome-ok }T
T{ fp 0 proj fp 1 proj lf-meta-eqv -> false outcome-ok }T
\ ctxApprox as configured (review N1 of 2026-11-18): read where it is
\ used, so lf-meta-with's scope sets it and gives it back.
: ctx-on ( -- ) lf-defeq-flags lf-defeq-ctx or lf-defeq-flags! ;
: ctx-off ( -- ) lf-defeq-flags lf-defeq-ctx invert and lf-defeq-flags! ;
T{ ctx-off ' ac-approx? lf-defeq-ctx lf-tr-default lf-meta-with ac-approx? -> true false }T
\ checkAssignment's refusals: an out-of-scope let variable, a variable
\ out of scope inside a beta-redex or under ctxApprox, hasCtxLocals.
T{ ?n xs 0 fl chk rot drop ?n xs 0 nat fj lam fk app
   chk rot drop -> false outcome-unsupported false outcome-unsupported }T
T{ ctx-on ?n xs 0 ?t fj app chk rot drop
   ctx-off ?n xk 1 ?h chk
   -> false outcome-unsupported ?h false outcome-ok }T
T{ ?n xs 0 nat fk fj let chk rot drop -> false outcome-ok }T
\ mkLambdaFVars: an xi in a metavariable's scope (elimMVarDeps) or a let
\ between the xi: not ported.
T{ xk 1 ?n lf-meta-mk-lambda xaj 2 fk lf-meta-mk-lambda
   -> -1 outcome-unsupported -1 outcome-unsupported }T

\ ---- Pins of the fe1c-3 review (2026-11-13).
\ Offsets and values are unsigned cells: 2^63, 2^64 - 1 and sums past
\ 2^63 are values; a sum past 2^64 has no cell (unsupported).
1 62 lshift constant q62
: sum3 ( -- t ) q62 ofnat q62 ofnat hadd q62 ofnat hadd ;
T{ sum3 lf-meta-eval-nat -> q62 3 * true outcome-ok }T
T{ succ ?h q62 ofnat hadd q62 ofnat hadd q62 ofnat hadd app lf-meta-offset
   -> ?h q62 3 * 1+ true outcome-ok }T
T{ own-mark succ ?h app max-n 1+ nlit dq ?h inst max-n ofnat same own-back
   -> true outcome-ok true }T
T{ own-mark succ ?h app -1 nlit dq ?h inst -2 ofnat same own-back -> true outcome-ok true }T
T{ succ ?h 1 63 lshift ofnat hadd app 5 nlit dq ?h free? -> false outcome-ok true }T
T{ -1 nlit 1 nlit nat-add lf-meta-eval-nat -> 0 false outcome-unsupported }T
T{ fk -1 nlit nat-add succ swap app lf-meta-offset nip nip nip -> outcome-unsupported }T
T{ succ fk app -1 nlit nat-add lf-meta-offset nip nip nip -> outcome-unsupported }T
\ evalNat takes HAdd.hAdd only with instHAdd Nat instAddNat.
: inst-x ( -- inst ) l0 1 s" instHAdd" cn nat app fx app ;
T{ inst-x 2 nlit 3 nlit hadd-by lf-meta-eval-nat -> 0 false outcome-ok }T
\ Universe lists: == compares every level; isDefEq pair by pair, false
\ when one list ends first. HAdd.hAdd at two levels: proof irrelevance's
\ isProp of its type now gets its binders' levels through whnfD
\ (outParam, infer.fs, branch s2-tactics), then false, as Lean; a
\ definition with one list too long is unfolded on one side only (lazy
\ delta, S2 merge A: deltaDefinition's level count), then its levels
\ differ: false, as Lean.
: hadd-c ( l -- t ) >r l0 l0 r> 3 s" HAdd.hAdd" cn ;
T{ l0 hadd-c lv1 hadd-c lf-meta-eqv l0 hadd-c lv1 hadd-c dq
   -> false outcome-ok false outcome-ok }T
: prod-c ( l -- t ) >r l0 r> 2 s" Prod.mk" cn ;
T{ l0 prod-c lv1 prod-c dq l0 prod-c l0 1 s" Prod.mk" cn dq -> false outcome-ok false outcome-ok }T
T{ l0 1 s" OfNat.ofNat" cn l0 l0 2 s" OfNat.ofNat" cn dq -> false outcome-ok }T
\ String literals by their text.
: slit ( c-addr u -- t ) lf-str-new made drop ;
T{ s" ab" slit s" ab" slit dq s" ab" slit s" ac" slit dq -> true outcome-ok false outcome-ok }T
T{ s" ab" slit s" ab" slit lf-meta-eqv s" ab" slit s" ac" slit lf-meta-eqv
   -> true outcome-ok false outcome-ok }T
\ ?n =?= n + k: first-order approximation without arguments fails (no
\ unfolding needed), and processAssignment' asks whnf, whose reduceNat?
\ has no value for ?n (withNatValue, S2 merge B): false, as Lean.
T{ ?n ?n fk nat-add dq ?n free? -> false outcome-ok true }T
\ checkAssignment: ?n in an xi's type, in a metavariable's type, through
\ a delayed assignment; ?z's context less j is a prefix of ?n's.
T{ ?n xq 1 fk chk -> fk false outcome-ok }T
\ Each xi's answer counts, not only the last's (review reuse-1a M2).
create xqk 2 cells allot  fq xqk !  fk xqk cell+ !
create xkq 2 cells allot  fk xkq !  fq xkq cell+ !
T{ ?n xqk 2 fk chk ?n xkq 2 fk chk -> fk false outcome-ok fk false outcome-ok }T
T{ ?n xs 0 ?w chk rot drop -> false outcome-ok }T
T{ own-mark ?d ?n 0 lf-mvar-delay ?n xs 0 ?d chk rot drop own-back
   -> outcome-ok false outcome-ok }T
T{ ctx-off ?n xs 1 ?z chk ?n xs 0 ?z chk rot drop
   -> ?z true outcome-ok false outcome-ok }T
\ Under ctxApprox Lean would give ?z a smaller context: not ported.
T{ ctx-on ?n xs 0 ?z chk rot drop ctx-off
   -> false outcome-unsupported }T
\ A stale metavariable, a free variable no longer in the context.
: stale ( -- mvar ) ?n lf-term-first@ ?n lf-term-second@ 1+ lf-mvar-leaf must ;
T{ stale xs 0 fk chk rot drop ?n xs 0 fdead chk rot drop
   -> false outcome-invalid false outcome-invalid }T
\ A quasi-pattern (k is in ?t's scope) needs isTypeCorrect: unsupported.
T{ ?t fk app succ fk app lf-defeq-elab lf-defeq-quasi or with-flags
   -> false outcome-unsupported }T
\ processAssignment' after a level comparison that failed on a level
\ metavariable (Sort (?u + 1) against Prop): unsupported, never retried.
: rec-prop ( -- t ) rec nat l0 sort lam app eqab app nat l0 sort 0 bv lam lam app zero app ;
T{ ?M rec-prop dq ?M free? -> false outcome-unsupported true }T
\ At reducible transparency an implicit argument is compared at implicit
\ (withImplicitConfig), where Nat.add and Nat.mul are delta candidates
\ (lazy delta, S2 merge A: neither constant unfolds, false); at reducible
\ they are not (false).
: refl-of ( name u -- t ) 0 -rot cn refl ;
T{ lf-tr-reducible lf-defeq-mode! s" Nat.add" refl-of s" Nat.mul" refl-of dq
   0 s" Nat.add" cn 0 s" Nat.mul" cn dq lf-tr-default lf-defeq-mode!
   -> false outcome-ok false outcome-ok }T
\ The instance argument of k + x compared at implicit: instHAdd Nat
\ instAddNat unfolds there to its constructor (true); at reducible alone
\ the two instances differ with a definition at the head (the hint table:
\ unsupported).
: hadd-mk ( -- inst ) l0 l0 l0 3 s" HAdd.mk" cn nat app nat app nat app
  nat nat l0 1 s" Add.add" cn nat app 0 s" instAddNat" cn app 1 bv app 0 bv app lam lam app ;
: inst-nat ( -- inst ) l0 1 s" instHAdd" cn nat app 0 s" instAddNat" cn app ;
T{ lf-tr-reducible lf-defeq-mode! inst-nat fk fx hadd-by hadd-mk fk fx hadd-by dq
   inst-nat hadd-mk dq lf-tr-default lf-defeq-mode! -> true outcome-ok false outcome-unsupported }T
\ isDefEqMVarSelf: a read-only ?t (one depth deeper) is false even under
\ constApprox.
T{ deeper ?t fk app ?t fx app lf-defeq-elab lf-defeq-const or with-flags
   shallower -> false outcome-ok }T
\ Unification hints: a failure with a definition at the head might match
\ a hint. With data of Init alone (this slice's, elab-init-only?), whose
\ one hint is Not p =?= p -> False, a side whnf makes no Not application
\ has none: false, as Lean (branch s2-tactics); data of another library
\ (its modules counted two here, then put back): unsupported, never false.
: hint-dq ( -- flag outcome )
  lf-tr-reducible lf-defeq-mode! 0 s" Nat.add" cn fk dq lf-tr-default lf-defeq-mode! ;
T{ elab-init-only? hint-dq -> true false outcome-ok }T
T{ 2 elab elab-modules# ! hint-dq 1 elab elab-modules# ! -> false outcome-unsupported }T
\ 26 of Mathlib's 27 hints are keyed at a projection node (Lean's key
\ .proj; tests/front/unif-hints.lean, MF1): a side whose head is one may
\ match a hint, as may one whose head is a definition; a variable's
\ cannot.
: add-proj ( -- t ) 0 s" instAddNat" cn 0 s" Add" projn fk app fk app ;
T{ add-proj de-hint-key? 0 s" Nat.add" cn fk app de-hint-key? fk de-hint-key?
   -> true true false }T
\ Its twin, Nat.rec _ k _ ?o =?= Nat.add with the synthetic opaque ?o
\ read-only (one depth deeper), reaches isDefEqOnFailure stuck on ?o:
\ under isDefEqStuckEx the stuck signal (ExprDefEq.lean:2182) and no
\ hints, else the hints: none for data of Init alone (Nat.add's whnf is
\ no Not application), so false, as Lean (review s1-meta-a M1; branch
\ s2-tactics).
: rec-major ( major -- t ) >r rec nat nat lam app fk app nat nat fk lam lam app r> app ;
: hint-twin ( flags -- flag outcome )
  lf-tr-reducible lf-defeq-mode! deeper ?o rec-major 0 s" Nat.add" cn
  rot with-flags shallower lf-tr-default lf-defeq-mode! ;
T{ lf-defeq-elab lf-defeq-stuck or hint-twin lf-defeq-elab hint-twin
   -> false lf-meta-stuck false outcome-ok }T
\ synthPending's hook (S1 appendix D; branch s1-synth sets it) on the
\ natural ?r : Nat, whose type might be a class, stuck in the same twin
\ under isDefEqStuckEx: a hook that fills it asks for Lean's retry, not
\ ported (unsupported); one that does not leaves the stuck signal.
: synth-yes ( mvar -- flag outcome ) drop true outcome-ok ;
: synth-no ( mvar -- flag outcome ) drop false outcome-ok ;
: synth-twin ( xt -- flag outcome )
  is lf-meta-synth-pending lf-tr-reducible lf-defeq-mode! deeper ?r rec-major
  0 s" Nat.add" cn lf-defeq-elab lf-defeq-stuck or with-flags shallower
  lf-tr-default lf-defeq-mode! ['] de-synth-later is lf-meta-synth-pending ;
T{ ' synth-yes synth-twin ' synth-no synth-twin
   -> false outcome-unsupported false lf-meta-stuck }T
\ getFunInfo's kinds come from the declared type: a store binder that
\ the binder table names may be another binder's (the store shares equal
\ nodes), so unsupported, here and through isDefEqArgs.
: imp! ( pi -- pi ) dup 0 lf-binder-implicit lf-pres-binder! drop ;
nat punit tpi imp! mv-natural lf-mvar-new made constant ?imp
T{ ?imp 1 lf-meta-fun-info nip ?imp fk app ?imp fx app dq
   -> outcome-unsupported false outcome-unsupported }T
\ A constructor short of its arguments is no structure eta; a proof
\ argument is skipped (Lean's answer, though e and p.1 differ in type).
T{ fp 0 0 2 s" Prod.mk" cn nat app nat app fa app dq -> false outcome-ok }T
T{ fi fe app fi fp 0 proj app dq -> true outcome-ok }T

\ ---- Lazy delta (S2 merge A, defeq-delta.fs; check_defeq.py compares the
\ same cases with pinned Lean). One side unfolds (outParam Type, either
\ side); a reducible side first (outParam ?n against Nat.add k x assigns
\ ?n, never unfolding Nat.add, which has a `_sunfold`); two names: class
\ projections unpacked to the other side's head (packedInstanceOf?),
\ either side, through two of them, with an assignment; one name: two
\ applications by their arguments first (tryHeuristic: Nat.add ?n x
\ against Nat.add k x), two constants at other levels both unfolded
\ (false); the side whose unfolding has the other's head alone (id Nat
\ (Nat.add ?n x) against Nat.add k x); a false answer leaves nothing
\ assigned; Nat.add's `_sunfold` reached: unsupported (merge B).
: outp ( t -- t' ) >r lv1 1 s" outParam" cn r> app ;
: outp2 ( t -- t' ) >r lv2 1 s" outParam" cn r> app ;
: add-add ( a b -- t ) >r >r l0 1 s" Add.add" cn nat app 0 s" instAddNat" cn app r> app r> app ;
: id1 ( t -- t' ) >r lv1 1 s" id" cn nat app r> app ;
: assigns? ( flag outcome mvar t -- flag outcome same? ) >r inst r> same ;
T{ lv1 sort outp2 lv1 sort dq lv1 sort lv1 sort outp2 dq -> true outcome-ok true outcome-ok }T
T{ own-mark ?n outp fk fx nat-add dq ?n fk fx nat-add assigns? own-back clean?
   -> true outcome-ok true true }T
T{ fk fx hadd fk fx add-add dq fk fx add-add fk fx hadd dq fk fx hadd fk fx nat-add dq
   -> true outcome-ok true outcome-ok true outcome-ok }T
T{ own-mark ?n fx hadd fk fx add-add dq ?n fk assigns? own-back clean? -> true outcome-ok true true }T
T{ own-mark ?n fx nat-add fk fx nat-add dq ?n fk assigns? own-back clean?
   -> true outcome-ok true true }T
T{ lv1 1 s" id" cn lv2 1 s" id" cn dq -> false outcome-ok }T
T{ own-mark ?n fx nat-add id1 fk fx nat-add dq ?n fk assigns? own-back clean?
   -> true outcome-ok true true }T
T{ ?n outp nat dq ?n free? clean? nat outp fk dq -> false outcome-ok true true false outcome-ok }T
\ (k + x =?= x + k: Nat.add's smart unfolding is stuck on x, false as Lean;
\ S2 merge B.)
T{ fk fx hadd fx fk hadd dq clean? -> false outcome-ok true }T
\ Fuel: too few steps is exhausted, nothing left assigned; the
\ transparency of the call is back after it.
T{ 4 lf-defeq-fuel! ?n fx hadd fk fx add-add dq ?n free? clean? 0 lf-defeq-fuel!
   -> false outcome-exhausted true true }T
T{ lf-tr-implicit lf-defeq-mode! lv1 sort outp2 lv1 sort dq lf-defeq-mode
   lf-tr-default lf-defeq-mode! -> true outcome-ok lf-tr-implicit }T

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
\ Through isDefEqArgs, under binders, and an assignment abstracted over
\ j (mkLambdaFVars): every path that allocates.
: args-pair ( -- t s ) fu ?h app fu fk app ;
: lam-pair ( -- t s ) nat ?t 0 bv app lam nat succ 0 bv app lam ;
: abs-pair ( -- t s ) ?t fj app succ fk fj nat-add app ;
T{ ' offset-pair refusals-sound? fulls @ 0> -> true true }T
T{ ' eta-pair refusals-sound? fulls @ 0> -> true true }T
T{ ' args-pair refusals-sound? fulls @ 0> -> true true }T
T{ ' lam-pair refusals-sound? fulls @ 0> -> true true }T
T{ ' abs-pair refusals-sound? fulls @ 0> -> true true }T
\ Through lazy delta: unfolding, whnfCore and the unpacked instance.
: delta-pair ( -- t s ) ?h fx hadd fk fx add-add ;
T{ ' delta-pair refusals-sound? fulls @ 0> -> true true }T
T{ own-mark args-pair dq own-back own-mark lam-pair dq own-back own-mark abs-pair dq own-back
   -> true outcome-ok true outcome-ok true outcome-ok }T
\ A rebuilt binder keeps its name and kind, or the call answers full
\ (instantiateMVars and instantiate1 copy the binder table's entry). The
\ new binder node is the first one past the table's room, so its entry
\ needs the heap, which each scan refuses in turn.
nat ?h tpi imp! constant pi-h
nat 1 bv tpi imp! constant pi-1
424242 nlit constant v1  434343 nlit constant v2
variable filler  5000000 filler !
: next-held? ( -- flag ) lf-term-base lf-term-count @ + lf-pres-held? ;
: to-edge ( -- ) begin next-held? while filler @ nlit drop 1 filler +! repeat ;
: implicit? ( t -- flag ) lf-pres-binder@ if nip lf-binder-implicit = else false then ;
: kept? ( t outcome -- flag )
  dup outcome-full = if 2drop true else ok? swap implicit? and then ;
: refused-inst ( k -- t outcome )
  own-mark ?h v1 lf-mvar-assign drop heap-refusals ! pi-h lf-instantiate-mvars
  0 heap-refusals ! own-back ;
: refused-i1 ( k -- t outcome )
  heap-refusals ! pi-1 v2 lf-meta-instantiate1 0 heap-refusals ! ;
: copies-sound? ( xt -- flag ) to-edge true 300 1 do i 2 pick execute kept? and loop nip ;
T{ ' refused-inst copies-sound? ' refused-i1 copies-sound? -> true true }T
T{ 0 refused-inst drop implicit? 0 refused-i1 drop implicit? clean? -> true true true }T
T{ own-mark offset-pair dq ?h free? own-back -> true outcome-ok false }T
\ A call frees what it allocates (its slabs keep their room).
T{ own-mark live-blocks @ offset-pair dq 2drop live-blocks @ = own-back clean? -> true true }T
\ The fed input as loading left it (S1 §1, trust point 3).
T{ lf-input-intact? -> true }T

\ kabstract's heads (review C3 of 2026-11-18): a literal by its value, as
\ Lean's HeadIndex .lit, also when the store shares no node (authoring
\ runs); a string by its text.
require ../../src/front/kabstract.fs
false lf-term-sharing!
: lit-of ( u -- t ) lf-hterm-cell 0= abort" lit" drop ;
: heads-apart ( t1 t2 -- same? apart? ) 2dup <> >r kab-heads= r> ;
T{ 2 lit-of 2 lit-of heads-apart 2 lit-of 3 lit-of kab-heads= -> true true false }T
T{ s" ab" slit s" ab" slit heads-apart s" ab" slit s" b" slit kab-heads=
   -> true true false }T
\ Every Sort is one head, HeadIndex .sort (review F2 of 2026-11-18): two
\ symbolic Sorts in nodes of their own, a concrete one against a symbolic
\ one, and Prop against Type; no Sort is a literal's or a pi's head.
: ssort ( level -- t ) lf-term-symbolic-sort 0= abort" sort" ;
: csort ( level -- t ) lf-term-sort 0= abort" sort" ;
T{ 0 ssort 0 ssort heads-apart 0 csort 0 ssort kab-heads= 0 ssort 0 csort kab-heads=
   -> true true true true }T
T{ 0 csort 1 csort heads-apart 0 csort 0 lit-of kab-heads= 2 lit-of 1 ssort kab-heads=
   -> true true false false }T
true lf-term-sharing!

bye

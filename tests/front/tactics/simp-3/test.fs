\ Unit tests of simp group 3 (plan row FE9, docs/design/TACTIC_SIMP.md
\ slices SL1b and SL2): src/front/simp/main.fs's binder visits
\ (simpLambda, simpForall, simpArrow), telescope.fs's lf-locals-mark,
\ lf-locals-back and lf-binder-local, and infer.fs's instantiation before
\ a lambda's type is closed, over the simp slice and its format-4 data,
\ by the classes of docs/development/TEST_COVERAGE_REVIEW.md:
\ 1. outcomes: a lambda (one and two binders) with and without a proof
\    (funext, the newest variable first); a ∀ whose domain is a
\    proposition, kept (forall_congr) or rewritten (forall_prop_domain_
\    congr, not supported yet); a ∀ that is no proposition (dsimp, not
\    supported yet); a goal with a binder through the tactic's text;
\ 2. interfaces: the binder visit's scope (the view and the local context
\    as they were after a run and after a throw below a binder);
\ 3. resources: every heap allocation of a binder walk refused in turn,
\    and sm-xs limited in turn: the answer or full.
\ The tactic's end-to-end runs against pinned Lean are check.py's.
\ Nothing here accepts a theorem: only the kernel's check does.
include ../../../support/heap-watch.fs
require ../../../support/tester.fs
include ../../../support/meta-sweeps.fs
require ../../../../src/load/checker.fs
require ../../../../src/load/front.fs
require ../../../../src/cli/check-lf.fs
require ../../../support/tactic-text.fs
decimal

4000000 lf-term-capacity! drop  100000 lf-cref-capacity! drop
T{ s" tests/front/simp-slice.ndjson" true lfc-library-open -> outcome-ok }T
lf-author-begin
T{ s" tests/front/simp-slice.elab.ndjson" lfc-elab-file! lfc-elab-read lfc-rooms
   -> outcome-ok outcome-ok }T
: made ( x outcome -- x ) ok? 0= abort" simp-3: not made" ;
: nat ( -- t ) s" Nat" lf-mk-const0 ;
: binder ( type c-addr u -- fvar )
  lfa-intern swap lf-lctx-local made tuck swap 0 lf-local-new made
  lf-mctx-view swap lf-view-push made lf-mctx-view! ;
: decl ( c-addr u -- d ) lfa-intern lf-menv-find made ;
: simp ( e -- e' h ) lf-simp-max-steps lf-simp ;
: simp-outcome ( e -- outcome ) ['] simp catch dup if nip lf-meta-outcome else nip nip then ;
: head? ( e c-addr u -- flag ) rot lf-meta-head -rot lf-meta-const-named? ;
: add-hyp ( h -- ) false ['] lf-simp-add-term catch abort" simp-3: no rule" ;
: with-self ( -- ) lf-simp-set-new s" eq_self" decl true lf-simp-add-decl ;

\ ---- 1. simpLambda. fun x => x + 0 (from Nat.add_zero's statement) is
\ fun x => x by Nat.add_zero, an rfl theorem: no proof. fun x => x = a
\ with h : a = b is fun x => x = b, by funext (fun x => congrArg (Eq x)
\ h); two binders, funext (fun x => funext (fun y => ..)), the outer for
\ x. A body nothing rewrites: the lambda itself, no proof.
nat s" x" binder constant x0   nat s" y" binder constant y0
nat s" a" binder constant a0   nat s" b" binder constant b0
a0 b0 lf-mk-eq s" h" binder constant h0
create x-cell x0 ,   create xy-cells x0 , y0 ,
: plus0 ( fvar -- e )
  >r s" Nat.add_zero" decl lf-menv-type rp@ 1 lf-meta-instantiate-forall made
  r> drop lf-eq? drop rot drop drop ;
: lam-x ( -- e ) x0 plus0 x-cell 1 lf-mk-lambda-fvars ;
: id-x ( -- e ) x0 x-cell 1 lf-mk-lambda-fvars ;
: with-rfl ( -- ) with-self s" Nat.add_zero" decl true lf-simp-add-decl ;
: with-h ( -- ) with-self h0 add-hyp ;
: x=a ( cells n -- e ) x0 a0 lf-mk-eq -rot lf-mk-lambda-fvars ;
: x=b ( cells n -- e ) x0 b0 lf-mk-eq -rot lf-mk-lambda-fvars ;
T{ with-rfl lam-x simp swap id-x lf-meta-eqv drop -> lf-simp-none true }T
T{ with-h x-cell 1 x=a simp swap x-cell 1 x=b lf-meta-eqv drop swap s" funext" head?
   -> true true }T
T{ with-h id-x simp swap id-x lf-meta-eqv drop -> lf-simp-none true }T
\ Two binders by definition: fun x y => x + 0 is fun x y => x. With a
\ proof, the outer funext's mkAppM must unify β x with fun y => ..'s
\ type, a unification LeanForth's does not do yet: unsupported.
: xy+0 ( -- e ) x0 plus0 xy-cells 2 lf-mk-lambda-fvars ;
: xy-x ( -- e ) x0 xy-cells 2 lf-mk-lambda-fvars ;
T{ with-rfl xy+0 simp swap xy-x lf-meta-eqv drop -> lf-simp-none true }T
T{ with-h xy-cells 2 x=a simp-outcome -> outcome-unsupported }T

\ ---- 1. simpForall. A domain that is a proposition: ∀ hp : p, hp = hp
\ is ∀ hp : p, True (forall_congr of eq_self); with q : Prop and the rule
\ p = q the domain has a proof: forall_prop_domain_congr, not supported
\ yet (unsupported). A ∀ that is no proposition, ∀ n, n = n -> Nat:
\ dsimp, not supported yet.
x0 x0 lf-mk-eq lf-infer! constant prop
prop s" p" binder constant p0   prop s" q" binder constant q0
p0 s" hp" binder constant hp0   create hp-cell hp0 ,
: all-hp ( -- e ) hp0 hp0 lf-mk-eq hp-cell 1 lf-mk-forall-fvars ;
T{ with-self all-hp simp-outcome -> outcome-unsupported }T
p0 q0 lf-mk-eq s" hpq" binder constant hpq0
T{ with-self hpq0 add-hyp all-hp simp-outcome -> outcome-unsupported }T
\ ∀ x, x = a with h: ∀ x, x = b by forall_congr; the arrow x = a -> p:
\ x = b -> p by implies_congr, its domain alone rewritten.
: all-x=a ( -- e ) x0 a0 lf-mk-eq x-cell 1 lf-mk-forall-fvars ;
T{ with-h all-x=a simp s" forall_congr" head? swap x0 b0 lf-mk-eq x-cell 1 lf-mk-forall-fvars
   lf-meta-eqv drop -> true true }T
: dom-arrow ( -- e ) x0 a0 lf-mk-eq p0 lf-term-pi lf-made! ;
T{ with-h dom-arrow simp s" implies_congr" head? swap lf-term-first@ x0 b0 lf-mk-eq
   lf-meta-eqv drop -> true true }T
create n-cell x0 ,
: all-n ( -- e ) x0 x0 lf-mk-eq nat lf-term-pi lf-made! n-cell 1 lf-mk-forall-fvars ;
T{ with-self all-n simp-outcome -> outcome-unsupported }T

\ ---- 2. The scope: after a run below binders, and after a throw below
\ one (a let variable in a lambda's body, reduceFVar's case not ported),
\ the view and the local context are as they were.
: scope@ ( -- count view ) lf-lctx-count @ lf-mctx-view ;
: scope-kept? ( count view xt -- flag outcome )
  catch dup if lf-meta-outcome else drop outcome-ok then
  >r scope@ rot = -rot = and r> ;
: lam-xy ( -- e' ) with-rfl xy+0 simp drop ;
: lam-x-h ( -- e' ) with-h x-cell 1 x=a simp drop ;
: run-lam ( -- ) lam-x-h drop lam-xy drop ;
T{ scope@ ' run-lam scope-kept? -> true outcome-ok }T
nat x0 s" l" lfa-intern false lf-let-decl-new lf-mctx-view! constant l0
: lam-l ( -- e ) l0 x-cell 1 lf-mk-lambda-fvars ;
: run-let ( -- ) with-self lam-l simp 2drop ;
T{ scope@ ' run-let scope-kept? -> true outcome-unsupported }T

\ ---- 3. The binder walks of fun x => x = a with h (a proof) and of
\ fun x y => x + 0 (two variables): sm-xs limited in turn (the answer
\ or full); then, for the walk with the proof, every heap allocation
\ refused in turn (the rules made before: the answer or full).
x-cell 1 x=a constant lam-a   xy+0 constant lam-xy0
: both ( -- e' ) lam-a simp drop drop lam-xy0 simp drop ;
: caught ( xt -- e' outcome ) catch ?dup if lf-meta-outcome 0 swap else outcome-ok then ;
: p-lam ( x -- e' outcome ) drop ['] both caught ;
with-h
' sm-xs sweep-slab-xt !   T{ 0 ' p-lam slab-sweep swept? -> true }T
: lam-anew ( -- ) sm-xs sweep-slab-anew sm-acts sweep-slab-anew ;
: just-a ( -- e' ) lam-a simp drop ;
: p-lam-a ( x -- e' outcome ) drop ['] just-a caught ;
' lam-anew sweep-slabs-xt !
T{ 0 ' p-lam-a heap-sweep swept? -> true }T
' noop sweep-slabs-xt !

\ ---- 1. Through the tactic's text (each run a new authoring run: the
\ locals above are gone after it): the target ∀ a, a + 0 = a
\ (by-revert) and an arrow under a ∀ (simp-binders.lf's twins are
\ Lean's node for node, check.py); no progress below a binder (500).
T{ s" Nat explicit: a a 0 + a ="
   s" ' a by-revert by-simp-only[ ' Nat.add_zero ] by-intro: a ' True.intro by-exact"
   tactic-ran -> 0 }T
T{ s" Nat explicit: b Nat explicit: a a 0 + b = explicit: h a b ="
   s" ' h by-revert ' a by-revert by-simp-only[ ' Nat.add_zero ] by-intro: a by-intro: h ' h by-exact"
   tactic-ran -> 0 }T
T{ s" Nat explicit: b Nat explicit: c Nat explicit: d c d = explicit: h Nat explicit: a a 1 + b ="
   s" ' a by-revert by-simp-only[ ' h ]" tactic-ran lf-tac-forget -> 500 }T
\ An arrow whose domain alone is rewritten: implies_congr with Eq.refl
\ of the body.
T{ s" Nat explicit: a Nat explicit: b Nat explicit: c a c = explicit: h2 a b = explicit: h c b ="
   s" ' h by-revert by-simp-only[ ' h2 ] by-intro: h ' h by-exact" tactic-ran -> 0 }T
.( simp-3 test.fs: all tests passed) cr
bye

\ Unit tests of simp slice SL1a-1 (plan row FE9, docs/design/TACTIC_SIMP.md):
\ src/front/simp/'s types.fs, theorems.fs, rewrite.fs and main.fs over the
\ simp slice and its format-4 data, by the classes of
\ docs/development/TEST_COVERAGE_REVIEW.md:
\ 1. outcomes: an rfl theorem's rewrite with no proof, a hypothesis's with
\    its proof and the congruence proofs (congrArg, congrFun'), the set's
\    pre theorems before its post ones, an unchanged term; every refusal
\    unsupported (a nested call, a dependent argument dsimp would visit, a
\    head with @[congr] lemmas, an unassigned argument after unification,
\    a hypothesis that is no equation, steps beyond maxSteps);
\ 2. the loop's counts: steps with the cache hit, the step check before
\    the increment at the boundary;
\ 3. builders: lf-simp-trans's three cases, lf-simp-congr-fun;
\ 4. state: the frames idle and the activations empty after a THROW, the
\    set emptied, a theorem added twice kept once;
\ 5. resources: every heap allocation of a run refused in turn (full or
\    the answer).
\ The tactic's end-to-end runs are check.py's. Nothing here accepts a
\ theorem: only the kernel's check does.
include ../../../support/heap-watch.fs
require ../../../support/tester.fs
include ../../../support/meta-sweeps.fs
require ../../../../src/load/checker.fs
require ../../../../src/load/front.fs
require ../../../../src/cli/check-lf.fs
decimal

4000000 lf-term-capacity! drop  100000 lf-cref-capacity! drop
T{ s" tests/front/simp-slice.ndjson" true lfc-library-open -> outcome-ok }T
lf-author-begin
T{ s" tests/front/simp-slice.elab.ndjson" lfc-elab-file! lfc-elab-read lfc-rooms
   -> outcome-ok outcome-ok }T
: made ( x outcome -- x ) ok? 0= abort" simp-1: not made" ;
: nat ( -- t ) s" Nat" lf-mk-const0 ;
: binder ( type c-addr u -- fvar )
  lfa-intern swap lf-lctx-local made tuck swap 0 lf-local-new made
  lf-mctx-view swap lf-view-push made lf-mctx-view! ;
: decl ( c-addr u -- d ) lfa-intern lf-menv-find made ;
: code1 ( x xt -- code ) catch dup if nip then ;
: named? ( e c-addr u -- flag ) rot lf-meta-head lf-const-name -rot lf-name-dotted? ;
nat s" n" binder constant n0   nat s" a" binder constant a0
nat s" b" binder constant b0   nat s" c" binder constant c0
a0 b0 lf-mk-eq s" h1" binder constant h1   a0 c0 lf-mk-eq s" h2" binder constant h2
create n-cell n0 ,
\ n + 0, from Nat.add_zero's statement at n.
: n+0 ( -- e ) s" Nat.add_zero" decl lf-menv-type n-cell 1 lf-meta-instantiate-forall made
  lf-eq? drop rot drop drop ;
: set-of ( c-addr u -- ) lf-simp-set-new decl true lf-simp-add-decl ;
: simp ( e -- e' h ) lf-simp-max-steps lf-simp ;

\ ---- 1, 2. An rfl theorem: n + 0 is n with no proof (rfl-step-kept), in
\ four steps: n + 0, its head, n, 0; n again is a cache hit (cache-ignored).
s" Nat.add_zero" set-of
T{ n+0 simp lf-simp-steps -> n0 lf-simp-none 4 }T
\ numSteps > maxSteps before the increment: 3 lets the fourth step run, 2
\ does not (step-check-after-increment); unsupported, never Lean's error.
T{ n+0 3 lf-simp lf-simp-steps -> n0 lf-simp-none 4 }T
: steps2 ( e -- ) 2 lf-simp 2drop ;
T{ n+0 ' steps2 code1 lf-meta-outcome -> outcome-unsupported }T
\ After that THROW the frames are idle and the activations empty.
T{ sm-frames frame-busy? sm-acts slab-count -> false 0 }T
T{ n0 simp lf-simp-steps -> n0 lf-simp-none 1 }T

\ ---- 1. Hypotheses: a pre theorem before a post one (post-before-pre).
lf-simp-set-new  h1 false lf-simp-add-hyp  h2 true lf-simp-add-hyp
T{ a0 simp -> b0 h1 }T
T{ lf-simp-thms# h1 false lf-simp-add-hyp lf-simp-thms# -> 2 2 }T
T{ 0 lf-simp-thm-post? 1 lf-simp-thm-post? 1 lf-simp-thm-rfl? 1 lf-simp-thm-decl?
   -> false true false false }T
\ a = c by h1 under Eq: congrFun' (congrArg Eq h1) c (congrfun-for-congrfun').
lf-simp-set-new  h1 true lf-simp-add-hyp
: a=c ( -- e ) a0 c0 lf-mk-eq ;
T{ a=c simp s" congrFun'" named? swap b0 c0 lf-mk-eq lf-meta-eqv drop -> true true }T
T{ a=c simp nip lf-term-first@ lf-term-second@ s" congrArg" named? -> true }T
\ Nothing to rewrite: the term itself, no proof.
T{ c0 simp lf-simp-steps -> c0 lf-simp-none 1 }T

\ ---- 1. Refusals: unsupported, never an answer.
: unsupported? ( e -- flag ) ['] simp code1 lf-meta-outcome outcome-unsupported = ;
\ @Eq (Nat -> Nat) f f: the type argument is a pi, which dsimp would
\ visit (dsimp-guard-off).
nat nat lf-term-pi lf-made! s" f" binder constant f0
T{ f0 f0 lf-mk-eq unsupported? -> true }T
\ ite has @[congr] lemmas (ite_congr): unsupported (SL2).
0 lf-term-symbolic-sort lf-made! s" p" binder constant p0
s" Decidable" lf-mk-const0 p0 lf-mk-app s" i" binder constant i0
: ite-n ( -- e )
  s" ite" nat lf-level! lf-mk-const1 nat lf-mk-app p0 lf-mk-app i0 lf-mk-app n0 lf-mk-app
  n0 lf-mk-app ;
T{ ite-n unsupported? -> true }T
\ eq_true (h : p) : p = True as a rule at p: h, a proposition, is left
\ unassigned by the left side (the discharger, SL2): unsupported.
s" eq_true" set-of
: rw-post ( e -- ) lf-simp-post false lf-simp-rewrite? drop 2drop ;
T{ p0 ' rw-post code1 lf-meta-outcome -> outcome-unsupported }T
\ ite_congr: Lean's isPerm holds (its sides' metavariables unify), so
\ it is a perm theorem: unsupported (acLt, SL3d).
: add-ite-congr ( -- ) s" ite_congr" set-of ;
T{ ' add-ite-congr catch lf-meta-outcome -> outcome-unsupported }T
\ A hypothesis that is no equation (h : p), and a perm theorem.
p0 s" hp" binder constant hp0
: add-hp ( -- ) hp0 true lf-simp-add-hyp ;
T{ ' add-hp catch lf-meta-outcome -> outcome-unsupported }T
: add-comm ( -- ) s" Nat.add_comm" decl true lf-simp-add-decl ;
T{ ' add-comm catch lf-meta-outcome -> outcome-unsupported }T
\ A nested call is refused (the frames busy), unsupported.
: nested ( -- ) true sm-frames frame-depth ! n0 simp 2drop ;
T{ ' nested catch lf-meta-outcome 0 sm-frames frame-depth ! -> outcome-unsupported }T

\ ---- 3. Builders.
T{ lf-simp-none n0 h1 lf-simp-trans -> n0 h1 }T
T{ h1 n0 lf-simp-none lf-simp-trans -> n0 h1 }T
T{ h1 n0 h2 lf-simp-trans nip s" Eq.trans" named? -> true }T
T{ a=c n0 lf-simp-none c0 lf-simp-congr-fun swap n0 c0 lf-mk-app lf-meta-eqv drop
   -> lf-simp-none true }T
: congr-fun-h ( -- ) a=c n0 h1 c0 lf-simp-congr-fun 2drop ;
T{ ' congr-fun-h catch lf-meta-outcome -> outcome-unsupported }T
T{ n0 lf-simp-none lf-simp-proof s" Eq.refl" named? h1 n0 swap lf-simp-proof -> true h1 }T

\ ---- 5. Every heap allocation of a run refused in turn: full or the answer.
s" Nat.add_zero" set-of
: simp-pass ( e -- e' outcome )
  ['] simp catch ?dup 0= if drop outcome-ok exit then
  nip -1 swap dup lf-meta-thrown? 0= if throw then lf-meta-outcome ;
: slabs-anew ( -- ) sm-acts sweep-slab-anew sr-cands sweep-slab-anew sr-xs sweep-slab-anew ;
' slabs-anew sweep-slabs-xt !
T{ n+0 ' simp-pass heap-sweep nip -> 0 }T
bye

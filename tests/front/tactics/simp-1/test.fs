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
\    the answer);
\ 6. the loop's corners: reduceStep (an instantiated metavariable head, a
\    beta-redex, a raw literal, a recursor's, a matcher's or a structure
\    projection's head), the leaves (a sort, a metavariable, a let or a
\    pi refused, a proof kept), literals (Char.ofNat, OfNat.ofNat at
\    arity 3 only), the dsimp guard's kept arguments (a sort, a type
\    variable), an argument past the function's parameters, the depth
\    limit, a head no congruence of this slice takes, two candidates;
\ 7. the tactic by-simp-only[ ] through its text (tests/support/
\    tactic-text.fs): each outcome (closed by of_eq_true or True.intro,
\    a target replaced with a proof or by defeq, Lean's 500) and each
\    rule or place answering not supported yet (99).
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
\ addExtraArgs: f a from the result f (no proof), and from f = g by
\ Eq.refl (mkCongrFun's shortcut); by a hypothesis h, Lean's congrFun h a
\ is not supported yet (SL1b). A non-arrow is no arrow.
nat nat lf-term-pi lf-made! constant nat>nat
nat>nat s" g" binder constant g0
f0 g0 lf-mk-eq s" hf" binder constant hf0
: f-n ( -- e ) f0 n0 lf-mk-app ;
T{ f-n 1 g0 lf-simp-none lf-simp-extra-args swap g0 n0 lf-mk-app lf-meta-eqv drop
   -> lf-simp-none true }T
T{ f-n 1 g0 f0 lf-mk-eq-refl lf-simp-extra-args nip s" Eq.refl" named? -> true }T
: extra-h ( -- ) f-n 1 g0 hf0 lf-simp-extra-args 2drop ;
T{ ' extra-h catch lf-meta-outcome -> outcome-unsupported }T
T{ nat lf-arrow? nat>nat lf-arrow? -> false true }T

\ ---- 6. reduceStep: an instantiated metavariable head (?m := f) and a
\ beta-redex reduce, then the loop runs again; a raw literal refused.
: did ( outcome -- ) ok? 0= abort" simp-1: not done" ;
: kept? ( e -- flag h ) dup simp >r lf-meta-eqv drop r> ;
nat>nat mv-natural lf-mvar-new made constant mf  mf f0 lf-mvar-assign did
nat mv-natural lf-mvar-new made constant m1
T{ mf n0 lf-mk-app simp swap f-n lf-meta-eqv drop m1 simp -> lf-simp-none true m1 lf-simp-none }T
T{ nat n0 lf-term-lam lf-made! a0 lf-mk-app simp swap n0 lf-meta-eqv drop -> lf-simp-none true }T
: nlit ( u -- e ) lf-nat-lit made ;   \ a raw literal
T{ 5 nlit unsupported? -> true }T
\ The heads reduceRecMatcher? and reduceProjFn? would unfold: Nat.rec,
\ Nat.add's matcher, Prod.fst.
: motive1 ( -- e ) nat nat lf-term-lam lf-made! ;
T{ s" Nat.rec" nat lf-level! lf-mk-const1 motive1 lf-mk-app unsupported? -> true }T
T{ s" Nat.add.match_1" nat lf-level! lf-mk-const1 nat motive1 lf-term-lam lf-made! lf-mk-app
   unsupported? -> true }T
: zero-level ( -- l ) p0 lf-level! ;
T{ s" Prod.fst" zero-level zero-level 2 lf-mk-const nat lf-mk-app nat lf-mk-app unsupported?
   -> true }T
\ Leaves: a sort and a proof kept; a pi and a let variable refused.
T{ nat lf-infer! kept? h1 simp -> true lf-simp-none h1 lf-simp-none }T
T{ nat>nat unsupported? -> true }T
: let-binder ( type value c-addr u -- fvar )
  lfa-intern -rot lf-lctx-let made tuck swap 0 lf-local-new made
  lf-mctx-view swap lf-view-push made lf-mctx-view! ;
nat n0 s" x" let-binder constant x0
T{ x0 unsupported? -> true }T
\ Literals: Char.ofNat 65 is kept whole (one step); OfNat.ofNat at four
\ arguments is no literal (isAppOfArity 3): it is visited, and its type
\ argument, a pi, is one dsimp would visit (unsupported, not kept).
T{ s" Char.ofNat" lf-mk-const0 65 nlit lf-mk-app kept? lf-simp-steps -> true lf-simp-none 1 }T
\ OfScientific.ofScientific _ _ m _ e with m and e raw literals is
\ a literal too (isOfScientificLit); simp's slice declares no OfScientific,
\ so the term is built by name (its shape is all sm-literal? reads; its
\ type cannot be inferred, so simp itself is not run on it). With e no
\ raw literal it is no literal (review low 3 of 2026-11-25).
: raw-sci ( m e -- t ) >r >r s" OfScientific.ofScientific" lf-mk-const0 nat lf-mk-app
  nat lf-mk-app r> lf-mk-app s" Bool.true" lf-mk-const0 lf-mk-app r> lf-mk-app ;
T{ 2 nlit n0 raw-sci sm-literal? 2 nlit 3 nlit raw-sci sm-literal? -> false true }T
: ofnat-f ( -- t ) s" OfNat" zero-level lf-mk-const1 nat>nat lf-mk-app 5 nlit lf-mk-app ;
ofnat-f s" i5" binder constant i5
: five-n ( -- e )
  s" OfNat.ofNat" zero-level lf-mk-const1 nat>nat lf-mk-app 5 nlit lf-mk-app i5 lf-mk-app
  n0 lf-mk-app ;
T{ five-n unsupported? -> true }T
\ The dsimp guard keeps a sort (@Eq Prop p p) and a type variable (@Eq α
\ x x); it refuses the type argument Nat -> Nat of @id (Nat -> Nat) f n,
\ before n, an argument past id's two parameters.
T{ p0 p0 lf-mk-eq kept? -> true lf-simp-none }T
nat lf-infer! s" α" binder constant al0   al0 s" y" binder constant y0
T{ y0 y0 lf-mk-eq kept? -> true lf-simp-none }T
: id-f-n ( -- e ) s" id" nat>nat lf-level! lf-mk-const1 nat>nat lf-mk-app f0 lf-mk-app n0 lf-mk-app ;
T{ id-f-n unsupported? -> true }T
\ Decidable.decide p i: its instance's congruence kind is not fixed or eq
\ (subsingletonInst), unsupported (SL2).
T{ s" Decidable.decide" lf-mk-const0 p0 lf-mk-app i0 lf-mk-app unsupported? -> true }T
\ More visits in progress than sm-depth-max: unsupported, never Lean's error.
: deep ( -- e ) n0 200 0 do s" Nat.succ" lf-mk-const0 swap lf-mk-app loop ;
T{ deep unsupported? sm-frames frame-busy? -> true false }T
\ Two candidates (hf1 fails to unify, hf2 rewrites; hf3 and hf2 of equal
\ priority in order); a rule whose two sides are metavariables is a perm
\ theorem (Subsingleton.elim): unsupported.
f0 a0 lf-mk-app c0 lf-mk-eq s" hf1" binder constant hf1
f0 b0 lf-mk-app c0 lf-mk-eq s" hf2" binder constant hf2
f0 b0 lf-mk-app a0 lf-mk-eq s" hf3" binder constant hf3
lf-simp-set-new  hf1 true lf-simp-add-hyp  hf2 true lf-simp-add-hyp
T{ f0 b0 lf-mk-app simp -> c0 hf2 }T
lf-simp-set-new  hf2 true lf-simp-add-hyp  hf3 true lf-simp-add-hyp
T{ f0 b0 lf-mk-app simp -> c0 hf2 }T
: add-elim ( -- ) s" Subsingleton.elim" set-of ;
T{ ' add-elim catch lf-meta-outcome -> outcome-unsupported }T
\ f a, with f = g and a = b: congr's proof (both changed); with f = g as a
\ pre theorem, f a is rewritten whole, with an extra argument: Lean's
\ congrFun h a, not supported yet (SL1b).
lf-simp-set-new  hf0 true lf-simp-add-hyp  h1 true lf-simp-add-hyp
T{ f0 a0 lf-mk-app simp s" congr" named? swap g0 b0 lf-mk-app lf-meta-eqv drop -> true true }T
lf-simp-set-new  hf0 false lf-simp-add-hyp
T{ f0 a0 lf-mk-app unsupported? -> true }T
\ A hypothesis f 2 = f (OfNat.ofNat 2), 2 a raw literal, at f
\ (OfNat.ofNat 2): it unifies, and its right side is the term itself: no
\ rewrite (Lean's e == rhs).
: f-two ( -- e ) f0 2 lf-meta-nat-lit made lf-mk-app ;
f0 2 nlit lf-mk-app f-two lf-mk-eq s" ha" binder constant ha0
lf-simp-set-new  ha0 true lf-simp-add-hyp
T{ f-two kept? -> true lf-simp-none }T
\ isPerm: f (f a) = f (f b) holds two different applications below the
\ top, which Lean walks into and this port does not: unsupported; f a =
\ f b is no perm (a and b differ): a rewrite.
f0 f0 a0 lf-mk-app lf-mk-app f0 f0 b0 lf-mk-app lf-mk-app lf-mk-eq s" hff" binder constant hff0
: add-hff ( -- ) hff0 true lf-simp-add-hyp ;
T{ lf-simp-set-new ' add-hff catch lf-meta-outcome -> outcome-unsupported }T
f0 a0 lf-mk-app f0 b0 lf-mk-app lf-mk-eq s" hfab" binder constant hfab0
lf-simp-set-new  hfab0 true lf-simp-add-hyp
T{ f0 a0 lf-mk-app simp swap f0 b0 lf-mk-app lf-meta-eqv drop -> hfab0 true }T
\ f a = g a: two heads, no perm.
f0 a0 lf-mk-app g0 a0 lf-mk-app lf-mk-eq s" hfg" binder constant hfg0
lf-simp-set-new  hfg0 true lf-simp-add-hyp
T{ f0 a0 lf-mk-app simp nip -> hfg0 }T
\ synthesizeArgs: b and c of Nat.eq_add_of_sub_eq (a = c + b) are left
\ unassigned but need nothing; its hypothesis b ≤ a needs the discharger.
s" Nat.eq_add_of_sub_eq" set-of
T{ n0 unsupported? -> true }T
\ Std.le_refl._simp_1 at n <= n: its instance of the class Std.Refl is
\ left unassigned, which instance synthesis would fill (SL1a-2).
s" Std.le_refl._simp_1" set-of
: n<=n ( -- e ) s" LE.le" zero-level lf-mk-const1 nat lf-mk-app s" instLENat" lf-mk-const0
  lf-mk-app n0 lf-mk-app n0 lf-mk-app ;
T{ n<=n unsupported? -> true }T
\ preprocess's shapes (simp/preprocess.fs, SL1b): And, Iff and Not by
\ their heads and arity; p (a variable) is none of them.
T{ p0 p0 s" And" lf-mk-const0 -rot 2 lf-mk-app-n lf-and-app? p0 lf-and-app? -> true false }T
T{ p0 p0 s" Iff" lf-mk-const0 -rot 2 lf-mk-app-n lf-iff-app? p0 lf-mk-not lf-not-app? -> true true }T
T{ p0 lf-iff-app? p0 lf-not-app? -> false false }T
\ isClass?: Nat is no class, Decidable p is one (synth-class-quick).
T{ nat sr-class? s" Decidable" lf-mk-const0 p0 lf-mk-app sr-class? -> false true }T
\ The dsimp guard's question: an rfl theorem among the candidates.
T{ nat lf-simp-post lf-simp-rfl-match? -> false }T
s" Nat.add_zero" set-of
T{ n+0 lf-simp-post lf-simp-rfl-match? -> true }T
\ rfl-only passes over a theorem without the rfl flag (eq_self).
s" eq_self" set-of
: n=n ( -- e ) n0 n0 lf-mk-eq ;
T{ n=n lf-simp-post true lf-simp-rewrite? n=n lf-simp-post false lf-simp-rewrite? nip nip
   -> false true }T

\ ---- 5. Every heap allocation of a run refused in turn: full or the answer.
s" Nat.add_zero" set-of
: simp-pass ( e -- e' outcome )
  ['] simp catch ?dup 0= if drop outcome-ok exit then
  nip -1 swap dup lf-meta-thrown? 0= if throw then lf-meta-outcome ;
: slabs-anew ( -- ) sm-acts sweep-slab-anew sr-cands sweep-slab-anew sr-xs sweep-slab-anew ;
' slabs-anew sweep-slabs-xt !
T{ n+0 ' simp-pass heap-sweep nip -> 0 }T

\ ---- Review of 2026-11-25 (M2, low 2). visitPostContinue: a post
\ rewrite's result is simplified again, so h1 : a = b, then h3 : b = c
\ take a to c (single-pass).
b0 c0 lf-mk-eq s" h3" binder constant h3
lf-simp-set-new  h1 true lf-simp-add-hyp  h3 true lf-simp-add-hyp
T{ a0 simp drop -> c0 }T
\ A proof is kept whole, even one with an argument a rule rewrites:
\ Eq.refl (n + 0) (proof-visited).
s" Nat.add_zero" set-of
T{ n+0 lf-mk-eq-refl kept? -> true lf-simp-none }T

\ ---- 7. by-simp-only[ ] through its text: closed by of_eq_true or
\ True.intro, a target replaced with a proof (h) or by defeq (Nat.add_zero
\ an rfl theorem), Lean's 500.
' noop sweep-slabs-xt !
T{ s" Nat explicit: n n 0 + 0 + n =" s" by-simp-only[ ' Nat.add_zero ]" tactic-ran -> 0 }T
T{ s" True" s" by-simp-only[ ]" tactic-ran -> 0 }T
: abc ( -- c-addr u )
  s" Nat explicit: a Nat explicit: b Nat explicit: c a b = explicit: h b c = explicit: k a c =" ;
T{ abc s" by-simp-only[ ' h ] ' k by-exact" tactic-ran -> 0 }T
T{ abc s" a b = ' h by-have: x by-simp-only[ ' x ] ' k by-exact" tactic-ran -> 0 }T
T{ s" Nat explicit: n Nat explicit: m n m = explicit: k n 0 + m ="
   s" by-simp-only[ ' Nat.add_zero ] ' k by-exact" tactic-ran -> 0 }T
T{ s" Nat explicit: n n n 1 + =" s" by-simp-only[ ]" tactic-ran -> 500 }T
lf-tac-forget
\ Not supported yet (99): a definition to unfold, a term. A variable that
\ is no proposition is Lean's 501 (tests/front/tactics/simp-2/ has at[ ]).
: ran99 ( c-addr u c-addr' u' -- flag ) tactic-ran 99 = lf-tac-forget ;
T{ s" Nat explicit: a a 0 Nat.add a =" s" by-simp-only[ ' Nat.add ]" ran99 -> true }T
T{ s" Nat explicit: a a a =" s" by-simp-only[ ' a ]" tactic-ran lf-tac-forget -> 501 }T
T{ abc s" by-simp-only[ << ' h >> ] ' k by-exact" ran99 -> true }T
\ preprocess: h : b = a with <- is Eq.symm h (a = c becomes b = c, which
\ k closes); h : a <= b is eq_true h
\ (with and_self: closed); h : True (True = True, a perm theorem), a
\ constant with <-, an And or Iff of True and True (perm theorems again)
\ answer 99; a proposition with <- is Lean's 502; a Not hypothesis is a
\ rule since SL1b (simp/preprocess.fs; True closed as ever).
T{ s" Nat explicit: a Nat explicit: b Nat explicit: c b a = explicit: h b c = explicit: k a c ="
   s" by-simp-only[ ' h <- ] ' k by-exact" tactic-ran -> 0 }T
T{ s" Nat explicit: a Nat explicit: b a b ≤ explicit: h a b ≤ a b ≤ ∧"
   s" by-simp-only[ ' h ' and_self ]" tactic-ran -> 0 }T
T{ s" True explicit: h True" s" by-simp-only[ ' h ]" ran99 -> true }T   \ True = True: a perm theorem
T{ s" Nat explicit: n n 0 + n =" s" by-simp-only[ ' Nat.add_zero <- ]" ran99 -> true }T
T{ s" True explicit: h True" s" by-simp-only[ ' h <- ]" tactic-ran lf-tac-forget -> 502 }T
T{ s" Nat explicit: a a 0 = Not explicit: h True" s" by-simp-only[ ' h ]" tactic-ran -> 0 }T
T{ s" True True ∧ explicit: h True" s" by-simp-only[ ' h ]" ran99 -> true }T
T{ s" True True ↔ explicit: h True" s" by-simp-only[ ' h ]" ran99 -> true }T
\ A theorem LeanForth's text declared has no defeq tag recorded (99).
: text-ran ( c-addr u -- code ) lf-author-begin lf-author-text drop lf-author-code ;
T{ s" theorem z0 Nat explicit: n n 0 + n = := by by-simp-only[ ' Nat.add_zero ] end z0 theorem t Nat explicit: m m 0 + m = := by by-simp-only[ ' z0 ] end t"
   text-ran -> 99 }T
lf-tac-forget
.( simp-1 test.fs: all tests passed) cr
bye

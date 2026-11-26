\ Unit tests of simp slice SL1a-2 (plan row FE9, docs/design/TACTIC_SIMP.md)
\ and plan row 9.4.8z2(e): src/front/simp/goal.fs (simpGoal), the goal
\ words it adds to meta-tactic/assert.fs (lf-goal-replace-local-decl-defeq,
\ lf-goal-assert-hyps), lctx-views.fs's lf-local-refvar and lf-view-refvar,
\ term-eqv.fs's lf-meta-equal? and by-simp-only[ ] at[ ] with its rule
\ errors, over the simp slice and its format-4 data, by the classes of
\ docs/development/TEST_COVERAGE_REVIEW.md:
\ 1. outcomes: a hypothesis replaced by defeq (the term, once
\    instantiated, the old free variable: Lean's), with a proof
\    (asserted, the old one cleared), closed by False with and without a
\    proof, True kept, several locations, the target after them, no
\    progress (Lean's 500, once for all locations), Lean's 501 and 502;
\    not supported (99): a let rule, at[ * ], a hypothesis something
\    depends on;
\ 2. interfaces: lf-meta-equal?'s answers (the same node, eqv terms with
\    and without binders, different terms, a dead term), lf-local-refvar's
\    and lf-view-refvar's refusals, replaceLocalDeclDefEq's two equal cases
\    (before and after instantiation), assertHypotheses of none;
\ 3. resources: every heap allocation of a replacement refused in turn,
\    and every local's record (lv-locals) of a run: full or the answer.
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
: made ( x outcome -- x ) ok? 0= abort" simp-2: not made" ;
: did ( outcome -- ) ok? 0= abort" simp-2: not done" ;
: nat ( -- t ) s" Nat" lf-mk-const0 ;
: binder ( type c-addr u -- fvar )
  lfa-intern swap lf-lctx-local made tuck swap 0 lf-local-new made
  lf-mctx-view swap lf-view-push made lf-mctx-view! ;
: code1 ( x xt -- code ) catch dup if nip then ;
: outcome-of ( i*x xt -- outcome ) catch dup if lf-meta-outcome then ;

\ ---- 2. lf-meta-equal?: the same node; eqv terms without binders (two
\ nodes); different terms; eqv terms with a binder (unsupported); a dead
\ term (invalid).
nat s" a" binder constant a0   nat s" b" binder constant b0
: a=b ( -- e ) a0 b0 lf-mk-eq ;
T{ a=b dup lf-meta-equal? -> true outcome-ok }T
T{ a=b a=b 2dup = >r lf-meta-equal? r> -> true outcome-ok false }T
T{ a=b b0 a0 lf-mk-eq lf-meta-equal? -> false outcome-ok }T
: lam ( -- e ) nat nat lf-term-lam lf-made! ;
T{ lam lam 2dup = >r lf-meta-equal? nip r> -> outcome-unsupported false }T
T{ -1 a0 lf-meta-equal? nip -> outcome-invalid }T

\ ---- 2. lf-local-refvar, lf-view-refvar: a dead free variable or an
\ unknown local refused, a free variable the view does not hold refused;
\ else the local in place on the new free variable, its name kept.
: ctx ( -- view ) lf-mctx-view ;
: local-of ( fvar -- local ) ctx swap lf-view-local-of ;
nat lf-lctx-local made constant x1
T{ a0 local-of -1 lf-local-refvar nip -> outcome-invalid }T
T{ -1 x1 lf-local-refvar nip -> outcome-invalid }T
T{ ctx x1 a0 lf-view-refvar nip -> outcome-invalid }T
T{ ctx a0 x1 lf-view-refvar made dup 0 lf-view-fvar swap 0 lf-view-local lf-local-name
   -> x1 a0 local-of lf-local-name }T

\ ---- 1, 2. replaceLocalDeclDefEq: h : a + 0 = b in the goal ?g : a = b.
create a-cell a0 ,
\ a + 0, from Nat.add_zero's statement at a.
: a+0 ( -- e ) s" Nat.add_zero" lfa-intern lf-menv-find made lf-menv-type a-cell 1
  lf-meta-instantiate-forall made lf-eq? drop rot drop drop ;
a+0 b0 lf-mk-eq s" h" binder constant h0
: goal ( -- g ) a=b 0 ctx lf-goal-new made ;
\ The same type, before or after instantiation (?m := a): the goal itself.
T{ goal dup h0 dup lf-fvar-type lf-goal-replace-local-decl-defeq = -> true }T
nat mv-natural lf-mvar-new made constant m1  m1 a+0 lf-mvar-assign did
T{ goal dup h0 m1 b0 lf-mk-eq lf-goal-replace-local-decl-defeq = -> true }T
\ a = b: a new goal whose context holds h' : a = b in h's place, named h;
\ the goal assigned, and once the new goal is h' its value is h (Lean's
\ term, the same free variable).
goal constant g1
g1 h0 a=b lf-goal-replace-local-decl-defeq constant g1'
: h' ( -- fvar ) g1' lf-goal-view 2 lf-view-fvar ;
T{ g1' g1 = h' h0 = h' lf-fvar-type a=b lf-meta-eqv drop g1 lf-goal-assigned?
   -> false false true true }T
T{ g1' lf-goal-view 2 lf-view-local lf-local-name h0 local-of lf-local-name = -> true }T
T{ g1' h' lf-mvar-assign did g1 lf-instantiate! -> h0 }T
\ k : h = h depends on h: not supported yet (unsupported).
h0 h0 lf-mk-eq s" k" binder constant k0
: dep ( -- ) goal h0 a=b lf-goal-replace-local-decl-defeq drop ;
T{ ' dep outcome-of -> outcome-unsupported }T
\ assertHypotheses of no hypothesis: the goal itself.
T{ goal dup 0 lf-goal-assert-hyps = -> true }T
\ ---- 3. Every heap allocation of a replacement refused in turn (its
\ frames given back first): replaced (0) or full.
: replace-anew ( -- ) mat-frames sweep-slab-anew mat-cells sweep-slab-anew ;
' replace-anew sweep-slabs-xt !
: replace-k ( -- ) goal k0 a=b lf-goal-replace-local-decl-defeq drop ;
: p-replace ( x -- 0 outcome ) drop ['] replace-k outcome-of 0 swap ;
T{ 0 ' p-replace heap-sweep swept? -> true }T
' noop sweep-slabs-xt !
lf-tac-forget

\ ---- 1. by-simp-only[ ] at[ ] through its text.
T{ s" Nat explicit: a Nat explicit: b a 0 + b = explicit: h a b ="
   s" by-simp-only[ ' Nat.add_zero ] at[ h ] ' h by-exact" tactic-ran -> 0 }T
T{ s" Nat explicit: a Nat explicit: b Nat explicit: c a b = explicit: h a 0 + c = explicit: k b c ="
   s" by-simp-only[ ' h ' Nat.add_zero ] at[ k ] ' k by-exact" tactic-ran -> 0 }T
T{ s" Nat explicit: a Nat explicit: b Nat explicit: c a b = explicit: h a 0 + c = explicit: k b 0 + c ="
   s" by-simp-only[ ' h ' Nat.add_zero ] at[ k |- ] ' k by-exact" tactic-ran -> 0 }T
\ Closed by False with a proof (k : (a = b) = False) and without one.
T{ s" Nat explicit: a Nat explicit: b a b = False = explicit: k a b = explicit: h a 0 ="
   s" by-simp-only[ ' k ] at[ h ]" tactic-ran -> 0 }T
T{ s" Nat explicit: a False explicit: h a 0 =" s" by-simp-only[ ] at[ h ]" tactic-ran -> 0 }T
\ Rewritten with itself (the rule h is no .fvar origin): h : True, kept;
\ exact h then fails with Lean's Type mismatch (twin w-at-self).
T{ s" Nat explicit: a Nat explicit: b a b = explicit: h b a = explicit: k b a ="
   s" by-simp-only[ ' h ] at[ h ] ' k by-exact" tactic-ran -> 0 }T
T{ s" Nat explicit: a Nat explicit: b a b = explicit: h a b ="
   s" by-simp-only[ ' h ] at[ h ] ' h by-exact" tactic-ran lf-tac-forget -> 96 }T
\ Two hypotheses with proofs, asserted at once in order (k1 then k2).
T{ s" Nat explicit: a Nat explicit: b Nat explicit: c Nat explicit: d a b = explicit: h a 0 + c = explicit: k1 a d = explicit: k2 b c ="
   s" by-simp-only[ ' h ' Nat.add_zero ] at[ k1 k2 ] ' k1 by-exact" tactic-ran -> 0 }T
\ Two locations, one unchanged; a hypothesis closed by False before the
\ target; the target closed after the hypotheses.
T{ s" Nat explicit: a Nat explicit: b Nat explicit: c a b = explicit: h a c = explicit: k1 b c = explicit: k2 b c ="
   s" by-simp-only[ ' h ] at[ k1 k2 ] ' k1 by-exact" tactic-ran -> 0 }T
T{ s" Nat explicit: a Nat explicit: b a b = False = explicit: k a b = explicit: h a a ="
   s" by-simp-only[ ' k ] at[ h |- ]" tactic-ran -> 0 }T
T{ s" Nat explicit: a Nat explicit: b a 0 + b = explicit: h a 0 + a 0 + ="
   s" by-simp-only[ ' Nat.add_zero ] at[ h |- ]" tactic-ran -> 0 }T
\ No progress: Lean's 500, once for two locations.
T{ s" Nat explicit: a Nat explicit: b a b = explicit: h b a = explicit: k a b ="
   s" by-simp-only[ ' Nat.add_zero ] at[ h k ]" tactic-ran lf-tac-forget -> 500 }T
\ Lean's 501 (a variable that is no proposition), 502 (a proposition with
\ <-); a let rule and at[ * ] not supported yet (99); an unknown location
\ is Lean's 455 (after the set).
T{ s" Nat explicit: a a a =" s" by-simp-only[ ' a ]" tactic-ran lf-tac-forget -> 501 }T
T{ s" Nat explicit: a Nat explicit: b a b ≤ explicit: h a b ≤"
   s" by-simp-only[ ' h <- ]" tactic-ran lf-tac-forget -> 502 }T
T{ s" Nat explicit: a a a =" s" Nat Nat.zero by-let: x by-simp-only[ ' x ]" tactic-ran
   lf-tac-forget -> 99 }T
T{ s" Nat explicit: a Nat explicit: b a 0 + b = explicit: h a b ="
   s" by-simp-only[ ' Nat.add_zero ] at[ * ] ' h by-exact" tactic-ran lf-tac-forget -> 99 }T
T{ s" Nat explicit: a a a =" s" by-simp-only[ ] at[ z ]" tactic-ran lf-tac-forget -> 455 }T

\ ---- 3. Every local's record refused in turn (each text empties
\ lv-locals at its start): the answer or full.
' lv-locals sweep-slab-xt !
: p-mixed ( x -- code outcome )
  drop s" Nat explicit: a Nat explicit: b Nat explicit: c a b = explicit: h c 0 + b = explicit: k1 a c = explicit: k2 c b ="
  s" by-simp-only[ ' h ' Nat.add_zero ] at[ k1 k2 |- ] ' k1 by-exact" text-full ;
T{ 0 ' p-mixed slab-sweep swept? -> true }T
lf-tac-forget
.( simp-2 test.fs: all tests passed) cr
bye

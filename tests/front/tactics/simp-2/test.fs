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
\    not supported (99): a let rule, a hypothesis something depends on;
\    at[ * ] (SL1b) and lf-goal-nondep-prop-hyps;
\ 2. interfaces: lf-meta-equal?'s answers (the same node, eqv terms with
\    and without binders, different terms, a dead term), lf-local-refvar's
\    and lf-view-refvar's refusals, replaceLocalDeclDefEq's two equal cases
\    (before and after instantiation), assertHypotheses of none;
\ 3. resources: every heap allocation of a replacement and of
\    lf-goal-simp refused in turn, simpGoal's frames limited in turn, and
\    every local's record (lv-locals) of a run: full or the answer.
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
: equal-apart ( a b -- flag outcome same? ) 2dup = >r lf-meta-equal? r> ;
T{ a=b dup lf-meta-equal? -> true outcome-ok }T
T{ a=b a=b equal-apart -> true outcome-ok false }T
T{ a=b b0 a0 lf-mk-eq lf-meta-equal? -> false outcome-ok }T
: lam ( -- e ) nat nat lf-term-lam lf-made! ;
T{ lam lam equal-apart rot drop -> outcome-unsupported false }T
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
\ simpGoal on an assigned goal: checkNotAssigned's refusal (invalid).
: simp-g1 ( -- ) g1 false 0 h0 lf-run+ lf-goal-simp drop ;
T{ ' simp-g1 outcome-of -> outcome-invalid }T
\ ---- 3. Every heap allocation of a replacement refused in turn (its
\ frames given back first): replaced (0) or full.
: replace-anew ( -- ) mat-frames sweep-slab-anew mat-cells sweep-slab-anew ;
' replace-anew sweep-slabs-xt !
: replace-k ( -- ) goal k0 a=b lf-goal-replace-local-decl-defeq drop ;
: p-replace ( x -- 0 outcome ) drop ['] replace-k outcome-of 0 swap ;
T{ 0 ' p-replace heap-sweep swept? -> true }T
' noop sweep-slabs-xt !
lf-tac-forget

\ ---- SL1b 1, 2. lf-simp-add-term on hypotheses no LeanForth text states
\ yet: h : ∀ n, n + 0 = n (Nat.add_zero's statement) is fun n => h n, and
\ rewrites a + 0 to a by (fun n => h n) a, a beta-redex Lean keeps; a pi
\ whose binder is unknown (no record), unsupported. h : a = b -> a + 0 = a is a
\ conditional rule, refused (unsupported) when tried: its condition needs
\ the discharger (slice SL2). h : ¬ (x = true) of a Bool x: Lean's
\ Bool.of_not_eq_true, not supported yet.
: decl ( c-addr u -- d ) lfa-intern lf-menv-find made ;
: simp ( e -- e' h ) lf-simp-max-steps lf-simp ;
: add-term ( h inv -- outcome ) ['] lf-simp-add-term catch dup if nip nip lf-meta-outcome then ;
: simp-outcome ( e -- outcome ) ['] simp catch dup if nip lf-meta-outcome else nip nip then ;
s" Nat.add_zero" decl lf-menv-type s" hz" binder constant hz0
T{ lf-simp-set-new hz0 false add-term lf-simp-thms# -> outcome-ok 1 }T
T{ 0 lf-simp-thm-proof dup lf-term-lam? swap lf-term-second@ lf-term-first@ hz0 = -> true true }T
T{ a+0 simp drop a0 = -> true }T
T{ a+0 simp nip dup lf-term-first@ lf-term-lam? swap lf-term-second@ a0 = -> true true }T
: nat->a+0=a ( -- t ) nat a+0 a0 lf-mk-eq lf-term-pi lf-made! ;
nat->a+0=a s" hu" binder constant hu0
T{ lf-simp-set-new hu0 false add-term lf-simp-thms# -> outcome-unsupported 0 }T
\ An And of two pis: h.1's local cut before h.2's opens, so each proof is
\ fun n => h.i n, its argument the bound variable.
: add0 ( -- t ) s" Nat.add_zero" decl lf-menv-type ;
s" And" lf-mk-const0 add0 add0 2 lf-mk-app-n s" hm" binder constant hm0
: bound-arg? ( t -- flag ) lf-simp-thm-proof lf-term-second@ lf-term-second@ lf-term-bvar? ;
T{ lf-simp-set-new hm0 false add-term lf-simp-thms# 0 bound-arg? 1 bound-arg?
   -> outcome-ok 2 true true }T
\ Inverted: fun n => Eq.symm (h n), whose left side is a bare variable.
T{ lf-simp-set-new hz0 true add-term 0 lf-simp-thm-proof lf-term-second@ lf-meta-head
   s" Eq.symm" lf-meta-const-named? -> outcome-ok true }T
: a=b->a+0=a ( -- t ) a=b a+0 a0 lf-mk-eq lf-term-pi lf-made! s" hc" lfa-intern lf-binder-named ;
a=b->a+0=a s" hi" binder constant hi0
T{ lf-simp-set-new hi0 false add-term -> outcome-ok }T
T{ a+0 simp-outcome -> outcome-unsupported }T
s" Bool" lf-mk-const0 s" x" binder constant x0
x0 s" Bool.true" lf-mk-const0 lf-mk-eq lf-mk-not s" hb" binder constant hb0
T{ lf-simp-set-new hb0 false add-term -> outcome-unsupported }T
\ The same below a binder, h : ∀ x : Bool, ¬ x = true: the walk throws
\ after it opened x's local, which it drops (lf-with-new-locals): the
\ view and the local context as they were.
create x-cell x0 ,
x0 s" Bool.true" lf-mk-const0 lf-mk-eq lf-mk-not x-cell 1 lf-mk-forall-fvars
s" hv" binder constant hv0
T{ lf-lctx-count @ lf-mctx-view lf-simp-set-new hv0 false add-term >r lf-mctx-view =
   swap lf-lctx-count @ = r> -> true true outcome-unsupported }T
\ The walk's locals dropped at its end: the context as it was.
T{ lf-mctx-view lf-view-count lf-simp-set-new hz0 false add-term drop lf-mctx-view lf-view-count
   = -> true }T

\ ---- SL1b 3. The walk on h : ∀ n, n + 0 = n with each of its slabs
\ limited in turn (spp-work, spp-xs, spp-out: the answer or
\ full), and every heap allocation of the walk refused in turn.
: p-forall ( x -- 0 outcome ) drop lf-simp-set-new hz0 false add-term 0 swap ;
' spp-work sweep-slab-xt !   T{ 0 ' p-forall slab-sweep swept? -> true }T
' spp-xs sweep-slab-xt !     T{ 0 ' p-forall slab-sweep swept? -> true }T
' spp-out sweep-slab-xt !    T{ 0 ' p-forall slab-sweep swept? -> true }T
: spp-anew ( -- ) spp-work sweep-slab-anew spp-xs sweep-slab-anew spp-out sweep-slab-anew ;
' spp-anew sweep-slabs-xt !
T{ 0 ' p-forall heap-sweep swept? -> true }T
' noop sweep-slabs-xt !

\ ---- 3. lf-goal-simp at h : a + 0 = b with the rule hz : ∀ n, n + 0 = n
\ (the smallest goal with a proof): its frames (sg-frames) limited in
\ turn, and every heap allocation refused in turn (each run in the same
\ context, the frames given back first): the answer (the new goal's
\ context's size) or full.
: simp-h ( -- n ) goal false 0 h0 lf-run+ lf-goal-simp lf-goal-view lf-view-count ;
: p-simp ( x -- n outcome )
  drop ['] simp-h catch ?dup if lf-meta-outcome 0 swap else outcome-ok then ;
: simp-anew ( -- )
  sg-frames sweep-slab-anew mat-frames sweep-slab-anew mat-cells sweep-slab-anew
  sweep-view-anew ;
lf-simp-set-new hz0 false add-term drop
' sg-frames sweep-slab-xt !   T{ 0 ' p-simp slab-sweep swept? -> true }T
sweep-keep-view ' simp-anew sweep-slabs-xt !
T{ 0 ' p-simp heap-sweep swept? -> true }T
' noop sweep-slabs-xt !
lf-simp-set-new

\ ---- SL1b 4. getNondepPropHyps (meta-tactic/goal.fs): in a context of
\ its own, a, b, h : a = b, k : h = h, c : Nat (no proposition, used by
\ nothing: no candidate), h is used by k's type, so k alone;
\ a target naming k, none. A let l : a = b := h and an implementation
\ detail d : k = k added: l is no candidate (it has a value), nor d, whose
\ use of k does not count (Lean skips details).
0 lf-mctx-view!
nat s" a" binder constant na   nat s" b" binder constant nb
na nb lf-mk-eq s" h" binder constant nh   nh nh lf-mk-eq s" k" binder constant nk
nat s" c" binder drop
: goal2 ( -- g ) na nb lf-mk-eq 0 ctx lf-goal-new made ;
: nondep1 ( goal -- n x ) lf-goal-nondep-prop-hyps dup run-count swap 0 run@ ;
T{ goal2 nondep1 -> 1 nk }T
T{ nk nk lf-mk-eq 0 ctx lf-goal-new made lf-goal-nondep-prop-hyps -> 0 }T
na nb lf-mk-eq nh s" l" lfa-intern false lf-let-decl-new lf-mctx-view! drop
: detail ( type c-addr u -- fvar )
  lfa-intern swap lf-lctx-local made tuck swap lf-local-aux-decl lf-local-new made
  lf-mctx-view swap lf-view-push made lf-mctx-view! ;
nk nk lf-mk-eq s" d" detail drop
T{ goal2 nondep1 -> 1 nk }T

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
\ <-); a let rule not supported yet (99); an unknown location
\ is Lean's 455 (after the set).
T{ s" Nat explicit: a a a =" s" by-simp-only[ ' a ]" tactic-ran lf-tac-forget -> 501 }T
T{ s" Nat explicit: a Nat explicit: b a b ≤ explicit: h a b ≤"
   s" by-simp-only[ ' h <- ]" tactic-ran lf-tac-forget -> 502 }T
T{ s" Nat explicit: a a a =" s" Nat Nat.zero by-let: x by-simp-only[ ' x ]" tactic-ran
   lf-tac-forget -> 99 }T
T{ s" Nat explicit: a Nat explicit: b a 0 + b = explicit: h a b ="
   s" by-simp-only[ ' Nat.add_zero ] at[ * ] ' h by-exact" tactic-ran -> 0 }T
\ at[ * ] (SL1b): every hypothesis that is a proposition nothing else
\ depends on, then the target; no progress anywhere is Lean's 500.
T{ s" Nat explicit: a Nat explicit: b Nat explicit: c a b = explicit: h a 0 + c = explicit: k a 0 + c ="
   s" by-simp-only[ ' h ' Nat.add_zero ] at[ * ] ' k by-exact" tactic-ran -> 0 }T
T{ s" Nat explicit: a False explicit: h a 0 =" s" by-simp-only[ ] at[ * ]" tactic-ran -> 0 }T
T{ s" Nat explicit: a Nat explicit: b a b = explicit: h b a ="
   s" by-simp-only[ ' Nat.add_zero ] at[ * ]" tactic-ran lf-tac-forget -> 500 }T
\ The hypotheses before the target (Lean's order; probe p48): k becomes
\ False and closes the goal before the target, a ∀ simp cannot enter yet
\ (99), is reached.
T{ s" Nat explicit: a Nat explicit: b Nat explicit: c a b ≤ ¬ explicit: h a b ≤ explicit: k c 0 + c ="
   s" ' c by-revert by-simp-only[ ' h ] at[ k |- ]" tactic-ran -> 0 }T
\ Changed by definition, then closed by a False hypothesis: the goal so
\ far is the one closed (p32).
T{ s" Nat explicit: a Nat explicit: b a 0 + b = explicit: h False explicit: k a b ="
   s" by-simp-only[ ' Nat.add_zero ] at[ h k ]" tactic-ran -> 0 }T
\ The old hypothesis cleared: once the new k is cleared, nothing proves
\ a = c (Lean: assumption fails).
T{ s" Nat explicit: a Nat explicit: b Nat explicit: c a b = explicit: h a c = explicit: k a c ="
   s" by-simp-only[ ' h ] at[ k ] ' k by-clear by-assumption" tactic-ran lf-tac-forget -> 381 }T
\ The same hypothesis twice, changed by definition (p30): the second pass
\ meets the hypothesis the first put in h's place.
T{ s" Nat explicit: a Nat explicit: b a 0 + b = explicit: h a b ="
   s" by-simp-only[ ' Nat.add_zero ] at[ h h ] ' h by-exact" tactic-ran -> 0 }T
\ The pass-1 review's case: h, a rule, changed by definition first.
T{ s" Nat explicit: a Nat explicit: b Nat explicit: c a 0 + 2 * b = explicit: h a 0 + 2 * c = explicit: j a 2 * c ="
   s" by-simp-only[ ' Nat.add_zero ' h ] at[ h j ] ' j by-exact" tactic-ran -> 0 }T
T{ s" Nat explicit: a a a =" s" by-simp-only[ ] at[ z ]" tactic-ran lf-tac-forget -> 455 }T

\ ---- 3. Every local's record refused in turn (each text empties
\ lv-locals at its start): the answer or full.
' lv-locals sweep-slab-xt !
: p-mixed ( x -- code outcome )
  drop s" Nat explicit: a Nat explicit: b Nat explicit: c a b = explicit: h c 0 + b = explicit: k1 a c = explicit: k2 c b ="
  s" by-simp-only[ ' h ' Nat.add_zero ] at[ k1 k2 |- ] ' k1 by-exact" text-full ;
T{ 0 ' p-mixed slab-sweep swept? -> true }T
lf-tac-forget

\ ---- SL1b 1. Rules from hypotheses that are no equation (simp/
\ preprocess.fs, Lean's preprocess), through their text: an Iff (both
\ ways), a Not and a Ne (at k, which becomes False), an And (h.2 closes
\ the goal; h.1 before h.2 when both rewrite a), Lean's 503 for <- on a
\ Not or a Ne, and an And inside an And not supported yet (99).
T{ s" Nat explicit: a Nat explicit: b a b ≤ b a ≤ ↔ explicit: h b a ≤ explicit: hq a b ≤"
   s" by-simp-only[ ' h ] ' hq by-exact" tactic-ran -> 0 }T
T{ s" Nat explicit: a Nat explicit: b a b ≤ b a ≤ ↔ explicit: h a b ≤ explicit: hq b a ≤"
   s" by-simp-only[ ' h <- ] ' hq by-exact" tactic-ran -> 0 }T
T{ s" Nat explicit: a Nat explicit: b a b ≤ ¬ explicit: h a b ≤ explicit: k b 0 ="
   s" by-simp-only[ ' h ] at[ k ]" tactic-ran -> 0 }T
T{ s" Nat explicit: a Nat explicit: b a b ≠ explicit: h a b = explicit: k b 0 ="
   s" by-simp-only[ ' h ] at[ k ]" tactic-ran -> 0 }T
T{ s" Nat explicit: a Nat explicit: b a b ≤ b a ≤ ∧ explicit: h b a ≤"
   s" by-simp-only[ ' h ]" tactic-ran -> 0 }T
T{ s" Nat explicit: a Nat explicit: b Nat explicit: c Nat explicit: d a b = a c = ∧ explicit: h b d = explicit: k a d ="
   s" by-simp-only[ ' h ] ' k by-exact" tactic-ran -> 0 }T
T{ s" Nat explicit: a Nat explicit: b Nat explicit: c Nat explicit: d a b = a c = ∧ explicit: h c d = explicit: k a d ="
   s" by-simp-only[ ' h ] ' k by-exact" tactic-ran lf-tac-forget -> 96 }T
T{ s" Nat explicit: a Nat explicit: b a b ≤ ¬ explicit: h a b ≤ False ="
   s" by-simp-only[ ' h <- ]" tactic-ran lf-tac-forget -> 503 }T
T{ s" Nat explicit: a Nat explicit: b a b ≠ explicit: h a b = False ="
   s" by-simp-only[ ' h <- ]" tactic-ran lf-tac-forget -> 503 }T
T{ s" Nat explicit: a Nat explicit: b Nat explicit: c a b ≤ b c ≤ c a = ∧ ∧ explicit: h c b ≤"
   s" by-simp-only[ ' h ]" tactic-ran lf-tac-forget -> 99 }T

\ ---- SL1b 3. The text's walk with each of its slabs limited in turn
\ (spp-work, spp-out: the answer or full).
: p-and ( x -- code outcome )
  drop s" Nat explicit: a Nat explicit: b a b ≤ b a ≤ ∧ explicit: h b a ≤"
  s" by-simp-only[ ' h ]" text-full ;
' spp-work sweep-slab-xt !  T{ 0 ' p-and slab-sweep swept? -> true }T   lf-tac-forget
' spp-out sweep-slab-xt !   T{ 0 ' p-and slab-sweep swept? -> true }T   lf-tac-forget
.( simp-2 test.fs: all tests passed) cr
bye

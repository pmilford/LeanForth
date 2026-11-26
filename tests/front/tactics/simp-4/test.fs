\ Unit tests of simp group 4, pass 1 (plan row FE9, docs/design/
\ TACTIC_SIMP.md; the plan .claude/work/briefs/simp-group-4-architect.md
\ sections 3 and 4): the re-entrant walk (src/front/simp/main.fs's
\ lf-simp-nested and lf-simp-preserved; rewrite.fs's frames and its
\ discharger hook, lf-simp-discharge), over the simp slice and its
\ format-4.1 data, by the classes of docs/development/
\ TEST_COVERAGE_REVIEW.md:
\ 1. outcomes: a nested walk inside a running one shares the cache and
\    the step count (the steps of the plain run, its visits reordered);
\    lf-simp-preserved gives the cache back (the outer walk visits the
\    term again); outside a walk invalid;
\ 2. state: the outer walk's frames and activations intact (its result
\    the plain run's), the rewrite's candidates and metavariables kept
\    across a discharger's nested walk (the second candidate tried after
\    the first fails; the first's proof its own after it succeeds);
\ 3. resources: every heap allocation of a nested run refused in turn,
\    the slabs given back first: full or the answer.
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
: made ( x outcome -- x ) ok? 0= abort" simp-4: not made" ;
: nat ( -- t ) s" Nat" lf-mk-const0 ;
: binder ( type c-addr u -- fvar )
  lfa-intern swap lf-lctx-local made tuck swap 0 lf-local-new made
  lf-mctx-view swap lf-view-push made lf-mctx-view! ;
: decl ( c-addr u -- d ) lfa-intern lf-menv-find made ;
: simp ( e -- e' h ) lf-simp-max-steps lf-simp ;
: thrown ( x xt -- outcome ) catch ?dup if nip lf-meta-outcome else 2drop outcome-ok then ;
: thrown1 ( x xt -- outcome ) catch ?dup if nip lf-meta-outcome else outcome-ok then ;
: thrown2 ( x y xt -- outcome ) catch ?dup if nip nip lf-meta-outcome else outcome-ok then ;
nat s" x" binder constant x0   nat s" a" binder constant a0
nat s" b" binder constant b0   nat s" c" binder constant c0
nat nat lf-term-pi lf-made! s" f" binder constant f0
create x-cell x0 ,
\ x + 0, from Nat.add_zero's statement at x.
: x+0 ( -- e ) s" Nat.add_zero" decl lf-menv-type x-cell 1 lf-meta-instantiate-forall made
  lf-eq? drop rot drop drop ;
: f(x+0) ( -- e ) f0 x+0 lf-mk-app ;
: with-add0 ( -- ) lf-simp-set-new s" Nat.add_zero" decl true lf-simp-add-decl ;

\ ---- 1. A nested walk, plugged where the walk asks for an
\ application's congruence (simp/main.fs's hook sm-congr) the first
\ time: the application's argument simplified first by xt, then the
\ congruence as ever.
' sm-congr defer@ constant congr0
variable nest-xt   variable nest-once
: nest-arg ( e -- e ) dup lf-term-second@ nest-xt @ execute 2drop ;
: nest-congr ( e -- ... ) nest-once @ if false nest-once ! nest-arg then congr0 execute ;
: nesting ( xt -- ) nest-xt ! true nest-once ! ['] nest-congr is sm-congr ;
: plain ( -- ) congr0 is sm-congr ;
\ The plain run: f (x + 0) is f x (Nat.add_zero, rfl: no proof).
with-add0
T{ f(x+0) simp swap f0 x0 lf-mk-app lf-meta-eqv drop -> lf-simp-none true }T
lf-simp-steps constant plain-steps
x+0 simp 2drop lf-simp-steps constant arg-steps
\ Nested: the same result, the same steps (the argument's visits done by
\ the nested walk, then a cache hit), the frames idle afterwards.
' lf-simp-nested nesting
T{ f(x+0) simp swap f0 x0 lf-mk-app lf-meta-eqv drop -> lf-simp-none true }T
T{ lf-simp-steps sm-frames frame-busy? sm-acts slab-count -> plain-steps false 0 }T
\ Preserved: the nested walk's cache entries cut, so the outer walk
\ visits x + 0 again and pays its steps twice.
' lf-simp-preserved nesting
T{ f(x+0) simp swap f0 x0 lf-mk-app lf-meta-eqv drop -> lf-simp-none true }T
T{ lf-simp-steps -> plain-steps arg-steps + }T
plain
\ Outside a walk: invalid, nothing changed.
T{ x+0 ' lf-simp-nested thrown sm-frames frame-busy? -> outcome-invalid false }T
T{ x+0 ' lf-simp-preserved thrown -> outcome-invalid }T

\ ---- 2. The rewrite's frames across a discharger's nested walk. h1 : p
\ -> a = c and h2 : a = b, both keyed a, tried in that order; the
\ discharger (rewrite.fs's hook lf-simp-discharge) first simplifies
\ x + 0 (a rewrite of its own, its candidates and metavariables above
\ the outer call's), then answers: false, so h1 fails and h2 rewrites a
\ to b by h2; true with hp assigned, so a is c by h1 hp.
' lf-simp-discharge defer@ constant disch0
x0 x0 lf-mk-eq lf-infer! constant prop
prop s" p" binder constant p0   p0 s" hp" binder constant hp0
p0 s" hq" binder constant hq0   create hq-cell hq0 ,
a0 c0 lf-mk-eq hq-cell 1 lf-mk-forall-fvars s" h1" binder constant h1
a0 b0 lf-mk-eq s" h2" binder constant h2
variable disch-yes   variable disch-saw   \ the nested walk's result
: test-disch ( x type -- flag )
  drop x+0 lf-simp-nested drop disch-saw ! disch-yes @ if hp0 lf-defeq! else drop false then ;
: with-hyps ( -- ) with-add0 h1 true lf-simp-add-hyp h2 true lf-simp-add-hyp ;
: rewrite-slabs ( -- n n n ) sr-frames slab-count sr-cands slab-count sr-xs slab-count ;
' test-disch is lf-simp-discharge
with-hyps false disch-yes !
T{ a0 simp disch-saw @ -> b0 h2 x0 }T
T{ rewrite-slabs -> 0 0 0 }T
true disch-yes !
T{ a0 simp swap c0 = swap dup lf-meta-head h1 = swap lf-term-second@ hp0 = -> true true true }T
disch0 is lf-simp-discharge
\ Without a discharger (not ported yet): unsupported, as before, and
\ the rewrite's frames forgotten with the throw.
with-hyps
T{ a0 ' simp thrown rewrite-slabs -> outcome-unsupported 0 0 0 }T

\ ---- 3. Every heap allocation of a nested run refused in turn: full or
\ the answer.
: simp-pass ( e -- e' outcome )
  ['] simp catch ?dup 0= if drop outcome-ok exit then
  nip -1 swap dup lf-meta-thrown? 0= if throw then lf-meta-outcome ;
: slabs-anew ( -- )
  sm-acts sweep-slab-anew sr-frames sweep-slab-anew sr-cands sweep-slab-anew
  sr-xs sweep-slab-anew ;
: nested-pass ( e -- e' outcome ) ['] lf-simp-nested nesting simp-pass plain ;
' slabs-anew sweep-slabs-xt !
with-add0
T{ f(x+0) ' nested-pass heap-sweep nip -> 0 }T
' noop sweep-slabs-xt !

\ ---- 4. The default set (simp/default-set.fs) on the slice's format-4.1
\ data. Its roots are made, none built; a rewrite builds the one it
\ queries: x + 0 is x by Nat.add_zero, an rfl lemma (no proof), its keys
\ recomputed once and found the record's.
: rec-of ( c-addr u -- i )   \ the data's lemma record of a theorem
  lfa-intern lf-menv-data-decl drop
  simp-lemma-count 0 do dup i simp-lemma-proof = if drop i unloop exit then loop drop -1 ;
: or-key ( -- k ) s" or_self" rec-of simp-lemma-keys drop ;
lf-simp-default
T{ lf-simp-default? lf-simp-thms# x+0 simp -> true 0 x0 lf-simp-none }T
T{ lf-simp-thms# 0> lf-simp-post or-key over lf-dtree-root drop swap lf-dtree-root-trie
   -> true -1 }T
\ A rule added later (a bracket lemma) forces its root first and goes in
\ after the root's values: or_self, already the data's value, is replaced
\ in place, so Or's root holds the data's ten values and no new record.
: or-root ( -- node ) lf-simp-post or-key over lf-dtree-root drop swap lf-dtree-root-trie ;
lf-simp-default
T{ s" or_self" decl true lf-simp-add-decl or-root 0< lf-simp-thms# lf-simp-post lf-dtree-vals#
   -> false 10 10 }T
\ A left-out lemma reached in candidate order: unsupported (True ∨ False:
\ or_false, which the slice lacks, comes before true_or); one the library
\ has the record of, keys tampered with: unsupported, its record put back.
T{ -1 lf-simp-data-entry drop ' lf-simp-thm-usable thrown1 -> outcome-unsupported }T
s" Nat.add_zero" rec-of constant add0-i
: add0-keys# ( -- a-addr ) add0-i ssl ssl-value cell+ ;
T{ add0-i lf-simp-data-entry drop dup lf-simp-thm-usable sth sth-checked @ -> true }T
1 add0-keys# !
T{ add0-i lf-simp-data-entry drop ' lf-simp-thm-usable thrown1 -> outcome-unsupported }T
7 add0-keys# !
T{ add0-i simp-lemma-keys 2dup sth-keys= add0-i simp-lemma-keys 2dup 1- sth-keys= -> true false }T
\ The simprocs: x = x has a post one (reduceCtorEq, keyed on every Eq),
\ none pre; a free variable none: their guard answers unsupported where
\ one may fire, nothing for a set without simprocs.
: x=x ( -- e ) x0 x0 lf-mk-eq ;
lf-simp-default
T{ x=x true ds-any? x=x false ds-any? x0 true ds-any? -> true false false }T
T{ x=x true ' ds-guard thrown2 -> outcome-unsupported }T
\ The walk asks at the pre step: if True then x else x has reduceIte's
\ pre candidate before ite_self could rewrite it at the post step.
: ite-tt ( -- e )
  s" ite" nat lf-level! lf-mk-const1 nat lf-mk-app s" True" lf-mk-const0 lf-mk-app
  s" instDecidableTrue" lf-mk-const0 lf-mk-app x0 lf-mk-app x0 lf-mk-app ;
T{ ite-tt ' simp thrown -> outcome-unsupported }T
\ And at the post step: the default set's simprocs with no lemma at all
\ (its trees emptied by hand), x = x has reduceCtorEq's post candidate.
: no-lemmas ( -- ) simp-pre-tree lf-rix-free simp-post-tree lf-rix-free
  0 simp-pre-tree lf-rix-kind! 0 simp-post-tree lf-rix-kind! ;
lf-simp-default no-lemmas
T{ x=x ' simp thrown -> outcome-unsupported }T
\ A definition the set unfolds (Eq.ndrec): unsupported where reduceStep
\ would unfold it; not with simp only's set.
T{ s" Eq.ndrec" lf-mk-const0 sm-unfold? lf-simp-set-new s" Eq.ndrec" lf-mk-const0 sm-unfold?
   -> true false }T
T{ with-add0 x=x true ' ds-guard thrown2 -> outcome-ok }T

\ ---- 5. by-simp through its text (tests/support/tactic-text.fs): closed
\ (True; True ∧ True by and_self; a + 0 = a by Nat.add_zero and
\ eq_self; False ∨ True by or_true), Lean's 500 (False), a goal left
\ (¬True is False: the theorem's unsolved goal, 89), and not supported
\ yet (99): a left-out lemma reached (True ∨ False), a simproc's
\ candidate (a = 0 is reduceCtorEq's).
: ran ( c-addr u -- code ) s" by-simp" tactic-ran lf-tac-forget ;
T{ s" True" ran s" True True ∧" ran s" Nat explicit: a a 0 + a =" ran s" False True ∨" ran
   -> 0 0 0 0 }T
T{ s" False" ran s" True Not" ran s" True False ∨" ran -> 500 89 99 }T
T{ s" Nat explicit: a a 0 = True ∧ a 0 = ↔" ran -> 99 }T
\ Data without the default set: unsupported.
elab-reset
T{ ' lf-simp-default catch lf-meta-outcome -> outcome-unsupported }T

.( simp-4 test.fs: all tests passed) cr
bye

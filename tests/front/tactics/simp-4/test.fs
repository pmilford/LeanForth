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

.( simp-4 test.fs: all tests passed) cr
bye

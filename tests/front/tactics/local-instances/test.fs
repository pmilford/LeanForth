\ Unit tests of local instances (src/front/local-instances.fs; Forth
\ review of small-tactics-1, 2026-11-26, finding 1) over decide's slice
\ of Init in an authoring run, by the classes of docs/development/
\ TEST_COVERAGE_REVIEW.md:
\ 1. outcomes: isClass? (lf-class-whnf?) a class, none, none past whnf
\    (Ne, a projection), a class past whnf (DecidableEq), unsupported
\    under binders; through text, every instance problem of a class a
\    local instance has is not supported yet (139): a header parameter
\    (explicit or instance implicit, named inferInstance too), a
\    DecidableEq parameter, a have's local, intro's local after revert,
\    and the statement's own decide (Lean's rfl then fails); a local of
\    no class leaves the search as it was; the locals of by-let:,
\    by-have: with a term, by-obtain[, by-generalize: and by-intros are
\    marked, by-rename: keeps the mark, by-clear drops it; a class only
\    past default whnf (id) is none, isClassExpensive? being reducible;
\ 2. malformed input: none of its own (the types are the elaborator's);
\ 3. records: the local's class is the class's name in the context's
\    names, the one instances.fs's guard compares;
\ 4. interfaces: lf-local-classed keeps a local of no class as it is;
\ 5. resources: the locals' slab given room for j in turn, each run
\    through text (tests/support/meta-sweeps.fs): the answer or full;
\    every heap allocation refused in turn, a parameter of type Ne;
\ 6. state: a new copy for the mark, the local before unchanged.
\ The texts that pinned Lean accepts with its local instance are in
\ ../batch-small-1/ (u-ii-local*.lf, exit 2). Nothing here accepts a
\ theorem: only the kernel's check does.
require ../../../support/tester.fs
include ../../../support/heap-watch.fs
include ../../../support/meta-sweeps.fs
require ../../../../src/load/checker.fs
require ../../../../src/load/front.fs
require ../../../../src/cli/check-lf.fs
require ../../../support/tactic-text.fs
decimal

4000000 lf-term-capacity! drop  100000 lf-cref-capacity! drop
T{ s" tests/front/decide-slice.ndjson" true lfc-library-open -> outcome-ok }T
T{ s" tests/front/decide-slice.elab.ndjson" lfc-elab-file! lfc-elab-read lfc-rooms
   -> outcome-ok outcome-ok }T
lf-author-begin
: made ( x outcome -- x ) ok? 0= abort" local-instances test: not made" ;
: nm ( c-addr u -- name ) lfa-intern ;
: nat ( -- t ) s" Nat" lf-mk-const0 ;
: fresh ( -- ) lf-view-empty lf-mctx-view! ;
: binder ( type c-addr u -- fvar )
  nm swap lf-lctx-local made tuck swap 0 lf-local-new made
  lf-mctx-view swap lf-view-push made lf-mctx-view! ;
: local-of ( type -- local ) lf-lctx-local made 0 0 lf-local-new made ;
: class-named? ( local c-addr u -- flag ) rot lf-local-class -rot nm lf-name-same? ;
: ne ( a b -- t ) s" Ne" 2swap 2 lf-mk-app-m ;
: dec ( p -- t ) s" Decidable" rot 1 lf-mk-app-m ;
: ttrue ( -- t ) s" True" lf-mk-const0 ;
create xs 1 cells allot
: all-x ( e fvar -- t ) xs ! xs 1 lf-mk-forall-fvars ;
: answer ( type -- flag outcome ) lf-class-whnf? dup ok? if over if rot drop then then ;

\ ---- 1. isClass?: quick, past whnf, unsupported under binders.
fresh
nat s" a" binder constant fa
nat s" b" binder constant fb
nat s" x" binder constant fx
s" Prod" nat nat 2 lf-mk-app-m s" p" binder constant fp
T{ ttrue dec answer nat answer -> true outcome-ok false outcome-ok }T
T{ fa fb ne answer s" DecidableEq" nat 1 lf-mk-app-m answer
   -> false outcome-ok true outcome-ok }T
T{ fx fb ne fx all-x answer -> false outcome-unsupported }T
\ A projection of a local stays one past whnf: isClassApp? none.
T{ fp s" Prod" nm 0 lf-proj-of made answer -> false outcome-ok }T

\ ---- 3, 4, 6. lf-local-classed: the class's name; none kept as it is.
ttrue dec local-of constant ld
T{ ld lf-local-classed made dup ld <> swap s" Decidable" class-named? ld lf-local-class
   -> true true 0 }T
s" DecidableEq" nat 1 lf-mk-app-m local-of constant lq
T{ lq lf-local-classed made s" Decidable" class-named? -> true }T
fa fb ne local-of constant ln
T{ ln lf-local-classed made ln = ln lf-local-class -> true 0 }T
T{ fx fb ne fx all-x local-of lf-local-classed nip -> outcome-unsupported }T
fresh

\ ---- 1. Through text: a local instance of the class asked is not
\ supported yet (139); a local of no class leaves the search alone.
: hh ( -- c-addr u ) s" Nat explicit: a Nat explicit: b a b = explicit: h a b =" ;
: hd ( -- c-addr u ) s" Nat explicit: a Nat explicit: b a b = Decidable instance: d a b = explicit: h a b =" ;
: have-ii ( -- c-addr u ) s" a b = Decidable by-have-by: e by-infer-instance by-end ' h by-exact" ;
T{ hd have-ii tactic-ran -> 139 }T
lf-tac-forget
T{ s" Nat explicit: a Nat explicit: b a b = Decidable explicit: inferInstance a b = explicit: h a b ="
   have-ii tactic-ran -> 139 }T
lf-tac-forget
T{ s" Nat DecidableEq explicit: d Nat explicit: a Nat explicit: b a b = explicit: h a b =" have-ii
   tactic-ran -> 139 }T
lf-tac-forget
T{ s" True Decidable explicit: d True True =" s" True Decidable by-have-by: e by-infer-instance by-end by-rfl"
   tactic-ran -> 139 }T
lf-tac-forget
\ The statement's decide (Lean elaborates it with d, and rfl fails).
T{ s" True Decidable explicit: d True Decidable.decide Bool.true =" s" by-rfl" tactic-ran -> 139 }T
lf-tac-forget
\ A have's local is one (assert, then intro), and intro's after revert.
T{ hh s" a b = Decidable by-have-by: e by-infer-instance by-end a b = Decidable by-have-by: f by-infer-instance by-end ' h by-exact"
   tactic-ran -> 139 }T
lf-tac-forget
T{ s" True Decidable explicit: d True True =" s" ' d by-revert by-intro: e True Decidable by-have-by: f by-infer-instance by-end by-rfl"
   tactic-ran -> 139 }T
lf-tac-forget
\ A local of another class, or of none (Ne past whnf), changes nothing;
\ one of the class for another type is not supported yet either (the
\ guard asks the class, not the type: Lean would try d and fail).
T{ hh have-ii tactic-ran -> 0 }T
T{ s" Nat explicit: a Nat explicit: b a b ≠ explicit: k a b = explicit: h a b =" have-ii tactic-ran -> 0 }T
T{ s" Nat Inhabited explicit: i Nat explicit: a Nat explicit: b a b = explicit: h a b =" have-ii tactic-ran
   -> 0 }T
T{ s" True Decidable explicit: d Nat explicit: a Nat explicit: b a b = explicit: h a b =" have-ii tactic-ran
   -> 139 }T
lf-tac-forget

\ ---- 1, 6. The other paths that make a local (re-check of the Forth
\ review, finding 2; probes li09-li14, li18, li20 and li01 of 2026-11-26
\ against pinned Lean): by-let:'s local (a dependent let; Lean uses e),
\ by-have:'s with a term, by-obtain['s, by-generalize:'s and by-intros'
\ after revert are local instances (139: Lean uses them, or with
\ Decidable True refuses rfl), by-rename: keeps the mark (Lean uses e2)
\ and by-clear removes the local with it (accepted, as Lean); a type that
\ is a class only past whnf at default transparency is none, as id is
\ implicit_reducible (Prelude.lean:131) and isClassExpensive? runs
\ withReducible: accepted with the global instance, as Lean.
: dec-k ( -- c-addr u ) s" True Decidable.decide Bool.true = by-have-by: k by-rfl by-end ' h by-exact" ;
: hdt ( -- c-addr u ) s" Nat explicit: a Nat explicit: b True Decidable explicit: d a b = explicit: h a b =" ;
T{ hh s" True Decidable instDecidableTrue by-let: e True Decidable by-have-by: f by-infer-instance by-end ' h by-exact"
   tactic-ran -> 139 }T   lf-tac-forget
T{ hh s" True Decidable instDecidableTrue by-have: e True Decidable.decide Bool.true = by-have-by: k by-rfl by-end ' h by-exact"
   tactic-ran -> 139 }T   lf-tac-forget
T{ s" Nat explicit: a Nat explicit: b ' Eq instDecidableTrue $ Exists explicit: h2 a b = explicit: h a b ="
   s" ' h2 by-obtain[ << d _ >> ] True Decidable.decide Bool.true = by-have-by: k by-rfl by-end ' h by-exact"
   tactic-ran -> 139 }T   lf-tac-forget
T{ hh s" instDecidableTrue by-generalize: d True Decidable by-have-by: f by-infer-instance by-end ' h by-exact"
   tactic-ran -> 139 }T   lf-tac-forget
T{ hh s" instDecidableTrue by-generalize: d True Decidable.decide Bool.true = by-have-by: k by-rfl by-end ' h by-exact"
   tactic-ran -> 139 }T   lf-tac-forget
T{ hdt s" by-revert[ d ] by-intros True Decidable.decide Bool.true = by-have-by: k by-rfl by-end ' h by-exact"
   tactic-ran -> 139 }T   lf-tac-forget
T{ hdt s" True Decidable by-rename: e2 True Decidable by-have-by: e by-infer-instance by-end ' h by-exact"
   tactic-ran -> 139 }T   lf-tac-forget
T{ hdt s" ' d by-clear True Decidable.decide Bool.true = by-have-by: k by-rfl by-end ' h by-exact" tactic-ran
   -> 0 }T
T{ s" Nat explicit: a Nat explicit: b True Decidable id explicit: d a b = explicit: h a b ="
   s" True Decidable by-have-by: e by-infer-instance by-end ' h by-exact" tactic-ran -> 0 }T
T{ s" Nat explicit: a Nat explicit: b True Decidable id explicit: d a b = explicit: h a b =" dec-k
   tactic-ran -> 0 }T

\ ---- 5. Resources: the locals' slab short of room, each j in turn; every
\ heap allocation refused in turn: the answer, or full.
: p-mark ( x -- code outcome ) drop hd have-ii text-full ;
: p-ne ( x -- code outcome )
  drop s" Nat explicit: a Nat explicit: b a b ≠ explicit: k a b = explicit: h a b =" s" ' h by-exact" text-full ;
' lv-locals sweep-slab-xt !
T{ 0 ' p-mark slab-sweep swept? -> true }T
T{ 0 ' p-ne heap-sweep swept? -> true }T
lf-tac-forget
.( local-instances test.fs: all tests passed) cr

\ Unit tests of plan FE1g-1 (docs/design/FE1G_TACTICS.md §4.1, §5.7; the
\ runs these use, src/lib/runs.fs, are tests/lib/runs.fs's): local
\ declarations and views (src/front/lctx-views.fs); each
\ metavariable's own local context, its tag and kind, and their rollback
\ under marks (mvars.fs); dependencies (lf-depends-on?); goals, clear,
\ rename and the goal list of the proof state (goals.fs); the goal
\ printer's rules beyond the comparison with pinned Lean
\ (goal-print.fs; tests/front/check_goals.py compares the shared ones).
\ Classes of docs/development/TEST_COVERAGE_REVIEW.md: every outcome,
\ malformed input, stack effects (every T{ }T checks the depth),
\ resources (a refused heap, large contexts and goal lists), state and
\ rollback, regression pins. Nothing here checks a theorem.
\ The modules load under HEX, each from a HEX caller (review fe1g1 L1):
\ loading must not depend on BASE, which each restores; their numbers
\ read in decimal.
require ../support/tester.fs
require ../support/heap-watch.fs
hex require ../../src/front/lctx-views.fs base @ decimal constant base-after-views
hex require ../../src/front/mvars.fs base @ decimal constant base-after-mvars
hex require ../../src/front/goal-print.fs base @ decimal constant base-after-load
require ./goal-states.fs
T{ base-after-views base-after-mvars base-after-load -> 16 16 16 }T
T{ lf-local-inaccessible lf-local-kind-mask lf-local-flags-mask -> 16 12 31 }T
T{ mv-epoch-mask mv-room gp-depth-shown gp-depth-most -> 2147483647 16 254 255 }T

: cells. ( run -- x1 .. xn ) dup run-count 0 ?do dup i run@ swap loop drop ;
: fresh-var ( -- fvar ) nat lf-lctx-local made ;

\ ---- Locals: made from a live free variable, a name (or 0) and flags.
g-fresh
fresh-var constant x1  fresh-var constant x2  fresh-var constant x3
s" x" nm constant nx  s" y" nm constant ny  s" Inhabited" nm constant cls
x1 nx 0 lf-local-new made constant lc1
x2 nx lf-binder-implicit lf-local-inaccessible or lf-local-new made constant lc2
x3 0 lf-local-aux-decl lf-local-new made constant l3
T{ lc1 lf-local-fvar lc1 lf-local-name lc1 lf-local-flags lc1 lf-local-class -> x1 nx 0 0 }T
T{ lc2 lf-local-binder lc2 lf-local-inaccessible? lc2 lf-local-detail? -> lf-binder-implicit true false }T
T{ l3 lf-local-name l3 lf-local-detail? lc1 lf-local-detail? -> 0 true false }T
T{ x1 nx lf-local-impl-detail lf-local-new made lf-local-detail? -> true }T
\ Malformed: no free variable (a constant, no node), no name, flags
\ outside the five bits or of both kinds.
T{ nat nx 0 lf-local-new 99999 nx 0 lf-local-new -> -1 outcome-invalid -1 outcome-invalid }T
T{ x1 99999 0 lf-local-new x1 nx 32 lf-local-new -> -1 outcome-invalid -1 outcome-invalid }T
T{ x1 nx lf-local-kind-mask lf-local-new -> -1 outcome-invalid }T
T{ 99999 lf-local-valid? l3 lf-local-valid? -> false true }T
\ Renamed: a new local, the user's name, accessible; the old one stays.
lc2 ny lf-local-renamed made constant l2y
T{ l2y lf-local-name l2y lf-local-inaccessible? l2y lf-local-binder l2y lf-local-fvar
   -> ny false lf-binder-implicit x2 }T
T{ lc2 lf-local-name lc2 lf-local-inaccessible? -> nx true }T
T{ lc2 99999 lf-local-renamed 99999 ny lf-local-renamed -> -1 outcome-invalid -1 outcome-invalid }T
\ A local instance carries its class; anonymous or no name is refused.
T{ lc1 cls lf-local-instance made lf-local-class lc1 lf-local-class -> cls 0 }T
T{ lc1 0 lf-local-instance lc1 99999 lf-local-instance 99999 cls lf-local-instance
   -> -1 outcome-invalid -1 outcome-invalid -1 outcome-invalid }T
\ A free variable gone with its scratch makes no local.
lf-lctx-count @ constant lctx-mark
fresh-var constant gone  lctx-mark lf-lctx-count !
T{ gone nx 0 lf-local-new -> -1 outcome-invalid }T

\ ---- Views: pushed, found, named, erased and renamed, each a new view.
0 lc1 lf-view-push made constant v1
v1 lc2 lf-view-push made constant v12
v12 l3 lf-view-push made constant v123
T{ v123 lf-view-count v123 0 lf-view-local v123 2 lf-view-local -> 3 lc1 l3 }T
T{ v123 x2 lf-view-find v123 x3 lf-view-find v1 x3 lf-view-find -> 1 true 2 true false }T
T{ 99 x1 lf-view-find lf-view-empty x1 lf-view-find -> false false }T
T{ v123 x2 lf-view-has? v1 x3 lf-view-has? 99 x1 lf-view-has? -> true false false }T
\ A free variable once only; a local that is none.
T{ v12 x1 nx 0 lf-local-new made lf-view-push v1 99999 lf-view-push
   -> -1 outcome-invalid -1 outcome-invalid }T
\ Named: the newest accessible local of the name (lc2, inaccessible, is
\ never found by its name; a renamed one is).
T{ v123 nx lf-view-named v123 ny lf-view-named -> 0 true false }T
v12 l2y lf-view-push nip drop
x2 nx 0 lf-local-new made constant l2x
T{ v1 l2x lf-view-push made nx lf-view-named -> 1 true }T
T{ v123 99999 lf-view-named 99 nx lf-view-named -> false false }T
\ Erased: the others in order; a variable it lacks changes nothing.
v123 x2 lf-view-erase made constant v13
T{ v13 lf-view-count v13 0 lf-view-local v13 1 lf-view-local v123 lf-view-count -> 2 lc1 l3 3 }T
T{ v1 x3 lf-view-erase made v1 = 99 x1 lf-view-erase -> true -1 outcome-invalid }T
T{ v123 x1 lf-view-erase made 0 lf-view-local v123 x3 lf-view-erase made lf-view-count -> lc2 2 }T
\ Renamed in place; the old view keeps the old name.
v123 x2 ny lf-view-rename made constant v1y3
T{ v1y3 1 lf-view-local lf-local-name v1y3 1 lf-view-local lf-local-fvar v1y3 lf-view-count
   -> ny x2 3 }T
T{ v123 1 lf-view-local lf-local-name v1y3 ny lf-view-named -> nx 1 true }T
T{ v1 x2 ny lf-view-rename v123 x2 99999 lf-view-rename 99 x1 ny lf-view-rename
   -> -1 outcome-invalid -1 outcome-invalid -1 outcome-invalid }T
\ Lean's isSubPrefixOf: in the same order, others between allowed.
T{ v13 v123 lf-view-sub-prefix? v123 v13 lf-view-sub-prefix? v1 v13 lf-view-sub-prefix? -> true false true }T
T{ 0 v1 lf-view-sub-prefix? v123 v123 lf-view-sub-prefix? 99 v1 lf-view-sub-prefix? -> true true false }T
0 l3 lf-view-push made lc1 lf-view-push made constant v31
T{ v31 v123 lf-view-sub-prefix? v123 v31 lf-view-sub-prefix? -> false false }T
\ With exceptions (Lean's exceptFVars): view1's excepted locals need not
\ be in view2, wherever they stand (also last); an exception view1 lacks
\ changes nothing; none is the plain test; a negative count is false.
create exc 3 cells allot
: exc! ( fvar i -- ) cells exc + ! ;
x2 0 exc!  x3 1 exc!  99999 2 exc!
T{ v123 v13 exc 1 lf-view-sub-prefix-except? v123 v1 exc 1 lf-view-sub-prefix-except?
   -> true false }T
T{ v123 v1 exc 2 lf-view-sub-prefix-except? v13 v1 exc 1 cells + 1 lf-view-sub-prefix-except?
   -> true true }T
T{ v123 v123 exc 2 cells + 1 lf-view-sub-prefix-except? v123 v13 exc 0 lf-view-sub-prefix-except?
   -> true false }T
T{ v123 v13 exc -1 lf-view-sub-prefix-except? 99 v13 exc 1 lf-view-sub-prefix-except?
   -> false false }T
\ The plain test after one with exceptions has none (they do not linger).
T{ v123 v13 exc 1 lf-view-sub-prefix-except? v123 v13 lf-view-sub-prefix? -> true false }T

\ ---- Each metavariable's local context: the current one, or one given.
T{ lf-mctx-view nat mv-natural lf-mvar-new made lf-mvar-view -> 0 0 true }T
v13 lf-mctx-view!
nat mv-natural lf-mvar-new made constant m13
lf-view-empty lf-mctx-view!
T{ m13 lf-mvar-view m13 x1 lf-mvar-sees? m13 x2 lf-mvar-sees? -> v13 true true false }T
T{ nat mv-synthetic v12 lf-mvar-new-at made dup lf-mvar-view rot lf-mvar-kind lf-mctx-view
   -> v12 true mv-synthetic true 0 }T
\ A view that names none is refused, and the current one is kept.
T{ nat mv-natural 99 lf-mvar-new-at lf-mctx-view -> -1 outcome-invalid 0 }T
T{ 99 lf-mctx-view! nat mv-natural lf-mvar-new 0 lf-mctx-view! -> -1 outcome-invalid }T
T{ 99999 x1 lf-mvar-sees? -> false }T

\ ---- Tags and kinds, set and rolled back under a mark (the trail keeps
\ the old value); a stale metavariable, a name or kind out of range, and
\ no mark open are told apart.
nat mv-natural lf-mvar-new made constant mt
T{ mt lf-mvar-tag mt ny lf-mvar-tag! mt lf-mvar-tag -> 0 true outcome-ok ny true }T
lf-mctx-mark made constant mk
T{ mt nx lf-mvar-tag! mt mv-opaque lf-mvar-kind! mt lf-mvar-tag mt lf-mvar-kind
   -> outcome-ok outcome-ok nx true mv-opaque true }T
T{ mv-trail slab-count mk lf-mctx-rollback mt lf-mvar-tag mt lf-mvar-kind
   -> 2 outcome-ok ny true mv-natural true }T
lf-mctx-mark made constant mk2
T{ mt 0 lf-mvar-tag! mk2 lf-mctx-commit mt lf-mvar-tag mv-trail slab-count -> outcome-ok outcome-ok 0 true 0 }T
T{ mt 99999 lf-mvar-tag! mt 3 lf-mvar-kind! 99999 nx lf-mvar-tag! 99999 0 lf-mvar-kind!
   -> outcome-invalid outcome-invalid outcome-invalid outcome-invalid }T
\ Out of room on the trail: with the trail at its capacity and the heap
\ refusing, a change is full and not made.
lf-mctx-mark made constant mk3
: trail-room ( -- )
  begin mv-trail slab-count mv-trail slab-capacity < while mt nx lf-mvar-tag! must-ok repeat ;
T{ trail-room 1 heap-refusals ! mt ny lf-mvar-tag! heap-refusals @ mt lf-mvar-tag
   -> outcome-full 0 nx true }T
T{ mk3 lf-mctx-rollback mt lf-mvar-tag -> outcome-ok 0 true }T

\ ---- Dependencies (Lean's exprDependsOn): directly, through an
\ assignment, a "may" dependency of an unassigned metavariable whose
\ context holds the variable, none once a beta step drops it, and the
\ instantiation's own failure.
: fapp ( a -- t ) s" f" t-const swap t-app ;
T{ x1 fapp x1 lf-depends-on? x2 fapp x1 lf-depends-on? -> true outcome-ok false outcome-ok }T
T{ m13 x1 lf-depends-on? m13 x2 lf-depends-on? m13 fapp x3 lf-depends-on?
   -> true outcome-ok false outcome-ok true outcome-ok }T
nat mv-natural v123 lf-mvar-new-at made constant ma
T{ ma nat lf-mvar-assign ma x1 lf-depends-on? -> outcome-ok false outcome-ok }T
nat mv-natural v123 lf-mvar-new-at made constant mb
T{ mb x2 fapp lf-mvar-assign mb x2 lf-depends-on? -> outcome-ok true outcome-ok }T
nat mv-natural v123 lf-mvar-new-at made constant mf
T{ mf nat nat t-lam lf-mvar-assign mf x2 t-app x2 lf-depends-on? -> outcome-ok false outcome-ok }T
\ Under a binder: ?mf #0 instantiated to Nat (plan FE1g-4: a loose
\ argument where no binder of the value lies around it).
T{ nat mf 0 t-var t-app t-lam x2 lf-depends-on? -> false outcome-ok }T

\ ---- Goals: synthetic opaque, tagged, in a view.
g-fresh
s" h" nm constant tag-h  s" succ" nm constant tsucc  s" m" nm constant nm-m
0 nat s" a" hyp constant fa  nat s" b" hyp constant fb  constant vab
fa fb eq tag-h vab goal constant g1
T{ g1 lf-mvar-kind g1 lf-mvar-tag g1 lf-mvar-view g1 lf-goal-assigned?
   -> mv-opaque true tag-h true vab true false }T
T{ nat 0 vab lf-goal-new nip nat 99999 vab lf-goal-new nat 0 99 lf-goal-new 99999 0 vab lf-goal-new
   -> outcome-ok -1 outcome-invalid -1 outcome-invalid -1 outcome-invalid }T

\ Clear (Lean's MVarId.clear): a hypothesis nothing depends on goes, in a
\ new goal of the same type and tag, which the old one is assigned; the
\ other goals keep their contexts.
0 nat s" n" hyp constant fn  nat s" k" hyp constant fk  constant vnk
fk fk eq 0 vnk goal constant gk
fk fk eq tsucc vnk goal constant gk2
gk fn lf-goal-clear made constant gk'
T{ gk' lf-mvar-view drop lf-view-count gk' fn lf-mvar-sees? gk' fk lf-mvar-sees? -> 1 false true }T
T{ gk lf-mvar-value gk' lf-mvar-type drop gk lf-mvar-type drop = gk' lf-mvar-kind
   -> gk' true true mv-opaque true }T
T{ gk2 lf-mvar-view drop vnk = gk2 lf-goal-assigned? -> true false }T
\ Refused, invalid, nothing assigned: an assigned goal, a variable not in
\ its context, the target or another hypothesis depending on it, a let's
\ value (a have's is hidden and does not count), a metavariable in the
\ target whose context holds it (Lean's may dependency).
T{ gk fk lf-goal-clear gk' fn lf-goal-clear 99999 fn lf-goal-clear
   -> -1 outcome-invalid -1 outcome-invalid -1 outcome-invalid }T
T{ gk2 fk lf-goal-clear gk2 lf-goal-assigned? -> -1 outcome-invalid false }T
vnk fk fk eq s" hk" hyp constant fhk constant vhk
true. 0 vhk goal constant gh
T{ gh fk lf-goal-clear gh lf-goal-assigned? -> -1 outcome-invalid false }T
T{ gh fhk lf-goal-clear made lf-mvar-view drop lf-view-count -> 2 }T
vnk nat fk s" x" let-hyp drop constant vlet
true. 0 vlet goal constant gl
T{ gl fk lf-goal-clear -> -1 outcome-invalid }T
vnk nat fk s" y" have-hyp drop constant vhave
true. 0 vhave goal constant gy
T{ gy fk lf-goal-clear nip -> outcome-ok }T
nat mv-natural vnk lf-mvar-new-at made 0 vnk goal constant gm
T{ gm fk lf-goal-clear -> -1 outcome-invalid }T

\ Rename (MVarId.rename): the local renamed in a new goal; refused for an
\ assigned goal, a variable not in its context, a name that is none.
gl fn nm-m lf-goal-rename made constant gl'
T{ gl' lf-mvar-view drop 0 lf-view-local lf-local-name gl lf-goal-assigned? gl' lf-mvar-tag
   -> nm-m true 0 true }T
T{ gl fn nm-m lf-goal-rename gl' fa nm-m lf-goal-rename -> -1 outcome-invalid -1 outcome-invalid }T
T{ gl' fn 99999 lf-goal-rename 99999 fn nm-m lf-goal-rename -> -1 outcome-invalid -1 outcome-invalid }T
\ Under a mark: the rename rolled back leaves the old goal open again.
lf-mctx-mark made constant mg
T{ gk2 fn nm-m lf-goal-rename nip gk2 lf-goal-assigned? -> outcome-ok true }T
T{ mg lf-mctx-rollback gk2 lf-goal-assigned? -> outcome-ok false }T

\ ---- The goal list: opened with the root goal; set; the main goal (the
\ first not assigned, the ones before it dropped); the unsolved goals
\ (Lean's getUnsolvedGoals prunes the list); replaced and appended; a
\ list from before a reset reads as empty.
g-fresh
0 nat s" n" hyp constant fq constant vn
: tgoal ( -- goal ) fq fq eq 0 vn goal ;
tgoal constant ga  tgoal constant gb  tgoal constant gc
T{ ga lf-pst-open lf-pst-root lf-goals cells. -> outcome-ok ga ga }T
T{ 99999 lf-pst-open lf-pst-root -> outcome-invalid ga }T
: list3 ( -- list ) 0 ga run-push made gb run-push made gc run-push made ;
T{ list3 lf-goals! lf-goals cells. -> outcome-ok ga gb gc }T
T{ 99 lf-goals! lf-goals cells. -> outcome-invalid ga gb gc }T
T{ ga nat lf-mvar-assign lf-main-goal lf-goals cells. -> outcome-ok gb outcome-ok gb gc }T
T{ list3 lf-goals! gc nat lf-mvar-assign lf-goals-unsolved swap cells. lf-goals cells.
   -> outcome-ok outcome-ok outcome-ok gb gb }T
T{ gb nat lf-mvar-assign lf-main-goal lf-goals cells. -> outcome-ok -1 outcome-invalid gb }T
\ A delayed assignment does not count (Lean's isAssigned).
tgoal constant gdl  tgoal constant gpend
T{ gdl gpend 0 lf-mvar-delay 0 gdl run-push made lf-goals! lf-main-goal -> outcome-ok outcome-ok gdl outcome-ok }T
tgoal constant gd  tgoal constant ge  tgoal constant gf
: list-de ( -- list ) 0 gd run-push made ge run-push made ;
T{ list-de lf-goals! 0 gf run-push made lf-replace-main lf-goals cells. -> outcome-ok outcome-ok gf ge }T
T{ 0 gd run-push made lf-goals-append lf-goals cells. -> outcome-ok gf ge gd }T
T{ 0 lf-goals! 0 lf-replace-main lf-goals 99 lf-goals-append -> outcome-ok outcome-invalid 0 outcome-invalid }T
T{ list-de lf-goals! lf-pst-reset lf-goals lf-pst-root -> outcome-ok 0 -1 }T
T{ list-de lf-goals! lf-mctx-reset lf-goals -> outcome-ok 0 }T

\ ---- Printing, the rules check_goals.py does not meet.
g-fresh
: cap-has? ( c-addr u -- flag ) cap 2swap search nip nip ;
: hyp-aux ( view type c-addr u -- view' fvar )
  rot lf-lctx-local made >r r@ -rot lf-local-aux-decl local-of lf-view-push made r> ;
\ Hidden: an implementation detail and an auxiliary declaration; the
\ hypotheses around them still share a line.
0 nat s" a" hyp drop nat s" b" hyp-detail drop nat s" c" hyp-aux drop nat s" d" hyp drop
constant vhid
T{ true. 0 vhid goal goal-text s\" a d : Nat\n⊢ True" compare -> 0 }T
\ Types with literals, built apart, are equal (Lean's == on literals): one
\ line; types that differ in a literal are not.
0 0 num 0 num eq s" h1" hyp drop 0 num 0 num eq s" h2" hyp drop 1 num 0 num eq s" h3" hyp drop
constant vlit
T{ true. 0 vlit goal goal-text s\" h1 h2 : 0 = 0\nh3 : 1 = 0\n⊢ True" compare -> 0 }T
\ A let value: shown up to Lean's approxDepth 254 for a tactic goal (the
\ sum of 126 ones; Lean measured 2n + 2 for n ones), as ⋯ past it; for
\ a goal of another kind (not synthetic opaque) only a leaf shows.
: ones ( n -- t ) 1 num swap 1 ?do 1 num add loop ;
T{ 1 num gp-depth 2 ones gp-depth 126 ones gp-depth 127 ones gp-depth 300 ones gp-depth
   -> 3 outcome-ok 6 outcome-ok 254 outcome-ok 255 outcome-ok 255 outcome-ok }T
0 nat 126 ones s" y" let-hyp constant fy constant v126
T{ fy fy eq 0 v126 goal goal-text 2drop s" y : Nat := 1 + 1 + 1" cap-has? s" ⋯" cap-has? -> true false }T
0 nat 2 ones s" y" let-hyp constant fy2 constant v2
0 nat nat s" z" let-hyp drop constant vz
T{ fy2 fy2 eq mv-natural v2 lf-mvar-new-at made goal-text s\" y : Nat := ⋯\n⊢ y = y" compare
   -> 0 }T
T{ true. mv-synthetic vz lf-mvar-new-at made goal-text s\" z : Nat := Nat\n⊢ True" compare -> 0 }T
\ A let's value with a let inside counts its type and body one level
\ down (LeanForth keeps them under a lambda): let c := 1; c is depth 4.
T{ 1 num nat 0 t-var t-lam 0 lf-let-make must gp-depth -> 4 outcome-ok }T
\ So two nested lets around 125 ones (depth 252) reach 254, still shown;
\ counted at the lambda's own depth they would reach 256, past it: the
\ value crosses the threshold only through the lets (review N16).
: let-around ( body -- t ) 1 num nat rot t-lam 0 lf-let-make must ;
: two-lets ( -- t ) 125 ones let-around let-around ;
T{ 125 ones gp-depth two-lets gp-depth -> 252 outcome-ok 254 outcome-ok }T
\ Metavariables: ?TAG for a tagged one, ?m.N for another.
nat mv-natural lf-mvar-new made constant mq  mq s" q" nm lf-mvar-tag! must-ok
nat mv-natural lf-mvar-new made constant manon
T{ mq manon eq 0 0 goal goal-text 2drop s" ⊢ ?q = ?m." cap-has? -> true }T
\ Twelve hypotheses of one name: tombstones up to ✝¹⁰ (two digits).
: twelve ( -- view ) 0 12 0 do nat s" x" hyp drop loop ;
T{ true. 0 twelve goal goal-text 2drop s" x✝¹⁰ x✝⁹" cap-has? s" x✝ x : Nat" cap-has? -> true true }T
\ A free variable outside the goal's context prints as _fvar.N; outside
\ a goal print, by the current context.
nat lf-lctx-local made constant floose
T{ floose floose eq 0 0 goal goal-text 2drop s" ⊢ _fvar." cap-has? -> true }T
0 nat s" w" hyp constant fw lf-mctx-view!  true lf-print-notation!
T{ cap-reset fw fw eq fuel lf-print-term cap s" w = w" compare -> outcome-ok 0 }T
lf-view-empty lf-mctx-view!
T{ cap-reset fw fuel lf-print-term cap s" _fvar." search nip nip -> outcome-ok true }T
\ A tag with macro scopes (an inaccessible binder's: apply's and rewrite's
\ new metavariables) prints erased, with ✝, as Lean's sanitizer gives it
\ (plan 9.4.8l R: ?a✝, not ?a.«_@»._internal._hyg.0).
nat mv-natural lf-mvar-new made constant mh
mh s" a._@._internal._hyg" nm 0 nm# lf-mvar-tag! must-ok
T{ mh mq eq 0 0 goal goal-text 2drop s" ⊢ ?a✝ = ?q" cap-has? -> true }T
\ lf-with-names: a message's term named as a goal of that context names
\ it (plan 9.4.8l O): the inaccessible n prints n✝, the plain name
\ outside; inside a goal print the goal's own names stay (here an empty
\ context's: _fvar.N); a throw puts the printer's state back.
0 nat s" n" hyp-hidden constant fhid9 constant vhid9
: hidprint ( t -- outcome ) fuel lf-print-term ;
T{ cap-reset fhid9 ' hidprint vhid9 lf-with-names cap s" n✝" compare gp gp-active @
   -> outcome-ok 0 false }T
T{ vhid9 lf-mctx-view! cap-reset fhid9 hidprint cap s" n" compare -> outcome-ok 0 }T
lf-view-empty lf-mctx-view!
: hidinside ( -- outcome )
  lf-view-empty gp gp-view ! true gp gp-active ! fhid9 ['] hidprint vhid9 lf-with-names
  false gp gp-active ! ;
T{ cap-reset hidinside cap s" _fvar." search nip nip -> outcome-ok true }T
: hidthrows ( t -- ) drop -77 throw ;
T{ fhid9 ' hidthrows vhid9 ' lf-with-names catch nip nip nip gp gp-active @ -> -77 false }T
\ No room for the names' codes (the heap refusing gp-codes' block, given
\ back first): the plain names (n in its own context), never codes not
\ made (review tactic-fidelity L4).
: codes-anew ( -- ) gp-codes dup slab-unit over slab-limit rot dup slab-free slab-init drop ;
T{ vhid9 lf-mctx-view! codes-anew 1 heap-refusals ! cap-reset fhid9 ' hidprint vhid9
   lf-with-names heap-refusals @ 0 heap-refusals ! cap s" n" compare gp gp-active @
   -> outcome-ok 0 0 false }T
lf-view-empty lf-mctx-view!
\ Failures: no goal, a stale one, an instantiation that is unsupported;
\ the printer's notation flag is restored whatever happens.
false lf-print-notation!
T{ 99999 lf-goal-print lf-print-notation? -> outcome-invalid false }T
\ (?mfz := fun x => Nat -> x: put into fun z => ?mfz z, the loose z would
\ need lifting under the arrow's binder, which is not ported.)
nat mv-natural lf-mvar-new made constant mfz  mfz nat nat 1 t-var t-pi t-lam lf-mvar-assign must-ok
T{ cap-reset nat mfz 0 t-var t-app t-lam 0 0 goal lf-goal-print lf-print-notation?
   -> outcome-unsupported false }T
\ The same failure in a hypothesis's type; a hypothesis of a type the
\ printer cannot compare (an importer's unsupported leaf) beside another;
\ a group the printer cannot print when a let ends it; a goal that fails
\ among the goals of .goals.
nat mfz 0 t-var t-app t-lam constant unsure
lf-form-mdata lf-hterm-unsupported must drop constant odd
T{ true. 0 0 unsure s" h" hyp drop goal lf-goal-print -> outcome-unsupported }T
T{ true. 0 0 odd s" a" hyp drop odd s" b" hyp drop goal lf-goal-print -> outcome-invalid }T
T{ true. 0 0 odd s" a" hyp drop nat 1 num s" x" let-hyp drop goal lf-goal-print
   -> outcome-invalid }T
T{ unsure 0 0 goal 0 swap run-push made lf-goals! lf-goals-print -> outcome-ok outcome-unsupported }T
true. 0 0 goal constant gstale  lf-mctx-reset
T{ gstale lf-goal-print -> outcome-invalid }T
\ The printer's comparison (lf-print-same?, Lean's ==) on each kind of
\ leaf and node: literals, strings, projections and their leaves, lets (a
\ let and a have differ here, where Lean's == ignores nonDep); a leaf it
\ does not know and negative fuel are invalid.
g-fresh
: same? ( a b -- flag ) fuel lf-print-same? must-ok ;
: str. ( c-addr u -- t ) lf-str-new must-ok drop ;
: proj. ( e i -- t ) >r s" Prod" nm r> lf-proj-of made ;
: let. ( nondep -- t ) >r 1 num nat 0 t-var t-lam r> lf-let-make must ;
T{ 1 num 1 num same? 1 num 2 num same? s" ab" str. s" ab" str. same? s" ab" str. s" ac" str. same?
   -> true false true false }T
T{ nat 0 proj. nat 0 proj. same? nat 0 proj. nat 1 proj. same? false let. false let. same?
   true let. false let. same? -> true false true false }T
T{ lf-form-mdata lf-hterm-unsupported must drop dup fuel lf-print-same? nat nat -1 lf-print-same?
   -> false outcome-invalid false outcome-invalid }T
\ A Π whose body's head is a hypothesis of an arrow type ending in Prop
\ is a proposition (Lean's isPropQuick reads the variable's type): ∀.
0 nat t-prop t-pi s" p" hyp constant fp constant vp
T{ nat fp 0 t-var t-app t-pi s" x" ex. 0 vp goal goal-text s\" p : Nat → Prop\n⊢ ∀ (x : Nat), p x"
   compare -> 0 }T
\ Tombstones numbered as Lean's sanitizeNames numbers them (review of
\ cleanup-families-2, L3): each counts the later locals renamed like it,
\ so three inaccessible x's print x✝² x✝¹ x✝, and two shadowed x's under
\ an accessible one x✝¹ x✝ x.
g-fresh
: three-x ( xt -- view ) >r 0 nat s" x" r@ execute drop nat s" x" r@ execute drop
  nat s" x" r> execute drop ;
T{ ' hyp-hidden three-x true. 0 rot goal goal-text s\" x✝² x✝¹ x✝ : Nat\n⊢ True" compare
   -> 0 }T
T{ ' hyp three-x true. 0 rot goal goal-text s\" x✝¹ x✝ x : Nat\n⊢ True" compare -> 0 }T
\ Many goals: unsolved ones printed in order, a blank line between two.
g-fresh
: goals-n ( n -- list ) 0 swap 0 ?do true. 0 0 goal run-push made loop ;
3 goals-n lf-goals! must-ok
T{ goals-text s\" ⊢ True\n\n⊢ True\n\n⊢ True\n" compare -> 0 }T
T{ lf-goals 1 run@ true. lf-mvar-assign goals-text s\" ⊢ True\n\n⊢ True\n" compare
   -> outcome-ok 0 }T

\ ---- Resources: 2,000 hypotheses in one view (each push in place, so
\ 2,000 cells), the oldest cleared; their tombstones printed (a sink that
\ keeps the first bytes); 1,000 goals, every other one assigned, pruned; a
\ refused heap at each allocation of a clear makes it full, the goal open.
g-fresh
: many ( n -- view ) 0 swap 0 ?do nat s" h" hyp drop loop ;
2000 many constant vbig
T{ vbig lf-view-count runs-cells -> 2000 2000 }T
true. 0 vbig goal constant gbig
T{ gbig vbig 0 lf-view-local lf-local-fvar lf-goal-clear made lf-mvar-view drop lf-view-count
   -> 1999 }T
variable sunk
: head-sink ( c-addr u -- ) dup sunk +! cap-len @ 4000 < if cap-sink else 2drop then ;
' head-sink lf-print-unicode lf-print-setup
T{ 0 sunk ! cap-reset true. 0 vbig goal lf-goal-print s" h✝¹⁹⁹⁸ h✝¹⁹⁹⁷" cap-has? sunk @ 10000 >
   -> outcome-ok true true }T
' cap-sink lf-print-unicode lf-print-setup
1000 goals-n constant l1000
: assign-odd ( list -- )
  dup run-count 0 ?do i 1 and if dup i run@ true. lf-mvar-assign must-ok then loop drop ;
T{ l1000 lf-goals! l1000 assign-odd lf-goals-unsolved swap run-count
   -> outcome-ok outcome-ok 500 }T
g-fresh
0 nat s" n" hyp constant fn9 constant vn9
true. 0 vn9 goal constant g9
variable refused
: refused-clear ( k -- outcome ) heap-refusals ! g9 fn9 lf-goal-clear nip ;
: clear-refusals ( -- outcome )
  0 refused ! 1 begin dup refused-clear dup ok? 0= while
    outcome-full <> abort" clear: not full" g9 lf-goal-assigned? abort" clear: assigned"
    1 refused +! 1+ repeat nip 0 heap-refusals ! ;
T{ clear-refusals refused @ 0> g9 lf-goal-assigned? -> outcome-ok true true }T

T{ depth -> 0 }T
cr .( goals.fs: all tests passed) cr
bye

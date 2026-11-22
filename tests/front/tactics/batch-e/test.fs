\ Unit tests of tactic batch 3b (plan row TB2) over decide's slice of Init
\ in an authoring run, by the classes of docs/development/
\ TEST_COVERAGE_REVIEW.md: tactic-syntax.fs's lists of names (read as
\ records), the holes _, ?_ and ?: NAME (reader.fs's nodes, elab-term.fs's
\ elaboration, elab-app.fs's records), mvars.fs's lf-mvar-at and
\ lf-mvar-named, new-goals.fs's lf-fresh-mvars, lf-natural-mvars,
\ lf-tac-log-unassigned and lf-tag-untagged, meta-config.fs's
\ lf-with-holes-as-goals, tactic-core.fs's lf-tac-arg-fvars and
\ lf-tac-elab-with-holes (through by-refine and by-specialize), and the
\ list words through LeanForth text (tests/support/tactic-text.fs):
\ 1. outcomes: each word accepted, each refusal with its code (94, 95,
\    99, 139, 440, 455, 461), each case not ported (99, 139);
\ 2. malformed input: a list with no ], an empty one, _, a LeanForth word
\    or a value where a name goes, ?: with no name, a reserved word as a
\    binder's name (458, 459, 460, 84, 86, 2, 78);
\ 3. stack effects and records: each T{ }T checks the depth; every field
\ of the steps, nodes, hole records and goals made;
\ 5. resources (tests/support/meta-sweeps.fs): the new goals' words and
\    the words through their text with every heap allocation refused in
\    turn: the answer or full, never another answer;
\ 6. state: the frames, the flags and the holes' records put back.
\ The terms are checked node for node with pinned Lean by check.py.
\ Nothing here accepts a theorem: only the kernel's check does.
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
: made ( x outcome -- x ) ok? 0= abort" batch-e test: not made" ;
: nm ( c-addr u -- id ) lfa-intern ;
: nat ( -- t ) s" Nat" lf-mk-const0 ;
: goal ( type -- goal ) 0 lf-mctx-view lf-goal-new made ;
: token ( -- c-addr u ) lfa-error lfa-err-token lfa-error lfa-err-length @ ;
: detail-has? ( c-addr u -- flag )
  0 lfa-detail slab-at lfa-detail slab-count 2swap search nip nip ;
: step@ ( i -- addr ) lf-tactic-step ;
: code1 ( x xt -- code ) catch if drop lf-author-code else drop 0 then ;
: tag@ ( mvar -- name ) lf-mvar-tag drop ;
: kind@ ( mvar -- kind ) lf-mvar-kind drop ;
create stmt 512 allot  variable stmt#
: stmt+ ( c-addr u -- ) tuck stmt stmt# @ + swap move stmt# +! ;
: st ( c-addr u -- c-addr' u' )
  0 stmt# ! s" Nat explicit: a Nat explicit: b " stmt+ stmt+ stmt stmt# @ ;
: ab ( -- c-addr u ) s" a b = explicit: h b a = explicit: k a b =" st ;
: and2 ( -- c-addr u ) s" a b = explicit: h1 b a = explicit: h2 a b = b a = ∧" st ;
: aa ( -- c-addr u ) s" a a ≤" st ;

\ ---- 3. Records: a list of names, its arguments and places.
T{ ab s" by-revert[ h k ] by-intro[ x _ ]" tactic-ran -> 89 }T
T{ 1 step@ tac-kind @ 1 step@ tac-shape @ 1 lf-tac-args# 1 0 lf-tac-arg s" h" nm =
   1 1 lf-tac-arg s" k" nm = -> tac-k-revert-list tac-shape-hyps 2 true true }T
T{ 2 step@ tac-kind @ 2 step@ tac-shape @ 2 lf-tac-args# 2 0 lf-tac-arg s" x" nm =
   2 1 lf-tac-arg -> tac-k-intro-list tac-shape-binders 2 true 0 }T
T{ 2 0 lf-tac-arg-at 2 1 lf-tac-arg-at < 2 step@ tac-to @ 2 1 lf-tac-arg-at >
   2 step@ tac-loc @ -> true true 0 }T
lf-tac-forget
\ The list ends at ]: what follows on the line is the next step, and x,
\ a name the list gave, is a hypothesis there.
T{ ab s" by-revert[ h k ] by-intro[ x y ] x by-exact" tactic-ran -> 0 }T
T{ ab s" by-revert[ h k ] by-intro[ ] by-intro[ ] by-assumption" tactic-ran -> 0 }T
T{ 2 lf-tac-args# 2 step@ tac-shape @ -> 0 tac-shape-binders }T
T{ s" a b = explicit: h ' h ' h = explicit: k b a = explicit: j b a =" st
   s" by-clear[ h k ] ' j by-exact" tactic-ran -> 0 }T
T{ 1 lf-tac-args# 1 step@ tac-kind @ -> 2 tac-k-clear-list }T
T{ ab s" by-revert[ h k ] by-intro[ _ _ ] by-rename-i[ x _ ] x by-exact" tactic-ran -> 0 }T
T{ 3 step@ tac-kind @ 3 step@ tac-shape @ 3 lf-tac-args# 3 1 lf-tac-arg
   -> tac-k-rename-i tac-shape-binders+ 2 0 }T
lf-tac-forget

\ ---- 2. Malformed lists.
T{ ab s" by-revert[ _ ]" tactic-ran token s" _" compare -> 459 0 }T
T{ ab s" by-clear[ h by-rfl ]" tactic-ran token s" by-rfl" compare -> 459 0 }T
T{ ab s" by-revert[ ]" tactic-ran token s" ]" compare -> 460 0 }T
T{ ab s" by-clear[ ]" tactic-ran ab s" by-rename-i[ ]" tactic-ran -> 460 460 }T
T{ ab s\" by-intro[ x\n ]" tactic-ran token s" x" compare -> 458 0 }T
T{ ab s\" by-revert[ h\n" tactic-ran token s" h" compare -> 458 0 }T
\ (on the theorem's one line, end is a name of the list: a LeanForth word)
T{ ab s" by-revert[ h" tactic-ran token s" end" compare -> 459 0 }T
T{ ab s" by-intro[ by-rfl ]" tactic-ran ab s" ' a by-intro[ x ]" tactic-ran -> 84 86 }T
T{ ab s" by-revert[ h ] by-intro[ x ] ]" tactic-ran -> 83 }T
lf-tac-forget
\ The new words are reserved: no binder takes their names (78), and the
\ step log shows each word as written.
T{ s" Nat explicit: ?_ a a =" st s" by-rfl" tactic-ran token s" ?_" compare -> 78 0 }T
T{ s" Nat explicit: ?: a a =" st s" by-rfl" tactic-ran -> 78 }T
T{ s" Nat explicit: by-intro[ a a =" st s" by-rfl" tactic-ran -> 78 }T
T{ s" Nat explicit: by-refine a a =" st s" by-rfl" tactic-ran -> 78 }T
T{ s" Nat explicit: by-rename-i[ a a =" st s" by-rfl" tactic-ran -> 78 }T
T{ tac-k-intro-list lf-tac-word s" by-intro[" compare tac-k-refine lf-tac-word s" by-refine"
   compare -> 0 0 }T
lf-tac-forget

\ ---- 1. The list words through the text.
\ getFVarIds: a name no local has (455, before anything is reverted), a
\ constant's name (99).
T{ ab s" by-revert[ h foo ]" tactic-ran -> 455 }T
T{ ab s" by-revert[ Nat.le_refl ]" tactic-ran ab s" by-clear[ h Nat.le_refl ]" tactic-ran
   -> 99 99 }T
\ clear newest first: k (on h) before h, whatever the order written; a
\ name twice cleared twice, unknown the second time (440); the goal's own
\ variable (442), after h.
T{ s" a b = explicit: h ' h ' h = explicit: k b a = explicit: j b a =" st
   s" by-clear[ k h ] ' j by-exact" tactic-ran -> 0 }T
T{ ab s" by-clear[ k k ]" tactic-ran ab s" by-clear[ a h ]" tactic-ran -> 440 441 }T
T{ s" a b = explicit: h a a =" st s" by-clear[ a h ]" tactic-ran -> 442 }T
\ (clear h alone, k depending on it: 441, as by-clear's)
T{ s" a b = explicit: h ' h ' h = explicit: k a b =" st s" by-clear[ h ]" tactic-ran -> 441 }T
\ intro: too many names (94), rfl (99); rename_i: too many (211).
T{ ab s" by-revert[ h ] by-intro[ x y ]" tactic-ran ab s" by-revert[ h ] by-intro[ rfl ]"
   tactic-ran -> 94 99 }T
T{ ab s" by-revert[ h ] by-intro[ _ ] by-rename-i[ x y ]" tactic-ran -> 211 }T
lf-tac-forget

\ ---- The holes: their nodes.
: arg-node ( i k j -- node ) >r lf-tac-arg r> syn-arg ;
T{ s" a a =" st s" _ Eq.refl by-exact" tactic-ran 1 0 0 arg-node syn-kind@ -> 0 syn-k-hole }T
T{ and2 s" ' And.intro ?: left $ ?_ $ by-refine" tactic-ran -> 89 }T
T{ 1 0 0 arg-node dup syn-kind@ swap syn-a@ s" left" nm = 1 0 1 arg-node dup syn-kind@
   swap syn-a@ -> syn-k-synthetic true syn-k-synthetic 0 }T
\ (each at its word: ?_ ten columns after ?:)
T{ 1 0 1 arg-node syn-at@ 1 0 0 arg-node syn-at@ - -> 10 }T
T{ and2 s" ' And.intro ?: _ $ ?_ $ by-refine" tactic-ran 1 0 0 arg-node syn-a@ -> 89 0 }T
T{ s" a a =" st s\" ?:\n" tactic-ran -> lfa-e-no-name }T
lf-tac-forget

\ ---- The holes elaborated: natural (refine's _), synthetic opaque (?_,
\ and _ under specialize's allowNaturalHoles), tagged (?: NAME), each
\ recorded once, an argument's marked.
: hole@ ( k -- addr ) ea-holes slab-at ;
: holes# ( -- n ) ea-holes slab-count ;
T{ aa s" ' Nat.le_refl _ $ by-refine" tactic-ran holes# 0 hole@ eh-mvar @ kind@
   0 hole@ eh-arg @ -> 0 1 mv-natural true }T
T{ 0 hole@ eh-at @ 1 0 0 arg-node syn-at@ = 0 hole@ eh-mvar @ lf-mvar-value nip -> true true }T
T{ aa s" ' Nat.le_refl _ $ by-specialize" tactic-ran holes# 0 hole@ eh-mvar @ kind@
   -> 447 1 mv-opaque }T
T{ ab s" ?_ by-exact" tactic-ran holes# 0 hole@ eh-mvar @ dup kind@ swap tag@
   0 hole@ eh-arg @ -> 461 1 mv-opaque 0 0 }T
T{ and2 s" ' And.intro ?: left $ ?_ $ by-refine" tactic-ran holes# 0 hole@ eh-mvar @ tag@
   s" left" nm = 1 hole@ eh-mvar @ tag@ s" refine" nm = -> 89 2 true false }T
\ A name some metavariable has already: not ported (139), and the second
\ hole is never made.
T{ and2 s" ' And.intro ?: x $ ?: x $ by-refine" tactic-ran holes# -> 139 1 }T
\ A hole applied to an argument: not ported (139).
T{ ab s" ?_ ' h $ by-exact" tactic-ran -> 139 }T
\ No implicit-lambda test for a hole (133 elsewhere on a negation): the
\ hole is made and left open (461).
T{ s" a b = ¬" st s" _ by-exact" tactic-ran holes# -> 461 1 }T
T{ s" context:" detail-has? -> true }T
lf-tac-forget

\ ---- refine: its goals and their tags (tagUntaggedGoals), the natural
\ holes refused (461; a hole that is an argument 99; an implicit
\ argument 95), a value with no new goal.
T{ and2 s" ' And.intro ?_ $ ?_ $ by-refine" tactic-ran -> 89 }T
T{ lf-goals dup run-count over 0 run@ tag@ s" refine_1" nm = rot 1 run@ tag@ s" refine_2" nm =
   -> 2 true true }T
T{ and2 s" ' And.intro ' h1 $ ?_ $ by-refine" tactic-ran lf-goals dup run-count swap 0 run@
   tag@ -> 89 1 0 }T
T{ aa s" _ by-refine" tactic-ran and2 s" ' And.intro ' h1 $ _ $ by-refine" tactic-ran
   -> 461 99 }T
T{ ab s" ' Eq.trans ?_ $ ?_ $ by-refine" tactic-ran -> 95 }T
T{ aa s" ' Nat.le_refl _ $ by-refine" tactic-ran lf-goals run-count -> 0 0 }T
\ The goal's own type: refine of a term of another fails (96), nothing
\ assigned.
T{ ab s" ' Nat.le_refl _ $ by-refine" tactic-ran -> 96 }T
lf-tac-forget

\ ---- lf-mvar-at, lf-mvar-named: the n-th metavariable, the newest of a
\ tag (assigned or not); none for a tag no metavariable has.
lf-view-empty lf-mctx-view!
nat goal constant g1
T{ lf-mvar-count 1- lf-mvar-at -> g1 }T
T{ g1 s" t1" nm lf-mvar-tag! s" t1" nm lf-mvar-named -> outcome-ok g1 true }T
nat goal constant g2
T{ g2 s" t1" nm lf-mvar-tag! s" t1" nm lf-mvar-named -> outcome-ok g2 true }T
T{ s" none-such" nm lf-mvar-named -> false }T
T{ g2 g1 lf-mvar-assign s" t1" nm lf-mvar-named -> outcome-ok g2 true }T

\ ---- lf-fresh-mvars: the open metavariables of e from `from` on, oldest
\ first, a run; an older one, an assigned one left out; a delayed one 99.
lf-mvar-count constant from0
nat goal constant m1
nat goal constant m2
nat goal constant m3
: pair ( x y -- e ) lf-mk-eq ;
T{ m2 m1 pair from0 lf-fresh-mvars dup run-count over 0 run@ rot 1 run@ -> 2 m1 m2 }T
T{ m2 m1 pair m1 lf-term-first@ 1+ lf-fresh-mvars dup run-count swap 0 run@ -> 1 m2 }T
T{ m3 m1 lf-mvar-assign m3 m1 pair from0 lf-fresh-mvars run-count -> outcome-ok 1 }T
T{ m1 m1 pair from0 lf-fresh-mvars run-count -> 1 }T
s" a" nm nat lf-lctx-local made constant fa
nat goal constant d1
nat goal constant p1
T{ fa lf-delay-fvar d1 p1 1 lf-mvar-delay -> outcome-ok outcome-ok }T
: fresh-d ( -- ) d1 m1 pair from0 lf-fresh-mvars drop ;
T{ 0 ' fresh-d code1 -> 99 }T
lf-tac-forget

\ ---- lf-natural-mvars: the natural ones, in order.
nat mv-natural lf-mvar-new made constant n1
nat mv-natural lf-mvar-new made constant n2
: run3 ( a b c -- run ) >r >r 0 swap run-push made r> run-push made r> run-push made ;
T{ n1 m1 n2 run3 lf-natural-mvars dup run-count over 0 run@ rot 1 run@ -> 2 n1 n2 }T
T{ m1 m2 m1 run3 lf-natural-mvars run-count -> 0 }T

\ ---- lf-tag-untagged: one anonymous goal takes the parent's tag; more,
\ parent ++ suffix_1, .. in order, the tagged ones left; no parent:
\ suffix_1 ...
nat goal constant u1
nat goal constant u2
nat goal constant u3
: c-refine ( -- c-addr ) c" refine" ;
: c-specialize ( -- c-addr ) c" specialize" ;
s" p" nm s" refine_1" nm lf-name-append-tag constant p-r1
s" p" nm s" refine_2" nm lf-name-append-tag constant p-r2
T{ u2 s" t" nm lf-mvar-tag! p-r1 p-r2 = -> outcome-ok false }T
T{ u1 u2 u3 run3 c-refine s" p" nm lf-tag-untagged u1 tag@ u2 tag@ u3 tag@
   -> p-r1 s" t" nm p-r2 }T
nat goal constant u4
: run2 ( a b -- run ) >r 0 swap run-push made r> run-push made ;
T{ u4 u2 run2 c-specialize s" q" nm lf-tag-untagged u4 tag@ -> s" q" nm }T
nat goal constant u5
nat goal constant u6
T{ u6 u5 run2 c-refine 0 lf-tag-untagged u5 tag@ u6 tag@ -> s" refine_2" nm s" refine_1" nm }T
T{ tng-frames slab-count -> 0 }T

\ ---- lf-tac-log-unassigned: none, nothing; each a hole: Lean's
\ placeholder error (461); a hole that is an argument (99); another
\ metavariable (95).
nat mv-natural lf-mvar-new made constant h1
T{ h1 0 lf-elab-hole+ -> outcome-ok }T
T{ h1 lf-elab-hole -> 0 false true }T
: log1 ( mvar -- run ) 0 swap run-push made dup lf-tac-log-unassigned ;
: log0 ( run -- run ) dup lf-tac-log-unassigned ;
: code1f ( x xt -- code ) code1 lf-tac-forget ;
T{ 0 ' log0 code1f h1 ' log1 code1f n1 ' log1 code1f -> 0 461 95 }T
T{ h1 ea-arg-hole! h1 lf-elab-hole -> h1 0 true true }T
T{ h1 ' log1 code1 -> 99 }T
lf-tac-forget

\ ---- lf-with-holes-as-goals: both flags set inside, put back after, a
\ THROW too.
: flags? ( -- holes? opaque? ) lf-holes-opaque? lf-defeq-opaque lf-meta-flag? ;
T{ flags? ' flags? lf-with-holes-as-goals flags? -> false false true true false false }T
: thrower ( -- ) 7 throw ;
T{ ' thrower ' lf-with-holes-as-goals catch nip flags? -> 7 false false }T

\ ---- 5. Resources: the new goals' words with every heap allocation
\ refused in turn, and the words through their text: the answer or full.
: frames-anew ( -- ) tng-frames sweep-slab-anew tcl-frames sweep-slab-anew
  ea-holes sweep-slab-anew ;
' frames-anew sweep-slabs-xt !
: s-fresh ( e -- n ) from0 lf-fresh-mvars run-count ;
: p-fresh ( e -- n outcome ) ['] s-fresh 1 1 lf-meta-catch ;
\ (lf-tag-untagged asks the heap for nothing a sweep could refuse: its
\ frame's slab and the run of goals have room already.)
T{ m2 m1 pair ' p-fresh heap-sweep swept? -> true }T
: full-code? ( code -- flag ) dup if lf-author-outcome outcome-full = then ;
: text-full ( c-addr u c-addr' u' -- code outcome )
  tactic-ran dup full-code? if drop -1 outcome-full else outcome-ok then ;
: p-refine ( x -- code outcome )
  drop and2 s" ' And.intro ?_ $ ?: r $ by-refine ' h1 by-exact ' h2 by-exact" text-full ;
: p-lists ( x -- code outcome ) drop ab
  s" by-revert[ h k ] by-intro[ x y ] by-clear[ y ] x by-exact" text-full ;
: p-names ( x -- code outcome ) drop ab
  s" by-revert[ h k ] by-intro[ _ _ ] by-rename-i[ x _ ] by-clear[ b ] x by-exact" text-full ;
T{ 0 ' p-refine heap-sweep swept? 0 ' p-names heap-sweep swept? -> true true }T
T{ 0 ' p-lists heap-sweep swept? tcl-frames slab-count tng-frames slab-count -> true 0 0 }T
lf-tac-forget
.( batch-e test.fs: all tests passed) cr

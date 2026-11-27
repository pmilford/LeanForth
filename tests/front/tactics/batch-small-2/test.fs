\ Unit tests of small tactics 2 (plan row 9.4.8z12) over the patterns
\ slice of Init in an authoring run, by the classes of docs/development/
\ TEST_COVERAGE_REVIEW.md: elab-calc.fs's words called on terms built here
\ (lf-calc-relation?, lf-calc-trans), meta-tactic/goal.fs's checked
\ assignment of a value with an open metavariable, and the tactic words
\ through their text (tests/support/tactic-text.fs): by-calc[ ],
\ by-with-reducible, by-with-reducible-and-instances, by-with-unfolding-all:
\ 1. outcomes: each word accepted; 96, 97, 510, 512, 513 with their
\    places; each case not supported (99, 131: unsupported);
\ 2. malformed input: an empty by-calc[ ], one never closed, an odd count,
\    a block never ended;
\ 3. records: the shapes, rows and modes, Lean's names, the codes;
\ 4. interfaces: getCalcRelation?'s parts, mkCalcTrans' term, type and
\    codes, its relation check, the new goals' tags and order;
\ 5. resources: every heap allocation refused in turn, lf-calc-trans
\    called directly and each tactic through its text
\    (tests/support/meta-sweeps.fs): the answer or full;
\ 6. state: the transparency inside a block, after it, after an error a
\    try took back and after a run that stopped inside one (no frame
\    left to the next authoring run); a block inside inherits it; the
\    elaboration inside a block at its transparency; lf-tac-at's mode
\    inside, put back after (rw's closing rfl, which closes or fails),
\    a LeanForth scope alone changing nothing; calc's new goals in
\    front of the others (the Forth review's B1, B2, M1, M2, Low 1, 4).
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
T{ s" tests/front/patterns-slice.ndjson" true lfc-library-open -> outcome-ok }T
T{ s" tests/front/patterns-slice.elab.ndjson" lfc-elab-file! lfc-elab-read lfc-rooms
   -> outcome-ok outcome-ok }T
lf-author-begin
: made ( x outcome -- x ) ok? 0= abort" batch-small-2 test: not made" ;
lf-meta-throw-base outcome-invalid - constant thrown-invalid
: authored ( code -- n ) dup lf-author-throw = if drop lf-author-code lf-tac-forget then ;
: code1 ( x xt -- code ) catch dup if nip then authored ;
: token ( -- c-addr u ) lfa-error lfa-err-token lfa-error lfa-err-length @ ;
: token? ( c-addr u -- flag ) token compare 0= ;
: nat ( -- t ) s" Nat" lf-mk-const0 ;
: fresh ( -- ) lf-view-empty lf-mctx-view! ;
: binder ( type c-addr u -- fvar )
  lfa-intern swap lf-lctx-local made tuck swap 0 lf-local-new made
  lf-mctx-view swap lf-view-push made lf-mctx-view! ;
: goal ( type -- goal ) 0 lf-mctx-view lf-goal-new made ;
: eqv? ( a b -- flag ) lf-meta-eqv made ;
: nm ( c-addr u -- name ) lfa-intern ;
: open? ( goal -- flag ) lf-goal-assigned? 0= ;

\ ---- 3. Records: shapes, rows, modes, Lean's names, the codes.
T{ tac-k-calc lf-tactic-shape@ -> tac-shape-list+ }T
: blocky? ( kind -- flag ) lf-tactic-shape@ tac-block tac-shape-has? ;
T{ tac-k-with-reducible blocky? tac-k-with-instances blocky? tac-k-with-all blocky?
   -> true true true }T
: lean? ( kind c-addr u -- flag ) rot lf-tac-lean compare 0= ;
T{ tac-k-calc s" calc" lean? tac-k-with-reducible s" with_reducible" lean?
   tac-k-with-instances s" with_reducible_and_instances" lean?
   tac-k-with-all s" with_unfolding_all" lean? -> true true true true }T
T{ lfa-e-calc-trans lfa-e-calc-not-rel lfa-e-calc-relation lfa-e-calc-lhs -> 510 511 512 513 }T
T{ twr-mode-reducible twr-mode-instances twr-mode-all 0 twr-weight -> twr-mode-reducible
   twr-mode-instances twr-mode-all 2 }T

\ ---- 4. getCalcRelation?: r a b of a relation of two arguments or more.
fresh
nat s" a" binder constant fa
nat s" b" binder constant fb
nat s" c" binder constant fc
s" True" lf-mk-const0 constant ttrue
fa fb lf-mk-eq constant eab
fb fc lf-mk-eq constant ebc
: rel-parts? ( e -- r? a? b? flag )
  lf-calc-relation? >r fb eqv? >r fa eqv? >r eab lf-calc-rel eqv? r> r> r> ;
T{ eab rel-parts? -> true true true true }T
T{ eab lf-calc-lhs fa eqv? eab lf-calc-rhs fb eqv? -> true true }T
T{ ttrue lf-calc-relation? s" Nat.succ" lf-mk-const0 fa lf-mk-app lf-calc-relation? -> false false }T
T{ ttrue ' ecl-relation code1 -> thrown-invalid }T    \ one the caller made sure of
\ mkCalcTrans' relation check: a type no relation is 511 with it.
T{ fa ttrue ecl-relation-result swap rot ttrue eqv? -> false 511 true }T
T{ fa eab ecl-relation-result -rot eab eqv? swap fa eqv? -> true true true }T

\ ---- 4. mkCalcTrans: h1 : a = b, h2 : b = c chained, a = c.
eab s" h1" binder constant fh1
ebc s" h2" binder constant fh2
fh1 eab fh2 ebc lf-calc-trans constant ct-ok constant ct-type constant ct-val
: head12 ( e -- f ) 12 0 do lf-term-first@ loop ;
T{ ct-ok ct-type fa fc lf-mk-eq eqv? ct-val head12 lf-const-name s" Trans.trans" nm lf-name-same?
   -> true true true }T
T{ ct-val lf-infer! lf-instantiate! fa fc lf-mk-eq eqv? -> true }T
\ No Trans instance for And with And: 510 and the type sought, Trans r s ?t.
: and-of ( p q -- t ) s" And" 2swap 2 lf-mk-app-m ;
eab ebc and-of constant aab
ebc fa fc lf-mk-eq and-of constant abc
aab s" h3" binder constant fh3
abc s" h4" binder constant fh4
T{ fh3 aab fh4 abc lf-calc-trans swap rot lf-meta-head lf-const-name s" Trans" nm
   lf-name-same? -> false 510 true }T

\ ---- 4. checkedAssign of a value with an open metavariable of the goal's
\ scope: assigned; the goal itself in it: 98 (the occurs check).
fa fc lf-mk-eq goal constant gca
fb fc lf-mk-eq 0 lf-mctx-view lf-goal-new made constant gstep
T{ gca fh1 eab gstep ebc lf-calc-trans drop drop lf-goal-checked-assign gca open? gstep open?
   -> false true }T
fa fc lf-mk-eq goal constant gocc
T{ gocc dup ' lf-goal-checked-assign catch nip nip authored -> 98 }T
\ An open metavariable beside a local out of the goal's scope (review M1,
\ U1): checkAssignment fails, 98, and the goal stays open.
nat mv-natural lf-mvar-new made constant mopen
nat lf-lctx-local made constant stray
nat goal constant gstray
: stray-val ( -- e ) s" Nat.add" lf-mk-const0 stray lf-mk-app mopen lf-mk-app ;
T{ gstray stray-val ' lf-goal-checked-assign catch nip nip authored gstray open? -> 98 true }T

\ ---- 4. The new public words' stack effects: lf-calc-rel?, the hole's
\ ascription, lf-tac-at and lf-elab-configured outside a run (the mode
\ in force set, and put back after a THROW).
T{ eab lf-calc-rel? ttrue lf-calc-rel? -> true false }T
syn-k-hole 0 syn-new drop constant hole-node
T{ hole-node syn-ascribed? -> false }T
T{ nat hole-node syn-ascribe! hole-node syn-ascribed? swap nat eqv? -> true true }T
T{ ' lf-defeq-mode lf-tr-all lf-tac-at lf-defeq-mode -> lf-tr-all lf-tr-default }T
T{ ' lf-defeq-mode lf-elab-configured -> lf-tr-default }T
T{ ' lf-defeq-mode ' lf-elab-configured lf-tr-reducible lf-tac-at -> lf-tr-reducible }T
T{ ' lf-defeq-flags lf-elab-configured lf-defeq-elab and 0<> -> true }T
: throws7 ( -- ) 7 throw ;
T{ ' throws7 lf-tr-all ' lf-tac-at catch nip nip lf-defeq-mode -> 7 lf-tr-default }T
fresh

\ ---- 1. The words through text: accepted, and Lean's errors.
: h3 ( -- c-addr u )
  s" Nat explicit: a Nat explicit: b Nat explicit: c a b = explicit: h1 b c = explicit: h2 a c =" ;
: hlt ( -- c-addr u )
  s" Nat explicit: a Nat explicit: b Nat explicit: c a b <= explicit: h1 b c < explicit: h2 a c <" ;
T{ h3 s" by-calc[ a b = ' h1 _ c = ' h2 ]" tactic-ran hlt s" by-calc[ a b <= ' h1 _ c < ' h2 ]"
   tactic-ran -> 0 0 }T
T{ h3 s" by-calc[ a b = ' h1 ] ' h2 by-exact" tactic-ran -> 0 }T   \ the last step a goal
T{ h3 s" by-calc[ a b = ' h1 ] by-case: calc.step => ' h2 by-exact by-end" tactic-ran -> 0 }T
T{ h3 s" by-calc[ a b = ?_ _ c = ?_ ] ' h1 by-exact ' h2 by-exact" tactic-ran -> 0 }T
T{ h3 s" by-calc[ a b = ' h1 _ c = ?_ ] by-case: calc_2 => ' h2 by-exact by-end" tactic-ran
   -> 210 }T   \ one ?_ is untagged: no case calc_2
lf-tac-forget
T{ h3 s" by-calc[ a b = ?_ _ c = ?_ ] by-case: calc_2 => ' h2 by-exact by-end ' h1 by-exact"
   tactic-ran -> 0 }T
T{ h3 s" by-calc[ a b = ' h1 a c = ' h2 ]" tactic-ran s" by-calc[" token? -> 513 true }T
lf-tac-forget
T{ h3 s" by-calc[ True ' trivial ]" tactic-ran -> 512 }T
lf-tac-forget
\ h1's type is not T: the elaborator's ensureHasType, a coercion (131).
T{ h3 s" by-calc[ a b = b c = /\ ' h1 ]" tactic-ran -> 131 }T
lf-tac-forget
: hand ( -- c-addr u )
  s" Nat explicit: a Nat explicit: b a b = a b = /\ explicit: h1 a b = a b = /\" ;
: detail-has? ( c-addr u -- flag )
  0 lfa-detail slab-at lfa-detail slab-count 2swap search nip nip ;
T{ hand s" by-calc[ a b = a b = /\ ' h1 _ a b = /\ ' h1 ]" tactic-ran
   s" set_option diagnostics true" detail-has? -> 510 true }T   \ lf-tac-diagnostics.'s hint
lf-tac-forget
\ The new goals in front of the others (review B1; Lean's pushGoals,
\ pinned Lean's trace_state: left.calc_1, left.calc_2, left.calc.step,
\ right): after by-constructor, h2 does not fit the ?_ goal (96).
: hab ( -- c-addr u )
  s" Nat explicit: a Nat explicit: b Nat explicit: c a b = explicit: h1 c c = explicit: h2 a b = c c = /\" ;
T{ hab s" by-constructor by-calc[ a b = ?_ ] ' h2 by-exact ' h1 by-exact" tactic-ran
   s" by-exact" token? -> 96 true }T
lf-tac-forget
T{ hab s" by-constructor by-calc[ a b = ?_ ] ' h1 by-exact ' h2 by-exact" tactic-ran -> 0 }T
: hcc ( -- c-addr u )
  s" Nat explicit: a Nat explicit: b Nat explicit: c a b = explicit: h1 b c = explicit: h2 a c = a c = /\" ;
T{ hcc s" by-constructor by-calc[ a b = ?_ _ c = ?_ ] by-calc[ a b = ' h1 _ c = ' h2 ] by-case: left.calc_2 => ' h2 by-exact by-end ' h1 by-exact"
   tactic-ran -> 96 }T   \ the second calc runs on left.calc_1
lf-tac-forget
T{ hcc s" by-constructor by-calc[ a b = ?_ _ c = ?_ ] ' h1 by-exact ' h2 by-exact by-calc[ a b = ' h1 _ c = ' h2 ]"
   tactic-ran -> 0 }T
\ A natural _ left in the chain (review M2): 461, the next step never runs.
T{ h3 s" by-calc[ a b = _ _ c = ' h2 ] ' h1 by-exact" tactic-ran s" by-calc[" token? -> 461 true }T
lf-tac-forget
T{ h3 s" by-try by-calc[ a b = ' h1 a c = ' h2 ] by-end by-calc[ a b = ' h1 _ c = ' h2 ]"
   tactic-ran -> 0 }T   \ 513 is Lean's: try takes it back
\ Not supported: the goal's type not the chain's (131), a step _ alone (99).
T{ s" Nat explicit: a Nat explicit: b a b = explicit: h1 b a =" s" by-calc[ a b = ' h1 ]"
   tactic-ran -> 131 }T
lf-tac-forget
T{ h3 s" by-calc[ a b = ' h1 _ ' h1 ]" tactic-ran -> 99 }T
lf-tac-forget
\ The last-step extension's other ways out, each 131: a goal that is no
\ relation; no Trans for And with Or; Nat.instTransLtLe's chain a < c for
\ the goal a ≤ c.
T{ s" Nat explicit: a Nat explicit: b a b = explicit: h1 True" s" by-calc[ a b = ' h1 ]"
   tactic-ran -> 131 }T
lf-tac-forget
T{ s" Nat explicit: a Nat explicit: b a b = a b = /\ explicit: h1 a b = a b = \/"
   s" by-calc[ a b = a b = /\ ' h1 ]" tactic-ran -> 131 }T
lf-tac-forget
T{ s" Nat explicit: a Nat explicit: b Nat explicit: c a b < explicit: h1 a c <="
   s" by-calc[ a b < ' h1 ]" tactic-ran -> 131 }T
lf-tac-forget
\ 510's detail is the type with Lean's hint, 511's the type alone.
T{ lfa-e-calc-trans ecl-detail lfa-e-calc-not-rel ecl-detail -> ' ecl-hinted. ' lf-tac-indented. }T

\ ---- 2. Malformed: empty (460), never closed (458), an odd count (99).
T{ h3 s" by-calc[ ]" tactic-ran s" ]" token? -> 460 true }T
lf-tac-forget
T{ h3 s" by-calc[ a b = ' h1" tactic-ran s" by-calc[" token? -> 458 true }T
lf-tac-forget
T{ h3 s" by-calc[ a a b = ' h1 ]" tactic-ran -> 99 }T
lf-tac-forget

\ ---- 1. The transparency blocks.
: hr ( -- c-addr u ) s" Nat explicit: a a a =" ;
: hz ( -- c-addr u ) s" Nat explicit: a a 0 + a =" ;
: hp ( -- c-addr u )
  s" Nat explicit: a Nat explicit: b a Nat.succ Nat.pred b = explicit: h a b =" ;
T{ hr s" by-with-reducible by-rfl by-end" tactic-ran hz s" by-with-unfolding-all by-rfl by-end"
   tactic-ran -> 0 0 }T
T{ hr s" by-with-reducible-and-instances by-rfl by-end" tactic-ran -> 0 }T
T{ hz s" by-with-reducible by-rfl by-end" tactic-ran s" by-rfl" token? -> 97 true }T
lf-tac-forget
T{ hp s" by-with-reducible ' h by-exact by-end" tactic-ran s" by-exact" token? -> 96 true }T
lf-tac-forget
T{ hp s" ' h by-exact" tactic-ran hp s" by-with-unfolding-all ' h by-exact by-end" tactic-ran
   -> 0 0 }T
\ calc's steps elaborated at the block's transparency: h's type is not
\ a = b at reducible (the elaborator's ensureHasType: a coercion, 131).
T{ hp s" by-with-reducible by-calc[ a b = ' h ] by-end" tactic-ran -> 131 }T
lf-tac-forget
T{ hp s" by-calc[ a b = ' h ]" tactic-ran -> 0 }T
T{ hr s" by-with-reducible by-rfl" tactic-ran s" end" token? -> 82 true }T   \ never ended
lf-tac-forget
\ rw's closing rfl is with_reducible rfl (review B2): exact Iff.rfl at
\ reducible leaves Nat.pred (Nat.succ b) = b ↔ b = b open (89), inside
\ with_unfolding_all too; with a = b the goal closes as before.
: hiff ( -- c-addr u )
  s" Nat explicit: a Nat explicit: b a b = explicit: h a Nat.succ Nat.pred b = b b = ↔" ;
T{ hiff s" by-rw[ ' h ]" tactic-ran -> 89 }T
lf-tac-forget
T{ hiff s" by-with-unfolding-all by-rw[ ' h ] by-end" tactic-ran -> 89 }T
lf-tac-forget
: hiff2 ( -- c-addr u ) s" Nat explicit: a Nat explicit: b a b = explicit: h a b = b b = ↔" ;
T{ hiff2 s" by-rw[ ' h ]" tactic-ran -> 0 }T

\ ---- 6. State: the transparency in force at each step.
variable seen
: mode-seen ( i -- ) drop lf-defeq-mode seen ! ;
tac-shape-plain lf-tactic: by-probe-mode constant tac-k-probe-mode
' mode-seen tac-k-probe-mode lf-tactic-action!
T{ hr s" by-with-reducible by-probe-mode by-rfl by-end" tactic-ran seen @ -> 0 lf-tr-reducible }T
T{ hr s" by-with-reducible by-rfl by-end by-probe-mode" tactic-ran seen @ -> 0 lf-tr-default }T
T{ hr s" by-with-unfolding-all by-probe-mode by-rfl by-end" tactic-ran seen @ -> 0 lf-tr-all }T
T{ hr s" by-with-reducible-and-instances by-probe-mode by-rfl by-end" tactic-ran seen @
   -> 0 lf-tr-instances }T
\ Inherited by a block inside; the innermost one's wins.
T{ hr s" by-with-reducible 1 by-iterate by-probe-mode by-end by-rfl by-end" tactic-ran seen @
   -> 0 lf-tr-reducible }T
T{ hr s" by-with-reducible by-with-unfolding-all by-probe-mode by-end by-rfl by-end"
   tactic-ran seen @ -> 0 lf-tr-all }T
\ first's next alternative opens in the loop's handler, outside any step:
\ the frame below's transparency all the same.
T{ hr s" by-with-reducible by-first | by-done | by-probe-mode by-rfl by-end by-end" tactic-ran
   seen @ -> 0 lf-tr-reducible }T
\ After an error try took back: default again (wr_try).
T{ hp s" by-try by-with-reducible ' h by-exact by-end by-end by-probe-mode ' h by-exact"
   tactic-ran seen @ -> 0 lf-tr-default }T
\ After a run that stopped inside a block: nothing left behind.
T{ hp s" by-with-reducible ' h by-exact by-end" tactic-ran lf-defeq-mode -> 96 lf-tr-default }T
lf-tac-forget
\ ... nor any frame (review Low 1): the next authoring run's term proof
\ elaborates at default.
: term-ran ( c-addr u -- code ) lf-author-begin lf-author-text drop lf-author-code ;
: hp-term ( -- c-addr u )
  s" theorem t2 Nat explicit: a Nat explicit: b a Nat.succ Nat.pred b = explicit: h a b = := ' h end t2" ;
T{ hp s" by-with-reducible ' h by-exact by-end" tactic-ran hp-term term-ran -> 96 0 }T
\ lf-tac-at in a run (review B2): the tactics' transparency (the top
\ frame's) is the mode inside, the block's again after, whether xt ends
\ or fails; rw's closing rfl runs in it. lf-tac-transparency! sets a
\ frame's for its later steps.
: tac-seen ( -- ) lf-tac-transparency seen ! ;
: probe-at ( i -- ) drop ['] tac-seen lf-tr-all lf-tac-at ;
tac-shape-plain lf-tactic: by-probe-at constant tac-k-probe-at
' probe-at tac-k-probe-at lf-tactic-action!
: probe-tac ( i -- ) drop tac-seen ;
tac-shape-plain lf-tactic: by-probe-tac constant tac-k-probe-tac
' probe-tac tac-k-probe-tac lf-tactic-action!
: probe-set ( i -- ) drop lf-tr-all lfr-top lf-tac-transparency! ;
tac-shape-plain lf-tactic: by-probe-set constant tac-k-probe-set
' probe-set tac-k-probe-set lf-tactic-action!
T{ hr s" by-probe-at by-rfl" tactic-ran seen @ -> 0 lf-tr-all }T
T{ hr s" by-probe-at by-probe-tac by-rfl" tactic-ran seen @ -> 0 lf-tr-default }T
T{ hiff2 s" by-rw[ ' h ] by-probe-tac" tactic-ran seen @ -> 0 lf-tr-default }T
T{ hiff s" by-rw[ ' h ] by-probe-tac" tactic-ran seen @ -> 89 lf-tr-default }T
lf-tac-forget
T{ hiff2 s" by-with-reducible by-rw[ ' h ] by-probe-tac by-end" tactic-ran seen @
   -> 0 lf-tr-reducible }T
T{ hr s" by-probe-set by-probe-mode by-rfl" tactic-ran seen @ -> 0 lf-tr-all }T
\ A LeanForth scope alone (meta-config.fs's lf-with-reducible) changes the
\ transparency in force, not the tactics'.
: probe-scope ( i -- ) drop ['] tac-seen lf-with-reducible ;
tac-shape-plain lf-tactic: by-probe-scope constant tac-k-probe-scope
' probe-scope tac-k-probe-scope lf-tactic-action!
T{ hr s" by-probe-scope by-rfl" tactic-ran seen @ -> 0 lf-tr-default }T
\ lf-close-main-goal-unchecked: xt's value a new goal of the main goal's
\ type, given as its new goal (lf-tac-new-goals), which comes in front of
\ the others; a natural one with no hole behind it is refused
\ (logUnassignedAndAbort's 95; a hole's is 461, the w-calc-natural text).
: fresh-goal ( type tag -- e goals ) drop mv-opaque lf-mvar-new lf-tac-must dup false lf-tac-new-goals ;
: fresh-natural ( type tag -- e goals ) drop mv-natural lf-mvar-new lf-tac-must dup false lf-tac-new-goals ;
: probe-close ( i -- ) ['] fresh-goal lf-close-main-goal-unchecked ;
: probe-natural ( i -- ) ['] fresh-natural lf-close-main-goal-unchecked ;
tac-shape-plain lf-tactic: by-probe-close constant tac-k-probe-close
' probe-close tac-k-probe-close lf-tactic-action!
tac-shape-plain lf-tactic: by-probe-natural constant tac-k-probe-natural
' probe-natural tac-k-probe-natural lf-tactic-action!
T{ hab s" by-constructor by-probe-close ' h1 by-exact ' h2 by-exact" tactic-ran -> 0 }T
T{ hab s" by-constructor by-probe-close ' h2 by-exact" tactic-ran -> 96 }T
lf-tac-forget
T{ hab s" by-constructor by-probe-natural ' h1 by-exact" tactic-ran -> 95 }T
lf-tac-forget

\ ---- 5. Resources: lf-calc-trans directly, every heap allocation refused
\ in turn, in the same context; then each tactic through text.
: frames-anew ( -- )
  ecl-trans-frames sweep-slab-anew ecl-step-frames sweep-slab-anew
  tng-frames sweep-slab-anew lfa-brackets sweep-slab-anew ;
fresh
nat s" a" binder constant wa
nat s" b" binder constant wb
nat s" c" binder constant wcz
wa wb lf-mk-eq s" h1" binder constant wh1
wb wcz lf-mk-eq s" h2" binder constant wh2
sweep-keep-view
: context-anew ( -- ) frames-anew sweep-view-anew ;
' context-anew sweep-slabs-xt !
: s-trans ( -- code )
  wh1 wa wb lf-mk-eq wh2 wb wcz lf-mk-eq lf-calc-trans nip nip ;
: d1 ( x -- n outcome ) drop ['] s-trans 0 1 lf-meta-catch ;
T{ 0 ' d1 heap-sweep swept? -> true }T
' frames-anew sweep-slabs-xt !
: p-calc ( x -- code outcome ) drop h3 s" by-calc[ a b = ' h1 _ c = ' h2 ]" text-full ;
: p-ext ( x -- code outcome ) drop h3 s" by-calc[ a b = ?_ ] ' h1 by-exact ' h2 by-exact" text-full ;
: p-wr ( x -- code outcome )
  drop hp s" by-try by-with-reducible ' h by-exact by-end by-end ' h by-exact" text-full ;
T{ 0 ' p-calc heap-sweep swept? 0 ' p-ext heap-sweep swept?
   0 ' p-wr heap-sweep swept? -> true true true }T
lf-tac-forget
.( batch-small-2 test.fs: all tests passed) cr

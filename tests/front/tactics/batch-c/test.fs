\ Unit tests of tactic batch 2b (plan row TB2) over decide's slice of Init
\ in an authoring run, by the classes of docs/development/
\ TEST_COVERAGE_REVIEW.md: the reader's <-, tac-shape-list, by-next and
\ by-case: _ (tactic-syntax.fs, read as records); tactic-api.fs's
\ lf-tactic-seq:; tactic-core.fs's lf-tac-arg-symm?, lf-tac-row,
\ lf-tac-rfl-reducible and lf-goals2; app-builder.fs's lf-mk-not; the goal
\ operations meta-tactic/symm.fs's lf-goal-symm, by-cases.fs's
\ lf-goal-by-cases, lf-decidable-instance and lf-mk-decidable, repeat.fs's
\ lf-goals-repeat and lf-goals-repeat-n; and each tactic word of the batch
\ through LeanForth text (tests/support/tactic-text.fs):
\ 1. outcomes: each word accepted, each refusal with its code (215, 381,
\    89, 96, 451, 90), each case not ported (99, 93);
\ 2. malformed input: <- outside a bracket of rules, with no rule before
\    it, twice, inside by-exacts[; by-next with no =>; _ for a name;
\    lf-tactic-seq: with no kind or a number that is no kind (the load
\    aborts);
\ 3. stack effects: each T{ }T checks the depth; the records' fields (the
\    rules' symm flags, the shapes, by-next's tag);
\ 5. resources (tests/support/meta-sweeps.fs): lf-goal-symm,
\    lf-goal-by-cases, lf-decidable-instance and lf-goals-repeat with
\    every heap allocation refused in turn and with room for every count
\    of terms in turn, and by-cases:, by-contra:, by-and-intros and
\    by-rwa[ through their text with every heap allocation refused: the
\    answer or full, never another answer (an instance search refused is
\    never Classical.propDecidable; a refusal inside an alternative is
\    never the next alternative; f refused inside repeat' is never "f
\    failed");
\ 6. state: the goal assigned, the new goals' tags, kinds and contexts,
\    an undone f's assignment, the frames and the current view put back.
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
: made ( x outcome -- x ) ok? 0= abort" batch-c test: not made" ;
lf-meta-throw-base outcome-invalid - constant thrown-invalid
lf-meta-throw-base outcome-unsupported - constant thrown-unsupported
lf-meta-throw-base outcome-full - constant thrown-full
: nat ( -- t ) s" Nat" lf-mk-const0 ;
: fresh ( -- ) lf-view-empty lf-mctx-view! ;
: local+ ( type c-addr u -- fvar )
  lfa-intern swap lf-lctx-local made tuck swap 0 lf-local-new made
  lf-mctx-view swap lf-view-push made lf-mctx-view! ;
: goal ( type -- goal ) 0 lf-mctx-view lf-goal-new made ;
: tagged ( type -- goal ) goal dup s" t" lfa-intern lf-mvar-tag! made ;
: le ( x y -- t ) s" LE.le" 2swap 2 lf-mk-app-m ;
: nm ( c-addr u -- id ) lfa-intern ;
: open? ( mvar -- flag ) lf-goal-assigned? 0= ;
: newest# ( goal -- view k ) lf-goal-view dup lf-view-count 1- ;
: newest-name ( goal -- name ) newest# lf-view-local lf-local-name ;
: newest-type ( goal -- type ) newest# lf-view-fvar lf-fvar-type ;
: eqv? ( t s -- flag ) lf-meta-eqv made ;
\ An application's argument j counted from the last (0).
: arg-k ( app j -- x ) 0 ?do lf-term-first@ loop lf-term-second@ ;
\ The authoring code a word ( x -- y ) or ( x -- ) threw, else 0.
: code1 ( x xt -- code ) catch if drop lf-author-code else drop 0 then ;
: code0 ( x xt -- code ) catch if drop lf-author-code else 0 then ;
: detail-has? ( c-addr u -- flag )
  0 lfa-detail slab-at lfa-detail slab-count 2swap search nip nip ;
: rel2 ( p q c-addr u -- t ) lf-mk-const0 rot lf-mk-app swap lf-mk-app ;

\ ---- 3. Records: the rules' symm flags, the shapes, by-next's tag.
: vars ( -- c-addr u ) s" Nat explicit: a Nat explicit: b " ;
create stmt 512 allot  variable stmt#
: stmt+ ( c-addr u -- ) tuck stmt stmt# @ + swap move stmt# +! ;
: st ( c-addr u -- c-addr' u' ) 0 stmt# ! vars stmt+ stmt+ stmt stmt# @ ;
: step@ ( i -- addr ) lf-tactic-step ;
: symm@ ( i k -- flag ) swap step@ tac-first @ + lf-tactic-arg-symm? ;
: hab ( -- c-addr u ) s" a b = explicit: h b a = explicit: h2 b a =" st ;
T{ hab s" by-rw[ ' h ' h <- ]" tactic-ran -> 0 }T
T{ 1 step@ tac-count @ 1 0 symm@ 1 1 symm@ 1 step@ tac-shape @ tac-shape-rules =
   -> 2 false true true }T
T{ 1 0 lf-tac-arg-symm? 1 1 lf-tac-arg-symm? -> false true }T
\ A rule after a <- comes after the rules before it (the bracket's values
\ appended), left to right.
T{ hab s" by-rewrite[ ' h <- ' h ' h <- ' h ] by-rfl" tactic-ran 1 step@ tac-count @
   -> 0 4 }T
T{ 1 0 symm@ 1 1 symm@ 1 2 symm@ 1 3 symm@ -> true false true false }T
T{ 1 2 lf-tac-arg syn-kind@ 1 3 lf-tac-arg syn-kind@ -> syn-k-var syn-k-var }T
lf-tac-forget
\ 2. Malformed: <- outside a bracket (83), with no rule before it (86),
\ twice (86), in by-exacts[ (83: no rules); by-exacts['s values are terms.
T{ hab s" ' h <- by-exact" tactic-ran -> 83 }T
T{ hab s" by-rw[ <- ]" tactic-ran -> 86 }T
T{ hab s" by-rw[ ' h <- <- ]" tactic-ran -> 86 }T
T{ hab s" by-exacts[ ' h <- ]" tactic-ran -> 83 }T
T{ hab s" by-exacts[ ' h2 ]" tactic-ran 1 step@ tac-shape @ tac-shape-list = -> 0 true }T
T{ s" a b ≤ explicit: h1 b a ≤ explicit: h2 a b ≤ b a ≤ ∧" st
   s" ' And.intro by-apply by-next => ' h1 by-exact by-end ' h2 by-exact" tactic-ran
   2 step@ dup tac-kind @ swap tac-name @ 2 step@ tac-arrow @ 0< -> 0 tac-k-case 0 false }T
T{ s" a b ≤ explicit: h1 a b ≤" st s" by-case: _ => ' h1 by-exact by-end" tactic-ran
   1 step@ tac-name @ -> 0 0 }T
\ by-next with no =>: the line ends first (84); an alternative's | _ is
\ still Lean's wildcard alternative, not supported yet (72).
T{ hab s" by-next" tactic-ran -> 84 }T
T{ s" Nat explicit: n n n =" st s" n by-induction-with | _ => by-rfl by-end" tactic-ran
   -> 72 }T
\ The shapes: by-exacts[ a bracket of values, by-rwa[ of rules.
T{ tac-shape-list lft-bracket-shape? tac-shape-rules lft-bracket-shape?
   tac-shape-plain lft-bracket-shape? 0 lft-bracket-shape? -> true true false false }T
lf-tac-forget

\ ---- lf-tactic-seq:: rows in order on one step. constructor, then
\ assumption: the left goal closed; the other order fails (381, Lean's
\ assumption on the And goal).
tac-k-constructor tac-k-assumption 2 tac-shape-plain lf-tactic-seq: by-test-ca
  constant tac-k-test-ca
tac-k-assumption tac-k-constructor 2 tac-shape-plain lf-tactic-seq: by-test-ac
  constant tac-k-test-ac
: hand ( -- c-addr u ) s" a b ≤ explicit: h1 b a ≤ explicit: h2 a b ≤ b a ≤ ∧" st ;
T{ hand s" by-test-ca ' h2 by-exact" tactic-ran -> 0 }T
T{ hand s" by-test-ac ' h2 by-exact" tactic-ran -> 381 }T
T{ tac-k-test-ca lf-tactic-shape@ tac-k-test-ca lf-tactic-run? -> tac-shape-plain true }T
lf-tac-forget
\ 2. No kind, or a number that is no kind: the load aborts (-2) before
\ lf-tactic: makes a row (tap-seq-kinds is what lf-tactic-seq: runs first).
T{ 0 ' tap-seq-kinds catch nip -> -2 }T
T{ 9999 1 ' tap-seq-kinds catch nip nip -> -2 }T

\ ---- lf-mk-not, lf-goals2, lf-mk-decidable.
fresh
nat s" a" local+ constant fa
nat s" b" local+ constant fb
fa fb le constant ab-le
fb fa le constant ba-le
T{ ab-le lf-mk-not dup 1 s" Not" lf-meta-app-of? swap lf-term-second@ ab-le = -> true true }T
T{ ab-le lf-mk-decidable dup 1 s" Decidable" lf-meta-app-of? swap lf-term-second@ ab-le =
   -> true true }T
ab-le goal constant ga  ba-le goal constant gb
T{ ga gb lf-goals2 dup run-count over 0 run@ rot 1 run@ -> 2 ga gb }T

\ ---- lf-decidable-instance: Nat.decLe a b found; Nonempty Nat has none:
\ Classical.propDecidable (Nonempty Nat).
s" Nonempty" nat 1 lf-mk-app-m constant ne-nat
: classical? ( inst -- flag ) 1 s" Classical.propDecidable" lf-meta-app-of? ;
T{ ab-le lf-decidable-instance lf-meta-head s" Nat.decLe" lf-meta-const-named? -> true }T
T{ ne-nat lf-decidable-instance dup classical? swap lf-term-second@ ne-nat eqv? -> true true }T

\ ---- lf-goal-symm: a = b to b = a, the goal assigned @Eq.symm.{1} Nat b
\ a ?h (its a := b and b := a), ?h the new goal (natural, the goal's tag,
\ of type b = a).
fa fb lf-mk-eq constant ab-eq
fb fa lf-mk-eq constant ba-eq
ab-eq tagged constant gs1
gs1 lf-goal-symm constant gs1'
T{ gs1' lf-goal-type lf-instantiate! ba-eq eqv? gs1' lf-goal-tag s" t" nm =
   gs1' lf-goal-kind mv-natural = -> true true true }T
T{ gs1 open? gs1 lf-instantiate! dup 4 s" Eq.symm" lf-meta-app-of? swap 0 arg-k gs1' =
   -> false true true }T
T{ gs1 lf-instantiate! dup 1 arg-k fa = swap 2 arg-k fb = -> true true }T
\ Iff, Ne, HEq, And, Or by their lemmas; ¬(a ≤ b) is no relation of two
\ (451), a ≤ b has no lemma (99), a conclusion that does not fit 99.
: symm-head? ( t c-addr u -- flag ) rot tagged dup lf-goal-symm drop lf-instantiate!
  lf-meta-head -rot lf-meta-const-named? ;
T{ ab-le ba-le s" Iff" rel2 s" Iff.symm" symm-head? -> true }T
T{ s" Ne" fa fb 2 lf-mk-app-m s" Ne.symm" symm-head? -> true }T
T{ s" HEq" fa fb 2 lf-mk-app-m s" HEq.symm" symm-head? -> true }T
T{ ab-le ba-le s" And" rel2 s" And.symm" symm-head? -> true }T
T{ ab-le ba-le s" Or" rel2 s" Or.symm" symm-head? -> true }T
: symm-code ( t -- code ) tagged ['] lf-goal-symm code1 ;
T{ ab-le lf-mk-not symm-code s\"   \xc2\xaca \xe2\x89\xa4 b" detail-has? -> 451 true }T
lf-tac-forget
T{ ab-le symm-code -> 99 }T
lf-tac-forget
T{ false ' msy-fit code0 true ' msy-fit code0 -> 99 0 }T
lf-tac-forget
\ getSymmLems' table: each relation's lemma, none for LE.le.
: lemma-of ( c-addr u -- c-addr' u' true | false ) lf-mk-const0 msy-lemma ;
T{ s" Eq" lemma-of >r s" Eq.symm" compare r> -> 0 true }T
T{ s" Or" lemma-of >r s" Or.symm" compare r> -> 0 true }T
T{ s" LE.le" lemma-of -> false }T
T{ msy-pairs# 0 msy-pair 2drop s" Eq" compare -> 6 0 }T

\ ---- lf-goal-by-cases: the dite and its goals pos (h : p) and neg (h :
\ ¬p), the frames and the current view put back.
ab-le tagged constant gc
lf-mctx-view constant view-c
gc s" h" nm ab-le dup lf-decidable-instance lf-goal-by-cases constant gneg constant gpos
T{ gpos lf-goal-tag s" pos" nm = gneg lf-goal-tag s" neg" nm = gpos open? gneg open?
   -> true true true true }T
T{ gpos lf-goal-type ab-le eqv? gneg lf-goal-type ab-le eqv? gpos lf-goal-kind mv-opaque =
   -> true true true }T
T{ gpos newest-name s" h" nm = gpos newest-type ab-le eqv? -> true true }T
T{ gneg newest-name s" h" nm = gneg newest-type ab-le lf-mk-not eqv? -> true true }T
T{ gpos lf-goal-view lf-view-count view-c lf-view-count 1+ = mbc-frames slab-count
   lf-mctx-view view-c = -> true 0 true }T
gc lf-instantiate! constant dite-c
T{ dite-c 5 s" dite" lf-meta-app-of? dite-c 4 arg-k ab-le eqv? dite-c 3 arg-k ab-le eqv?
   -> true true true }T
T{ dite-c 2 arg-k lf-meta-head s" Nat.decLe" lf-meta-const-named? -> true }T
T{ dite-c 1 arg-k dup lf-term-lam? swap lf-term-first@ ab-le eqv? -> true true }T
T{ dite-c 0 arg-k dup lf-term-lam? swap lf-term-first@ ab-le lf-mk-not eqv? -> true true }T
T{ dite-c 0 arg-k lf-binder-name s" h" nm = dite-c 1 arg-k lf-binder-name s" h" nm =
   -> true true }T
\ An assigned goal: invalid, before any branch is made.
: cases-again ( -- ) gc s" h" nm ab-le dup lf-decidable-instance lf-goal-by-cases 2drop ;
T{ ' cases-again catch mbc-frames slab-count -> thrown-invalid 0 }T

\ ---- lf-goals-repeat with and_intros' f (tactics/and-intros.fs's
\ tai-in): a ∧ (b ∧ c) gives the goals a, b, c depth first; at most one
\ call of f: a and b ∧ c; none: the goal itself; a goal f fails on, and
\ an assigned one, kept and dropped; f's refusal thrown on; f's failure
\ undone.
: and2 ( p q -- t ) s" And" rel2 ;
fa fa le constant aa-le
ba-le aa-le and2 constant t2
ab-le t2 and2 constant t3
: goals1 ( t -- goals ) tagged lf-goals1 ;
\ goal k of goals has type t.
: type-at? ( goals k t -- goals flag ) >r over swap run@ lf-goal-type r> eqv? ;
T{ t3 goals1 ' tai-in lf-goals-repeat dup run-count swap 0 ab-le type-at? swap
   1 ba-le type-at? swap 2 aa-le type-at? nip -> 3 true true true }T
\ Their tags: t.refine_1, t.refine_2.refine_1, t.refine_2.refine_2 (refine's).
: tag-at ( goals k -- name ) run@ lf-goal-tag ;
: tag+ ( name c-addr u -- name' ) nm lf-name-append-tag ;
s" t" nm s" refine_1" tag+ constant tag-1
s" t" nm s" refine_2" tag+ s" refine_2" tag+ constant tag-22
T{ t3 goals1 ' tai-in lf-goals-repeat dup 0 tag-at tag-1 = swap 2 tag-at tag-22 =
   -> true true }T
T{ t3 goals1 ' tai-in 1 lf-goals-repeat-n dup run-count swap 0 ab-le type-at? swap
   1 t2 type-at? nip -> 2 true true }T
T{ t3 goals1 ' tai-in 0 lf-goals-repeat-n dup run-count swap 0 t3 type-at? nip -> 1 true }T
T{ ab-le goals1 ' tai-in lf-goals-repeat dup run-count swap 0 ab-le type-at? nip -> 1 true }T
ab-le goal constant gdone
T{ gdone fa lf-mvar-assign 0 gdone run-push made ' tai-in lf-goals-repeat run-count
   -> outcome-ok 0 }T
\ (with no call of f left, the goals not visited are given back less the
\ assigned ones)
T{ 0 gdone run-push made ' tai-in 0 lf-goals-repeat-n run-count -> 0 }T
: f-full ( goal -- goals true | false ) drop outcome-full lf-must 0 true ;
T{ ab-le goals1 ' f-full ' lf-goals-repeat catch nip nip -> thrown-full }T
\ f assigns its goal, then fails: the assignment undone, the goal kept.
: f-undone ( goal -- false ) fa lf-mvar-assign drop false ;
ab-le goal constant gu
T{ 0 gu run-push made ' f-undone lf-goals-repeat dup run-count swap 0 run@ gu = gu open?
   mrp-frames slab-count -> 1 true true 0 }T

\ ---- 5. Resources: each goal operation on a new goal with every heap
\ allocation refused in turn (the frame slabs given back first) and with
\ room for every count of terms in turn: the answer or full, never
\ another answer.
: frames-anew ( -- ) mbc-frames sweep-slab-anew mrp-frames sweep-slab-anew
  tl-frames sweep-slab-anew ;
' frames-anew sweep-slabs-xt !
: caught ( x xt -- y outcome ) 1 1 lf-meta-catch ;
\ (a refusal thrown, not aborted: the sweeps' scenarios make their goals so)
: new-goal ( type -- goal ) 0 lf-mctx-view lf-goal-new lf-must ;
: s-symm ( type -- type' ) new-goal lf-goal-symm lf-goal-type lf-instantiate! ;
ab-le lf-decidable-instance constant inst-le
: s-cases ( type -- dite? )
  new-goal dup s" h" nm ab-le inst-le lf-goal-by-cases 2drop lf-instantiate!
  5 s" dite" lf-meta-app-of? ;
: s-inst ( type -- inst ) lf-decidable-instance ;
: s-repeat ( type -- n ) new-goal 0 swap run-push lf-must ['] tai-in lf-goals-repeat run-count ;
: p-symm ( type -- type' outcome ) ['] s-symm caught ;
: p-cases ( type -- dite? outcome ) ['] s-cases caught ;
: p-inst ( type -- inst outcome ) ['] s-inst caught ;
: p-repeat ( type -- n outcome ) ['] s-repeat caught ;
: both-swept ( type xt -- heap? room? )
  2dup heap-sweep swept? >r room-sweep swept? r> swap ;
T{ ab-eq ' p-symm both-swept ab-le ' p-cases both-swept -> true true true true }T
T{ t3 ' p-repeat both-swept -> true true }T
\ An instance search refused is never Classical.propDecidable: a ≤ b's
\ answer is Nat.decLe or full.
T{ ab-le ' p-inst heap-sweep swept? -> true }T

\ ---- 1. The tactics through LeanForth text.
\ rwa: rfl closes (h, then ← h); assumption closes (b = c by h2);
\ assumption's 381 (c = b is no b = c); a rule's 215; rfl on ≤, 93.
T{ s" a b = explicit: h a b =" st s" by-rwa[ ' h ]" tactic-ran -> 0 }T
T{ s" a b = explicit: h b b = explicit: h2 b a =" st s" by-rwa[ ' h <- ]" tactic-ran -> 0 }T
T{ s" Nat explicit: c a b = explicit: h b c = explicit: h2 a c =" st s" by-rwa[ ' h ]"
   tactic-ran -> 0 }T
T{ s" Nat explicit: c a b = explicit: h c b = explicit: h2 a c =" st s" by-rwa[ ' h ]"
   tactic-ran -> 381 }T
T{ s" a b = explicit: h a 0 + a =" st s" by-rwa[ ' h <- ]" tactic-ran -> 215 }T
T{ s" Nat explicit: c a b = explicit: h b c ≤ explicit: h2 a c ≤" st s" by-rwa[ ' h ]"
   tactic-ran -> 93 }T
lf-tac-forget
\ exacts: two terms, none, too few (89), a mismatch (96), no goal (90).
T{ hand s" ' And.intro by-apply by-exacts[ ' h1 ' h2 ]" tactic-ran -> 0 }T
T{ hand s" ' And.intro by-apply by-exacts[ ' h1 ]" tactic-ran -> 89 }T
T{ hand s" ' And.intro by-apply by-exacts[ ' h1 ] ' h2 by-exact" tactic-ran -> 89 }T
T{ hand s" ' And.intro by-apply by-exacts[ ' h2 ' h1 ]" tactic-ran -> 96 }T
T{ s" a b ≤ explicit: h1 a b ≤" st s" ' h1 by-exact by-exacts[ ]" tactic-ran -> 0 }T
T{ s" a b ≤ explicit: h1 a b ≤" st s" ' h1 by-exact by-exacts[ ' h1 ]" tactic-ran -> 90 }T
lf-tac-forget
\ by-cases: decidable, classical, h named in both goals; no Prop (99), _
\ for the name (99), a term left open (93).
: hle ( -- c-addr u ) s" a b ≤ explicit: h1 a b ≤" st ;
T{ hle s" a b ≤ by-cases: h ' h by-exact ' h by-absurd ' h1 by-exact" tactic-ran -> 0 }T
T{ s" Nat Nonempty explicit: hp Nat Nonempty" st
   s" Nat Nonempty by-cases: h ' h by-exact ' h by-absurd ' hp by-exact" tactic-ran -> 0 }T
T{ hle s" a b ≤ by-cases: h ' h1 by-exact ' h1 by-exact" tactic-ran -> 0 }T
T{ hle s" a by-cases: h" tactic-ran -> 99 }T
T{ hle s" a b ≤ by-cases: _" tactic-ran -> 99 }T
T{ hle s" ' Nat.le_trans by-cases: h" tactic-ran -> 93 }T
T{ hle s" a b ≤ by-cases: h by-case: neg => ' h by-absurd ' h1 by-exact by-end ' h by-exact"
   tactic-ran -> 0 }T
lf-tac-forget
\ by-contra: the three alternatives (¬p by change, a decidable p, a
\ classical p), this, by-contra-core alone, a ≠; a goal False (96 after).
T{ s" a b ≤ ¬ explicit: h a b ≤ ¬" st s" by-contra: k ' k by-absurd by-assumption"
   tactic-ran -> 0 }T
\ (the change alternative first: k : a ≤ b, not ¬¬(a ≤ b))
T{ s" a b ≤ ¬ explicit: h a b ≤ ¬" st
   s" by-contra: k a b ≤ ' k by-have: k2 ' k2 by-absurd by-assumption" tactic-ran -> 0 }T
T{ hle s" by-contra: k ' k by-absurd ' h1 by-exact" tactic-ran -> 0 }T
T{ s" Nat Nonempty explicit: h Nat Nonempty" st s" by-contra ' this by-absurd ' h by-exact"
   tactic-ran -> 0 }T
T{ s" a b ≠ explicit: h a b ≠" st s" by-contra-core by-intro: k ' k by-absurd by-assumption"
   tactic-ran -> 0 }T
T{ hle s" by-contra: k ' h1 by-exact" tactic-ran -> 96 }T
T{ hle s" by-contra: rfl" tactic-ran -> 99 }T
lf-tac-forget
\ symm, and_intros, next through the text; next with no goal: 90.
T{ s" a b = explicit: h b a =" st s" by-symm ' h by-exact" tactic-ran -> 0 }T
T{ s" a b ≤ ¬ explicit: h a b ≤ ¬" st s" by-symm" tactic-ran -> 451 }T
T{ s" a b ≤ explicit: h b a ≤" st s" by-symm" tactic-ran -> 99 }T
T{ hand s" by-and-intros ' h1 by-exact ' h2 by-exact" tactic-ran -> 0 }T
T{ hand s" by-and-intros ' h2 by-exact" tactic-ran -> 96 }T
T{ hand s" ' And.intro by-apply by-next => ' h1 by-exact by-end ' h2 by-exact" tactic-ran
   -> 0 }T
T{ s" a b ≤ explicit: h1 a b ≤" st s" ' h1 by-exact by-next => ' h1 by-exact by-end"
   tactic-ran -> 90 }T
T{ s" a b ≤ explicit: h a b ≤" st s" ' h by-revert by-intro: _ by-next k => ' k by-exact by-end"
   tactic-ran -> 0 }T
lf-tac-forget

\ ---- 5. Through the text, every heap allocation of the run refused in turn:
\ accepted, or full (60, 88 or another out of room), never another error
\ (a refusal inside an alternative of by-contra-core is never the next
\ alternative, nor one inside f an f that failed).
: full-code? ( code -- flag ) dup if lf-author-outcome outcome-full = then ;
: text-full ( c-addr u c-addr' u' -- code outcome )
  tactic-ran dup full-code? if drop -1 outcome-full else outcome-ok then ;
: p-cases-text ( x -- code outcome )
  drop hle s" a b ≤ by-cases: h ' h by-exact ' h by-absurd ' h1 by-exact" text-full ;
: p-contra-text ( x -- code outcome ) drop hle s" by-contra: k ' k by-absurd ' h1 by-exact"
  text-full ;
T{ 0 ' p-cases-text heap-sweep swept? 0 ' p-contra-text heap-sweep swept? -> true true }T
lf-tac-forget
.( batch-c test.fs: all tests passed) cr

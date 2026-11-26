\ Unit tests of small tactics 1 (plan row TB2) over decide's slice of
\ Init in an authoring run, by the classes of docs/development/
\ TEST_COVERAGE_REVIEW.md: the goal layer's new words, each called on
\ goals built here (meta-tactic/apply.fs's lf-goal-apply-const,
\ generalize.fs's lf-goal-generalize-eq and lf-goal-generalize-hyp), and
\ the tactic words through their text (tests/support/tactic-text.fs):
\ by-funext, by-funext[ ], by-infer-instance, by-rename:, by-generalize:,
\ by-generalize-eq: (with at[ ]), by-skip, by-done:
\ 1. outcomes: each word accepted; 89, 110, 125, 380, 460, 482 with their
\    places; each case not ported (99, 93, 119: unsupported);
\ 2. malformed input: an unclosed by-funext[, a by-rename: with no type,
\    an assigned goal, two pairs for the equation form;
\ 3. records: the shapes and rows, Lean's names, the codes;
\ 4. interfaces: the constant at new levels (the same term as
\    lf-mk-const0 for one without universe parameters), the new goals,
\    their types and names, the hypotheses reverted and put back, the
\    newest hypothesis renamed;
\ 5. resources: every heap allocation refused in turn, each library
\    word called directly and each tactic through its text
\    (tests/support/meta-sweeps.fs): the answer or full;
\ 6. state: rename's search undone (its metavariables and assignments)
\    and one metavariable depth deeper (482 for k : a = ?w), a refused
\    goal left unassigned; trivial's apply on the shared word.
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
: made ( x outcome -- x ) ok? 0= abort" batch-small-1 test: not made" ;
lf-meta-throw-base outcome-invalid - constant thrown-invalid
lf-meta-throw-base outcome-unsupported - constant thrown-unsupported
: authored ( code -- n ) dup lf-author-throw = if drop lf-author-code lf-tac-forget then ;
: code2 ( x y xt -- code ) catch dup if nip nip then authored ;
: code3 ( x y z xt -- code ) catch dup if >r 2drop drop r> then authored ;
: code4 ( w x y z xt -- code ) catch dup if >r 2drop 2drop r> then authored ;
: token ( -- c-addr u ) lfa-error lfa-err-token lfa-error lfa-err-length @ ;
: token? ( c-addr u -- flag ) token compare 0= ;
: nat ( -- t ) s" Nat" lf-mk-const0 ;
: fresh ( -- ) lf-view-empty lf-mctx-view! ;
: binder ( type c-addr u -- fvar )
  lfa-intern swap lf-lctx-local made tuck swap 0 lf-local-new made
  lf-mctx-view swap lf-view-push made lf-mctx-view! ;
: goal ( type -- goal ) 0 lf-mctx-view lf-goal-new made ;
: nm ( c-addr u -- name ) lfa-intern ;
: view# ( goal -- n ) lf-goal-view lf-view-count ;
: local-at ( goal i -- local ) swap lf-goal-view swap lf-view-local ;
: named? ( goal i c-addr u -- flag ) 2>r local-at lf-local-name 2r> nm lf-name-same? ;
: type-at ( goal i -- type ) local-at lf-local-fvar lf-fvar-type ;
: open? ( goal -- flag ) lf-goal-assigned? 0= ;
: eqv? ( a b -- flag ) lf-meta-eqv made ;
: and-of ( p q -- t ) s" And" 2swap 2 lf-mk-app-m ;
: pair ( e c-addr u -- args ) nm lf-run2 ;

\ ---- 3. Records: shapes, rows, Lean's names, the codes.
T{ tac-k-funext lf-tactic-shape@ tac-k-funext-names lf-tactic-shape@ tac-k-skip lf-tactic-shape@
   -> tac-shape-plain tac-shape-binders+ tac-shape-plain }T
T{ tac-k-done lf-tactic-shape@ tac-k-infer-instance lf-tactic-shape@ -> tac-shape-plain tac-shape-plain }T
: shape3 ( kind -- want names at ) lf-tactic-shape@ dup shape-want @ over shape-names @ rot shape-at @ ;
T{ tac-k-rename shape3 tac-k-generalize shape3 tac-k-generalize-eq shape3
   -> 1 1 false 1 1 true 1 2 true }T
: lean? ( kind c-addr u -- flag ) rot lf-tac-lean compare 0= ;
T{ tac-k-funext s" funext" lean? tac-k-funext-names s" funext" lean? tac-k-skip s" skip" lean?
   -> true true true }T
T{ tac-k-done s" done" lean? tac-k-infer-instance s" infer_instance" lean? tac-k-rename s" rename" lean?
   -> true true true }T
T{ tac-k-generalize s" generalize" lean? tac-k-generalize-eq s" generalize" lean? -> true true }T
T{ lfa-e-rename -> 482 }T

\ ---- 4. lf-goal-apply-const: the constant at new levels, apply's goals.
fresh
T{ s" And.intro" lfa-intern lf-menv-find made lf-meta-const-fresh made
   s" And.intro" lf-mk-const0 eqv? -> true }T
s" True" lf-mk-const0 constant ttrue
ttrue ttrue and-of goal constant ga
ga s" And.intro" lf-goal-apply-const constant gs
: gtype ( goal -- t ) lf-goal-type lf-instantiate! ;
T{ gs run-count gs 0 run@ gtype ttrue eqv? gs 1 run@ gtype ttrue eqv? ga open? -> 2 true true false }T
\ The same value as apply of lf-mk-const0's term (trivial's word before).
ttrue ttrue and-of goal constant gb
gb s" And.intro" lf-mk-const0 lf-goal-apply-named drop
T{ ga lf-instantiate! gb lf-instantiate! lf-meta-equal? made -> false }T   \ new goals differ
: head4 ( e -- f ) lf-term-first@ lf-term-first@ lf-term-first@ lf-term-first@ ;
T{ ga lf-instantiate! head4 gb lf-instantiate! head4 eqv? ga lf-instantiate! head4 s" And.intro" lf-mk-const0 eqv? -> true true }T
\ funext, a constant with universe parameters: one goal, ∀ x, f x = g x.
s" Nat.succ" lf-mk-const0 dup lf-mk-eq goal constant gf
gf s" funext" lf-goal-apply-const constant fs
T{ fs run-count fs 0 run@ lf-goal-type lf-term-pi? gf open? -> 1 true false }T
\ No fit: Lean's 380; a name no declaration has: thrown invalid; assigned: invalid.
T{ ttrue goal dup s" funext" ' lf-goal-apply-const code3 swap open? -> 380 true }T   \ left open
T{ ttrue goal s" No.such" ' lf-goal-apply-const code3 -> thrown-invalid }T
T{ ga s" And.intro" ' lf-goal-apply-const code3 -> thrown-invalid }T

\ ---- 4. lf-goal-generalize-eq: x and h : e = x, the goal x = b.
fresh
nat s" a" binder constant fa
nat s" b" binder constant fb
nat s" c" binder constant fc
fa fb lf-mk-eq goal constant ge
ge fa s" x" pair s" h" nm lf-goal-generalize-eq constant ge' constant xs
T{ xs run-count ge' view# ge' 3 s" x" named? ge' 4 s" h" named? ge open? -> 2 5 true true false }T
T{ ge' lf-goal-type xs 0 run@ fb lf-mk-eq eqv? ge' 4 type-at fa xs 0 run@ lf-mk-eq eqv?
   xs 1 run@ ge' 4 local-at lf-local-fvar = -> true true true }T
\ The goal assigned ?g a (Eq.refl a): its last argument the proof.
T{ ge lf-mvar-value drop dup lf-term-second@ fa lf-mk-eq-refl eqv? swap lf-term-first@ lf-term-second@ fa = -> true true }T
\ Two pairs: unsupported; an assigned goal: invalid.
T{ fa fb lf-mk-eq goal fa s" x" pair fb lf-run+ s" y" nm lf-run+ s" h" nm
   ' lf-goal-generalize-eq code3 -> thrown-unsupported }T
T{ ge fa s" x" pair s" h" nm ' lf-goal-generalize-eq code3 -> thrown-invalid }T
\ A name not given: the hidden x (lf-goal-generalize's mgz-name).
T{ fa fb lf-mk-eq goal fa 0 lf-run2 s" h" nm lf-goal-generalize-eq nip 3 s" x" named? -> true }T

\ ---- 4. lf-goal-generalize-hyp: h reverted, generalized, put back.
fa fc lf-mk-eq s" h" binder constant fh
fc fc lf-mk-eq s" hc" binder constant fhc
fa fb lf-mk-eq goal constant gh
gh fa s" x" pair 0 fh lf-run1 lf-goal-generalize-hyp constant gh' constant hx
\ a b c hc x h: h after x, of type x = c; the goal x = b.
T{ hx run-count gh' view# gh' 4 s" x" named? gh' 5 s" h" named? -> 1 6 true true }T
T{ gh' 5 type-at hx 0 run@ fc lf-mk-eq eqv? gh' lf-goal-type hx 0 run@ fb lf-mk-eq eqv? -> true true }T
\ With the equation: x, k, then h.
fa fb lf-mk-eq goal fa s" x" pair s" k" nm fh lf-run1 lf-goal-generalize-hyp nip constant gk
T{ gk view# gk 5 s" k" named? gk 6 s" h" named? -> 7 true true }T
\ A hypothesis without a stays (hc, place 4; h too, not asked); none
\ asked at all is generalize.
fa fb lf-mk-eq goal fa s" x" pair 0 fhc lf-run1 lf-goal-generalize-hyp nip constant gn
T{ gn view# gn 4 s" hc" named? gn 5 s" x" named? gn 3 s" h" named? -> 6 true true true }T
T{ fa fb lf-mk-eq goal fa s" x" pair 0 0 lf-goal-generalize-hyp nip view# -> 6 }T
T{ gh fa s" x" pair 0 fh lf-run1 ' lf-goal-generalize-hyp code4 -> thrown-invalid }T
\ Each new goal keeps the goal's tag (funext's one goal: appendParentTag).
: tagged ( type -- goal ) goal dup s" t" lfa-intern lf-mvar-tag! made ;
: tag-t? ( goal -- flag ) lf-goal-tag s" t" nm lf-name-same? ;
T{ fa fb lf-mk-eq tagged fa s" x" pair s" h" nm lf-goal-generalize-eq nip tag-t? -> true }T
T{ fa fb lf-mk-eq tagged fa s" x" pair 0 fh lf-run1 lf-goal-generalize-hyp nip tag-t? -> true }T
T{ s" Nat.succ" lf-mk-const0 dup lf-mk-eq tagged s" funext" lf-goal-apply-const 0 run@ tag-t?
   -> true }T
fresh

\ ---- 1. The words through text: accepted, and Lean's errors.
: hh ( -- c-addr u ) s" Nat explicit: a Nat explicit: b a b = explicit: h a b =" ;
: h2 ( -- c-addr u ) s" Nat explicit: a Nat explicit: b a b = explicit: h a b = explicit: h2 a b =" ;
: hs ( -- c-addr u ) s" ' Nat.succ ' Nat.succ =" ;
: h3 ( -- c-addr u ) s" Nat explicit: a Nat explicit: b Nat explicit: c a b + c = explicit: h a b + c =" ;
T{ hs s" by-funext by-rfl" tactic-ran hs s" by-funext[ x ] by-rfl" tactic-ran -> 0 0 }T
\ The name given is a hypothesis later steps name; _ is hidden.
T{ hs s" by-funext[ x ] x Nat.succ x Nat.succ = by-show by-rfl" tactic-ran -> 0 }T
T{ hs s" by-funext[ _ ] x Nat.succ x Nat.succ = by-show by-rfl" tactic-ran -> 1 }T
lf-tac-forget
\ The plain form: no pass on a goal that is no function equation; and it
\ stops (the next pass fails, undone): the goal f x = g x after it.
T{ hh s" by-funext ' h by-exact" tactic-ran -> 0 }T
T{ hs s" by-funext by-funext by-rfl" tactic-ran -> 0 }T
T{ hs s" by-funext ' Nat.succ ' Nat.succ = by-show by-rfl" tactic-ran -> 444 }T   \ goal changed
lf-tac-forget
T{ hs s" by-funext[ x ] by-funext[ y ]" tactic-ran s" by-funext[" token? -> 380 true }T
lf-tac-forget
T{ hs s" by-funext[ ] by-rfl" tactic-ran s" ]" token? -> 460 true }T
lf-tac-forget
T{ hs s" by-funext[ x by-rfl" tactic-ran s" by-funext[" token? -> 458 true }T   \ never closed
lf-tac-forget
T{ s" ' Nat.add ' Nat.add =" s" by-funext[ x y ] by-rfl" tactic-ran -> 93 }T
lf-tac-forget
\ by-infer-instance: the instance, or 125, 110, 119.
T{ s" Nat explicit: a Nat explicit: b a b = Decidable Subsingleton" s" by-infer-instance"
   tactic-ran -> 0 }T
T{ hh s" a b = Decidable by-have-by: d by-infer-instance by-end ' h by-exact" tactic-ran -> 0 }T
T{ hh s" Nat IntCast by-have-by: d by-infer-instance by-end ' h by-exact" tactic-ran
   s" by-infer-instance" token? -> 125 true }T
lf-tac-forget
T{ hh s" by-infer-instance" tactic-ran -> 110 }T
lf-tac-forget
T{ hh s" False Inhabited by-have-by: d by-infer-instance by-end ' h by-exact" tactic-ran -> 119 }T
lf-tac-forget
\ by-rename: the newest fitting hypothesis; none: 482; _: 99.
T{ hh s" a b = by-rename: k ' k by-exact" tactic-ran h2 s" a b = by-rename: k ' h by-exact" tactic-ran
   -> 0 0 }T
T{ h2 s" a b = by-rename: k ' h2 by-exact" tactic-ran -> 76 }T   \ h2 renamed: gone
lf-tac-forget
T{ hh s" b a = by-rename: k" tactic-ran s" by-rename:" token? -> 482 true }T
lf-tac-forget
T{ hh s" a b = by-rename: _ ' h by-exact" tactic-ran -> 99 }T
lf-tac-forget
T{ hh s" by-rename: k" tactic-ran -> 86 }T   \ no type
lf-tac-forget
\ by-generalize: and by-generalize-eq:, with at[ ].
T{ s" Nat explicit: a Nat explicit: b a b + a b + =" s" a b + by-generalize: x by-rfl" tactic-ran
   -> 0 }T
T{ h3 s" a b + by-generalize-eq: k x at[ h ] ' h by-exact" tactic-ran -> 0 }T
T{ h3 s" a b + by-generalize-eq: k x by-rw[ ' k <- ] ' h by-exact" tactic-ran -> 0 }T
T{ h3 s" a b + by-generalize: x at[ * ] ' h by-exact" tactic-ran -> 99 }T
lf-tac-forget
T{ h3 s" a b + by-generalize-eq: _ x ' h by-exact" tactic-ran -> 99 }T
lf-tac-forget
T{ h3 s" a b + by-generalize: x at[ k ] ' h by-exact" tactic-ran -> 455 }T
lf-tac-forget
T{ s" Nat explicit: a Nat explicit: b a b = Decidable.decide a b = Decidable.decide ="
   s" a b = by-generalize: x by-rfl" tactic-ran -> 99 }T
lf-tac-forget
\ by-skip, by-done: done with a goal is 89 at by-done; inside try taken back.
T{ hh s" by-skip ' h by-exact by-done by-skip" tactic-ran -> 0 }T
T{ hh s" by-done" tactic-ran s" by-done" token? -> 89 true }T
lf-tac-forget
T{ hh s" by-try by-done by-end ' h by-exact" tactic-ran -> 0 }T
\ trivial on the shared apply: And.intro and True.intro.
T{ s" True True ∧" s" by-trivial" tactic-ran -> 0 }T

\ ---- 6. State: rename's search leaves nothing behind (withoutModifyingState):
\ the metavariables it made (its hole's, which the search assigned b) are
\ unassigned after it (a rollback keeps them in the store, unassigned),
\ and the problems its elaboration put off (2's OfNat) are gone.
variable before  variable assigned-made  variable pending-before  variable pending-after
: count-before ( i -- ) drop lf-mvar-count before ! lf-elab-pending# pending-before ! ;
tac-shape-plain lf-tactic: by-probe-before constant tac-k-probe-before
' count-before tac-k-probe-before lf-tactic-action!
: assigned# ( -- n )
  0 lf-mvar-count before @ ?do i lf-mvar-at lf-goal-assigned? if 1+ then loop ;
: count-assigned ( i -- )
  drop assigned# assigned-made ! lf-elab-pending# pending-after ! ;
tac-shape-plain lf-tactic: by-probe-assigned constant tac-k-probe-assigned
' count-assigned tac-k-probe-assigned lf-tactic-action!
T{ s" Nat explicit: a Nat explicit: b b a = explicit: k a b = explicit: h b a ="
   s" by-probe-before _ a = by-rename: j by-probe-assigned ' j by-exact" tactic-ran
   assigned-made @ -> 0 0 }T
T{ s" Nat explicit: b b 2 = explicit: k b 2 ="
   s" by-probe-before _ 2 = by-rename: j by-probe-assigned ' j by-exact" tactic-ran
   assigned-made @ pending-after @ pending-before @ - -> 0 0 0 }T
\ The search runs one metavariable depth deeper (withNewMCtxDepth): a
\ hypothesis k : a = ?w, ?w the goal's own metavariable, does not fit
\ a = a, as ?w may not be assigned there: 482, as pinned Lean's
\ (Exists (Ne a) by constructor; intro k; rename a = a => j). The probe
\ puts k in a new main goal (by-intro: through Ne is not supported yet).
: with-k ( i goal -- goal' )
  nip dup lf-goal-type swap lf-goal-view 0 lf-view-fvar
  nat mv-natural lf-mvar-new made lf-mk-eq s" k" binder drop goal ;
: k-goal ( i -- ) dup ['] with-k lf-lift-meta-tactic1 ;
tac-shape-plain lf-tactic: by-probe-k constant tac-k-probe-k
' k-goal tac-k-probe-k lf-tactic-action!
T{ s" Nat explicit: a a a =" s" by-probe-k a a = by-rename: j" tactic-ran s" by-rename:" token?
   -> 482 true }T
lf-tac-forget

\ ---- 5. Resources: each library word directly, every heap allocation
\ refused in turn, in the same context; then each tactic through text.
: frames-anew ( -- )
  mgz-frames sweep-slab-anew mgq-frames sweep-slab-anew mgh-frames sweep-slab-anew
  mtk-frames sweep-slab-anew mrv-frames sweep-slab-anew mti-frames sweep-slab-anew
  ap-news sweep-slab-anew ap-goals sweep-slab-anew ap-todo sweep-slab-anew
  ap-later sweep-slab-anew lfa-brackets sweep-slab-anew ;
fresh
nat s" a" binder constant wa
nat s" b" binder constant wb
nat s" c" binder constant wcc
wa wcc lf-mk-eq s" h" binder constant wh
sweep-keep-view
: context-anew ( -- ) frames-anew sweep-view-anew ;
' context-anew sweep-slabs-xt !
: w-goal ( -- goal ) wa wb lf-mk-eq goal ;
: caught1 ( i*x xt in -- x outcome ) 1 lf-meta-catch ;
: direct ( x xt -- y outcome ) nip 0 caught1 ;
: s-const ( -- n ) ttrue ttrue and-of goal s" And.intro" lf-goal-apply-const run-count ;
: s-funext ( -- n ) s" Nat.succ" lf-mk-const0 dup lf-mk-eq goal s" funext" lf-goal-apply-const run-count ;
: s-eq ( -- n ) w-goal wa s" x" pair s" h" nm lf-goal-generalize-eq drop run-count ;
: s-hyp ( -- n ) w-goal wa s" x" pair 0 wh lf-run1 lf-goal-generalize-hyp nip view# ;
: s-hyp-eq ( -- n ) w-goal wa s" x" pair s" k" nm wh lf-run1 lf-goal-generalize-hyp nip view# ;
: d1 ( x -- n outcome ) ['] s-const direct ;
: d2 ( x -- n outcome ) ['] s-funext direct ;
: d3 ( x -- n outcome ) ['] s-eq direct ;
: d4 ( x -- n outcome ) ['] s-hyp direct ;
: d5 ( x -- n outcome ) ['] s-hyp-eq direct ;
T{ 0 ' d1 heap-sweep swept? 0 ' d2 heap-sweep swept? 0 ' d3 heap-sweep swept? -> true true true }T
T{ 0 ' d4 heap-sweep swept? 0 ' d5 heap-sweep swept? -> true true }T
' frames-anew sweep-slabs-xt !
: p-funext ( x -- code outcome ) drop hs s" by-funext by-rfl" text-full ;
: p-names ( x -- code outcome ) drop hs s" by-funext[ x ] by-rfl" text-full ;
: p-infer ( x -- code outcome )
  drop hh s" a b = Decidable by-have-by: d by-infer-instance by-end ' h by-exact" text-full ;
: p-rename ( x -- code outcome ) drop h2 s" a b = by-rename: k ' h by-exact" text-full ;
: p-gen ( x -- code outcome ) drop h3 s" a b + by-generalize-eq: k x at[ h ] ' h by-exact" text-full ;
: p-done ( x -- code outcome ) drop hh s" by-skip ' h by-exact by-done" text-full ;
T{ 0 ' p-funext heap-sweep swept? 0 ' p-names heap-sweep swept? 0 ' p-infer heap-sweep swept?
   -> true true true }T
T{ 0 ' p-rename heap-sweep swept? 0 ' p-gen heap-sweep swept? 0 ' p-done heap-sweep swept?
   -> true true true }T
lf-tac-forget
.( batch-small-1 test.fs: all tests passed) cr

\ Unit tests of tactic blocks, slice 2 (plan row TB2, piece F; design
\ docs/design/TACTIC_BLOCKS.md) over decide's slice of Init in an
\ authoring run, by the classes of docs/development/TEST_COVERAGE_REVIEW.md:
\ tactic-syntax.fs's then-step (<;>, tac-then, the lazy close), the
\ runner's per-goal modes and tfr-held (tactic-run.fs), goals.fs's
\ lf-goals-next-open and the words of tactics/blocks.fs, through their
\ text (tests/support/tactic-text.fs) and through probe tactics this file
\ registers (as blocks-1's: what the runner shows a step; a block with
\ recover false; a handler as slice 3's try will be; a macro's rules):
\ 1. outcomes: each form accepted; 468, 85 at each closer, 86, 72, 453,
\    90, 89, 96 final, 76, with their tokens and places;
\ 2. malformed input: <;> first in a block, twice, last, before a closer;
\ 3. records: every field of a then-step's and its t1's, a chain's, a
\    closed block as t1, at[ after t2; the shapes, modes and rows;
\ 4. interfaces: recover inside the per-goal modes, an error final under
\    recover and taken by a handler without it, a goal assigned when
\    reached skipped, lf-tac-again and lf-goals-next-open directly, the
\    goals set aside held during a chain and put back once after it, a
\    macro rule's logged error final under recover and passed over in a
\    block without it (review tb2-blocks1, re-check);
\ 5. resources: step fuel and the declaration's budget at every k below
\    a passing run, every heap allocation refused in turn;
\ 6. state: names given in t1, t2 and by-all-goals kept after them.
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
: must ( outcome -- ) ok? 0= abort" blocks-2 test: refused" ;
: token ( -- c-addr u ) lfa-error lfa-err-token lfa-error lfa-err-length @ ;
: token? ( c-addr u -- flag ) token compare 0= ;
: see@ ( -- pos ) lfa-error lfa-err-see @ ;
: step@ ( i -- addr ) lf-tactic-step ;
: at-of ( i -- pos ) step@ tac-at @ ;
\ Statements: a = b with h : a = b and k : b = a; a = b ∧ b = a; a = b ∧
\ a = b; (a = b ∧ a = b) ∧ (a = b ∧ a = b); (a = b ∧ a = b) ∧ b = a;
\ b = a with h; n + 0 = n; ∃ x, a = x.
: hh ( -- c-addr u ) s" Nat explicit: a Nat explicit: b a b = explicit: h b a = explicit: k a b =" ;
: hk ( -- c-addr u )
  s" Nat explicit: a Nat explicit: b a b = explicit: h b a = explicit: k a b = b a = ∧" ;
: hh2 ( -- c-addr u ) s" Nat explicit: a Nat explicit: b a b = explicit: h a b = a b = ∧" ;
: h4 ( -- c-addr u )
  s" Nat explicit: a Nat explicit: b a b = explicit: h a b = a b = ∧ a b = a b = ∧ ∧" ;
: hr ( -- c-addr u )
  s" Nat explicit: a Nat explicit: b a b = explicit: h b a = explicit: k a b = a b = ∧ b a = ∧" ;
: hq ( -- c-addr u ) s" Nat explicit: a Nat explicit: b a b = explicit: h b a = explicit: k a b = a b = ∧ b a = b a = ∧ ∧" ;
: hs ( -- c-addr u ) s" Nat explicit: a Nat explicit: b a b = explicit: h b a =" ;
: hn ( -- c-addr u ) s" Nat explicit: n n 0 + n =" ;
: hx ( -- c-addr u ) s" Nat explicit: a ' Eq a $ Exists" ;

\ ---- Probes: tactics registered here (rows are set while modules load).
\ by-probe: the recover flag, the top block's mode and depth, the goals
\ the proof's block holds aside, and how many times it ran.
variable seen-recover  variable seen-mode  variable seen-depth  variable seen-held
variable probes
: probe ( i -- ) drop lf-tac-recover? seen-recover ! lfr-top tfr-mode @ seen-mode !
  lfr-depth seen-depth ! 0 lfr-frame tfr-held @ seen-held ! 1 probes +! ;
tac-shape-plain lf-tactic: by-probe constant tac-k-probe
' probe tac-k-probe lf-tactic-action!
\ A block opened with recover false.
: probe-block ( i -- ) ['] lf-tac-focused lf-tac-no-recover ;
0 0 tac-block-cuts tac-shape-block lf-tactic: by-probe-block constant tac-k-probe-block
' probe-block tac-k-probe-block lf-tactic-action!
\ A handler, as slice 3's try: a save at its open, kept at its end, the
\ state put back and the block closed at a Lean error inside it.
: t-open ( frame -- ) lf-tac-save must swap tfr-save ! ;
: t-end ( frame -- ) dup tfr-save @ lf-tac-commit must lfr-focus-end ;
: t-fail ( frame -- ) drop lfr-pop ;
' t-open ' t-end ' t-fail lfr-no-recover lf-block-mode constant t-mode
: probe-try ( i -- ) 0 lf-tac-block ;
0 0 0 tac-shape-block lf-tactic: by-probe-try constant tac-k-probe-try
' probe-try tac-k-probe-try lf-tactic-action!
t-mode tac-k-probe-try lf-tactic-mode!
\ A macro's two rules (lf-tac-macro-alts): the newest raises an error of
\ Lean's logged class, the older one records that it ran.
variable ran2
: raise-logged ( -- ) lfa-e-tac-mismatch lf-tac-log-fail ;
: alt-ran ( -- ) true ran2 ! ;
: probe-mlog ( i -- ) drop ['] alt-ran ['] raise-logged 2 lf-tac-macro-alts ;
tac-shape-plain lf-tactic: by-probe-mlog constant tac-k-probe-mlog
' probe-mlog tac-k-probe-mlog lf-tactic-action!

\ ---- 3. Shapes, modes and rows.
: shape3 ( kind -- want names flags )
  lf-tactic-shape@ dup shape-want @ over shape-names @ rot shape-block @ ;
T{ tac-k-then shape3 tac-k-all-goals shape3 -> 0 0 tac-block tac-block-one or 0 0 tac-block }T
T{ tac-k-then lf-tactic-shape@ tac-shape-then = tac-shape-then shape-build @ -> true ' lft-build-then }T
T{ tac-shape-then dup shape-at @ swap shape-some @ -> 0 0 }T
: mode@ ( kind -- mode ) lfr-row trow-mode @ ;
T{ tac-k-then mode@ tac-k-all-goals mode@ -> lf-mode-then lf-mode-per-goal }T
: mode4 ( mode -- open end fail flags )
  dup mode-open @ over mode-end @ rot dup mode-fail @ swap mode-flags @ ;
T{ lf-mode-per-goal mode4 -> ' lfr-goals-open ' lfr-goals-end 0 lfr-admits }T
T{ lf-mode-then mode4 -> ' lfr-goals-open ' lfr-then-end 0 lfr-admits }T
: row-run@ ( kind -- xt ) lfr-row trow-run @ ;
T{ tac-k-then row-run@ tac-k-all-goals row-run@ -> ' lf-tac-all ' lf-tac-all }T
T{ tac-k-then lf-tac-word s" <;>" compare tac-k-then lf-tac-lean s" and_then" compare
   tac-k-all-goals lf-tac-word s" by-all-goals" compare tac-k-all-goals lf-tac-lean s" all_goals"
   compare -> 0 0 0 0 }T
T{ tac-k-then lfr-holder? tac-k-all-goals lfr-holder? -> true true }T
T{ s" <;>" lf-pf-reserved? -> true }T

\ ---- 3. A then-step's record: ' h by-exact <;> ' k by-exact (0 by, 1
\ t1 marked, 2 the then-block, its <;> its second place, its text from
\ past t1 to past t2, 3 t2 inside it).
T{ hh s" ' h by-exact <;> ' k by-exact" tactic-ran -> 0 }T
T{ lf-tactic-count 1 step@ tac-then @ 2 step@ tac-kind @ 3 step@ tac-parent @
   -> 4 true tac-k-then 2 }T
T{ 2 step@ dup tac-parent @ over tac-inner @ rot tac-then @ -> 0 1 false }T
T{ 2 step@ tac-arrow @ 2 at-of = 2 step@ tac-from @ 1 step@ tac-to @ =
   2 step@ tac-to @ 3 step@ tac-to @ = -> true true true }T
T{ 2 step@ dup tac-shape @ tac-shape-then = over tac-count @ rot tac-loc @ 3 step@ tac-then @
   -> true 0 0 false }T
T{ 0 step@ tac-inner @ 2 step@ tac-entries @ -> 2 0 }T
\ A chain, (a <;> b) <;> c: a and the first then-block marked, the
\ second not; each then-block right inside by.
T{ h4 s" by-constructor <;> by-constructor <;> ' h by-exact" tactic-ran -> 0 }T
T{ 1 step@ tac-then @ 2 step@ tac-then @ 4 step@ tac-then @ 3 step@ tac-then @
   -> true true false false }T
T{ 2 step@ tac-parent @ 3 step@ tac-parent @ 4 step@ tac-parent @ 5 step@ tac-parent @
   -> 0 2 0 4 }T
\ t1 a closed block: the induction (its alternatives inside it) is t1.
T{ hn s" n by-induction-with | zero => by-rfl | succ m ih => by-rfl by-end <;> by-rfl" tactic-ran
   -> 0 }T
T{ 1 step@ tac-then @ 1 step@ tac-kind @ 6 step@ tac-kind @ 6 step@ tac-parent @
   -> true tac-k-with tac-k-then 0 }T
\ at[ after t2 amends t2, inside the then-block, which stays open.
T{ hs s" ' h by-revert by-intro: x <;> by-symm at[ x ] ' x by-exact" tactic-ran -> 0 }T
T{ 4 step@ dup tac-parent @ swap tac-loc @ 0<> 5 step@ tac-parent @ 3 step@ tac-to @ 4 step@ tac-to @ =
   -> 3 true 0 true }T
\ by-all-goals' step: a block of its steps; names given inside it stay.
T{ hk s" by-constructor by-all-goals by-assumption by-end" tactic-ran 2 step@ dup tac-kind @
   swap tac-inner @ -> 0 tac-k-all-goals 1 }T
lf-tac-forget

\ ---- 1, 2. Reading errors: <;> with no step before it in its block
\ (468: first in the proof, in a brace, right after another <;>), with
\ none after it (85 at the closer, <;> the second place: end, }, by-end,
\ |), a value before it (86), right inside by-induction-with (72), at[
\ right after it (453).
T{ hh s" <;> ' h by-exact" tactic-ran s" <;>" token? -> 468 true }T
T{ hh s" { <;> ' h by-exact }" tactic-ran -> 468 }T
T{ hh s" ' h by-exact <;> <;> ' k by-exact" tactic-ran see@ -> 468 -1 }T
T{ hh s" ' h by-exact <;>" tactic-ran s" end" token? see@ 2 at-of = -> 85 true true }T
T{ hh s" { ' h by-exact <;> }" tactic-ran s" }" token? see@ 3 at-of = -> 85 true true }T
T{ hh s" by-focus ' h by-exact <;> by-end" tactic-ran s" by-end" token? -> 85 true }T
T{ hn s" n by-induction-with | zero => by-rfl <;> | succ m ih => by-rfl by-end" tactic-ran
   s" |" token? -> 85 true }T
T{ hh s" ' h <;> ' k by-exact" tactic-ran -> 86 }T
T{ hn s" n by-induction-with <;> by-rfl | zero => by-rfl | succ m ih => by-rfl by-end" tactic-ran
   -> 72 }T
T{ hh s" ' h by-exact <;> at[ h ]" tactic-ran -> 453 }T
\ The then-block closes before }, by-end, | and end, and before a tactic
\ word: a <;> b inside a brace, a by-focus and an alternative.
T{ hk s" { by-constructor <;> by-assumption }" tactic-ran -> 0 }T
T{ hk s" by-focus by-constructor <;> by-assumption by-end" tactic-ran -> 0 }T
T{ hn s" n by-induction-with | zero => by-rfl <;> by-rfl | succ m ih => by-rfl by-end" tactic-ran
   -> 0 }T
lf-tac-forget

\ ---- 4. Runs. t1 with no goal: 90 at t1 (Lean's focus, before t1).
T{ hh s" ' h by-exact by-rfl <;> by-rfl" tactic-ran s" by-rfl" token? see@ -> 90 true -1 }T
\ t1 leaving no goal: no pass, t2 (here wrong) never runs; likewise
\ by-all-goals over no goal.
T{ hh s" ' h by-exact <;> ' k by-exact" tactic-ran -> 0 }T
T{ hh s" ' h by-exact by-all-goals ' k by-exact by-end" tactic-ran -> 0 }T
\ A goal left by the chain: 89 at by. The goals set aside come back once,
\ after the whole chain: the second then-block runs on no goal here.
T{ hk s" by-constructor <;> a b = ' h by-have: x" tactic-ran s" by" token? -> 89 true }T
T{ hr s" by-constructor by-constructor <;> ' h by-exact <;> ' h by-exact ' k by-exact" tactic-ran
   -> 0 }T
\ Each pass's goals kept, in order: those of the first goal first.
T{ hq s" by-constructor <;> by-constructor ' h by-exact ' h by-exact ' k by-exact ' k by-exact"
   tactic-ran -> 0 }T
T{ hq s" by-constructor by-all-goals by-constructor by-end ' h by-exact ' h by-exact by-assumption"
   tactic-ran -> 89 }T
\ An error of a pass: final where the block recovers (Lean logs it), the
\ second goal's at its step; with recover false (inside the handler) not
\ final, and the handler takes it back.
T{ hk s" by-constructor <;> ' h by-exact" tactic-ran lf-author-final? -> 96 true }T
T{ hk s" by-constructor by-all-goals ' h by-exact by-end" tactic-ran lf-author-final? -> 96 true }T
T{ hh s" by-probe-try by-all-goals ' k by-exact by-end by-end ' h by-exact" tactic-ran -> 0 }T
T{ hk s" by-probe-try by-constructor <;> ' h by-exact by-end by-constructor <;> by-assumption"
   tactic-ran -> 0 }T
lf-tac-forget
\ The recover flag inside the per-goal blocks: the block's, true in a
\ run; the then-block is the top block of t2, inside by.
T{ hk s" by-constructor by-all-goals by-probe by-assumption by-end" tactic-ran seen-recover @
   seen-mode @ seen-depth @ -> 0 true lf-mode-per-goal 2 }T
T{ hk s" by-constructor <;> by-probe by-assumption by-assumption" tactic-ran seen-mode @
   seen-depth @ -> 0 lf-mode-then 2 }T
\ The goals aside are held in the proof's frame during the chain, none
\ after it.
T{ hk s" by-constructor <;> by-probe by-assumption by-assumption" tactic-ran seen-held @ 0<
   -> 0 false }T
T{ hk s" by-constructor <;> by-assumption by-probe" tactic-ran seen-held @ -> 0 -1 }T
\ A goal assigned when it is reached is skipped: rfl on a = ?w assigns
\ the witness, the second goal; one pass only.
T{ 0 probes ! hx s" by-constructor by-all-goals by-probe by-rfl by-end" tactic-ran probes @
   -> 0 1 }T
T{ 0 probes ! hk s" by-constructor by-all-goals by-probe by-assumption by-end" tactic-ran
   probes @ -> 0 2 }T
\ lf-goals-next-open: an empty list has none; lf-tac-again: the steps
\ from the first again, no goals held.
T{ 0 0 lf-goals-next-open -> false }T
create fake-frame /tfr allot
T{ 5 fake-frame tfr-step ! 9 fake-frame tfr-next ! 7 fake-frame tfr-held !
   fake-frame lf-tac-again fake-frame tfr-next @ fake-frame tfr-held @ -> 6 -1 }T
\ The walk's place (review tb2-blocks2 finding 1): the open takes it
\ from 0, a pass on goal x at place k keeps k and has the goals [x]; the
\ next pass looks from k.
T{ 7 fake-frame tfr-at ! fake-frame lfr-goals-take fake-frame tfr-at @ -> fake-frame 0 }T
T{ fake-frame 3 77 lfr-pass-on fake-frame tfr-at @ fake-frame tfr-next @ lf-goals run-count
   lf-goals 0 run@ -> 3 6 1 77 }T
T{ 41 fake-frame tfr-todo ! 1 fake-frame tfr-at ! fake-frame lfr-todo@ -> 41 1 }T
\ A macro's rule raising a logged error under recover: final, the macro
\ ends there (the older rule never runs); inside a block that does not
\ recover it is an ordinary failure and the older rule runs (Lean's
\ expandEval keeps recover; review tb2-blocks1, its re-check's finding).
T{ false ran2 ! hh s" by-probe-mlog ' h by-exact" tactic-ran lf-author-final? ran2 @
   -> 96 true false }T
T{ false ran2 ! hh s" by-probe-block by-probe-mlog ' h by-exact by-end" tactic-ran ran2 @
   -> 0 true }T
lf-tac-forget

\ ---- 6. Names: given by t1 and t2 and inside by-all-goals, they stay
\ after the chain or block; one used on a goal that lacks it is refused
\ (76; Lean's unknown identifier, TACTIC_STATUS row NR).
T{ hh2 s" by-constructor <;> a b = ' h by-have: x ' x by-exact ' x by-exact" tactic-ran -> 0 }T
T{ hh2 s" by-constructor by-all-goals a b = ' h by-have: x by-end ' x by-exact ' x by-exact"
   tactic-ran -> 0 }T
T{ hk s" by-constructor a b = ' h by-have: x <;> ' x by-exact ' x by-exact" tactic-ran -> 76 }T
lf-tac-forget
\ A pass that leaves its goal open: each goal reached once, both kept.
T{ 0 probes ! hk s" by-constructor by-all-goals by-probe by-end by-assumption by-assumption"
   tactic-ran probes @ -> 0 2 }T
lf-tac-forget

\ ---- 3, 1. The fixed blocks on block shapes (plan row 9.4.8s): by's row,
\ by-induction-with's (bars, its term), the headers' (headed, names cut)
\ and their steps; each a holder; a header's goals told at its =>.
: hdr ( -- flags ) tac-block tac-block-headed or tac-block-cuts or ;
T{ tac-k-by lfr-holder? tac-k-with lfr-holder? tac-k-alt lfr-holder? tac-k-case lfr-holder?
   tac-k-rfl lfr-holder? -> true true true true false }T
T{ tac-k-by shape3 tac-k-with shape3 -> 0 0 tac-block 1 0 tac-block tac-block-bars or }T
T{ tac-k-alt shape3 tac-k-case shape3 -> 0 0 hdr 0 0 hdr }T
T{ hn s" n by-induction-with | zero => by-rfl | succ m ih => by-rfl by-end" tactic-ran
   0 step@ tac-shape @ 1 step@ tac-shape @ 2 step@ tac-shape @ 4 step@ tac-shape @
   -> 0 0 tac-shape-with tac-shape-headed tac-shape-headed }T
T{ hk s" by-constructor by-case: right => ' k by-exact by-end by-next => ' h by-exact by-end"
   tactic-ran 2 step@ tac-shape @ 4 step@ tac-shape @ -> 0 tac-shape-headed tac-shape-headed }T
T{ hk s" by-constructor by-case: left => a b = ' h by-have: x by-end ' k by-exact" tactic-ran
   s" =>" token? -> 89 true }T
lf-tac-forget

\ ---- 5. Fuel: the run's steps and the declaration's budget at each k
\ below a passing run: 91 or 138 (exhausted) or the answer, never another.
: exhausted-or-0? ( code -- flag ) dup 0= if drop true else lf-author-outcome outcome-exhausted = then ;
: chain-text ( -- code ) h4 s" by-constructor <;> by-constructor <;> ' h by-exact" tactic-ran ;
: fuel-ran ( k -- code ) lf-tactic-fuel! chain-text lf-tactic-fuel-default ;
: fuel-swept? ( -- flag ) true 12 0 do i fuel-ran exhausted-or-0? and loop 12 fuel-ran 0= and ;
T{ fuel-swept? -> true }T
: all-text ( -- code ) hk s" by-constructor by-all-goals by-assumption by-end" tactic-ran ;
: budget-ran ( k -- code ) lf-elab-fuel! all-text lf-meta-default-budget lf-elab-fuel! ;
: budget-swept? ( -- flag )
  true 1 begin dup 4096 < while dup budget-ran exhausted-or-0? rot and swap 2* repeat drop
  all-text 0= and ;
T{ budget-swept? -> true }T
lf-tac-forget

\ ---- 5. Every heap allocation refused in turn (the frames' and saves'
\ slabs given back first), and every run record claim refused in turn
\ (room for j records: a pass's run claims, lfr-only, lfr-acc+ and the
\ hold among them; review tb2-blocks2 finding 1; each text empties the
\ runs at its start, reader.fs): the answer or full.
: blocks-anew ( -- ) trun-frames sweep-slab-anew trun-saves sweep-slab-anew ;
lf-lib-private order+
' rn-recs sweep-slab-xt !
order-
' blocks-anew sweep-slabs-xt !
: p-then ( x -- code outcome ) drop hk s" by-constructor <;> by-assumption" text-full ;
: p-all ( x -- code outcome )
  drop hk s" by-constructor by-all-goals by-assumption by-end" text-full ;
: p-chain ( x -- code outcome )
  drop h4 s" by-constructor <;> by-constructor <;> ' h by-exact" text-full ;
T{ 0 ' p-then heap-sweep swept? 0 ' p-all heap-sweep swept? 0 ' p-chain heap-sweep swept?
   -> true true true }T
T{ 0 ' p-then slab-sweep swept? 0 ' p-all slab-sweep swept? 0 ' p-chain slab-sweep swept?
   -> true true true }T
lf-tac-forget
.( blocks-2 test.fs: all tests passed) cr

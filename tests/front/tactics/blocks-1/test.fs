\ Unit tests of tactic blocks, slice 1 (plan row TB2, piece F; design
\ docs/design/TACTIC_BLOCKS.md) over decide's slice of Init in an
\ authoring run, by the classes of docs/development/TEST_COVERAGE_REVIEW.md:
\ tactic-syntax.fs's block shapes and closers ({ }, by-end), the runner's
\ block modes, recover flags, logged class and loop (tactic-run.fs), and
\ the words of tactics/blocks.fs and have.fs's by-have-by:, through their
\ text (tests/support/tactic-text.fs) and through probe tactics this file
\ registers (each tells what the runner shows a step: the recover flag,
\ the top block's mode, the depth; a handler mode as slice 3's try will
\ be; a block run by a loop of its own, as FE2's nested by will be):
\ 1. outcomes: each word accepted; 82, 83 (each closer at the wrong
\    block), 84, 78, 85, 89, 90, 72, 99 with their tokens and places;
\ 2. malformed input: a closer with no block, a brace left open at by-end
\    and at end, | in a brace, a name in a brace used after it;
\ 3. records: every field of a brace's and a have-by's step, the shapes'
\    fields, the modes' fields and rows;
\ 4. interfaces: the recover flag in each mode, no-recover, first's
\    alternatives, the logged class, a handler taking an error back with
\    the state put back, a final error it may not take, a gap it may not
\    take, a loop from a base above 0;
\ 5. resources: step fuel and the declaration's budget at every k below
\    a passing run (91 or the answer, never another), and every heap
\    allocation refused in turn (full or the answer: tests/support/
\    meta-sweeps.fs), try's alternatives among them (by-trivial);
\ 6. state: no frame pushed by a { that finds no goal, names cut or kept.
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
: must ( outcome -- ) ok? 0= abort" blocks-1 test: refused" ;
: token ( -- c-addr u ) lfa-error lfa-err-token lfa-error lfa-err-length @ ;
: token? ( c-addr u -- flag ) token compare 0= ;
: at@ ( -- pos ) lfa-error lfa-err-at @ ;
: see@ ( -- pos ) lfa-error lfa-err-see @ ;
: step@ ( i -- addr ) lf-tactic-step ;
: at-of ( i -- pos ) step@ tac-at @ ;
\ Statements: a = b with h : a = b and k : b = a; a = b ∧ b = a; a = b ∧
\ a = b; b = a with h; n + 0 = n.
: hh ( -- c-addr u ) s" Nat explicit: a Nat explicit: b a b = explicit: h b a = explicit: k a b =" ;
: hk ( -- c-addr u )
  s" Nat explicit: a Nat explicit: b a b = explicit: h b a = explicit: k a b = b a = ∧" ;
: hh2 ( -- c-addr u )
  s" Nat explicit: a Nat explicit: b a b = explicit: h b a = explicit: k a b = a b = ∧" ;
: hs ( -- c-addr u ) s" Nat explicit: a Nat explicit: b a b = explicit: h b a =" ;
: hn ( -- c-addr u ) s" Nat explicit: n n 0 + n =" ;
: ha ( -- c-addr u ) s" Nat explicit: a a a =" ;

\ ---- Probes: tactics registered here (rows are set while modules load).
variable seen-recover  variable seen-mode  variable seen-depth
: probe ( i -- ) drop lf-tac-recover? seen-recover ! lfr-top tfr-mode @ seen-mode !
  lfr-depth seen-depth ! ;
tac-shape-plain lf-tactic: by-probe constant tac-k-probe
' probe tac-k-probe lf-tactic-action!
variable inner-recover
: probe-inner ( -- ) lf-tac-recover? inner-recover ! ;
: probe-nr ( i -- ) drop ['] probe-inner lf-tac-no-recover lf-tac-recover? seen-recover ! ;
tac-shape-plain lf-tactic: by-probe-nr constant tac-k-probe-nr
' probe-nr tac-k-probe-nr lf-tactic-action!
variable alt1  variable alt2
: alt-fails ( -- ) lf-tac-recover? alt1 ! lfa-e-tac-mismatch lf-tac-stop ;
: alt-ends ( -- ) lf-tac-recover? alt2 ! ;
: probe-first ( i -- ) drop ['] alt-ends ['] alt-fails 2 lf-tac-first-of ;
tac-shape-plain lf-tactic: by-probe-first constant tac-k-probe-first
' probe-first tac-k-probe-first lf-tactic-action!
variable was-final
: raise-logged ( -- ) lfa-e-tac-mismatch lf-tac-log-fail ;
: probe-log ( i -- ) drop ['] raise-logged catch lf-author-final? was-final ! throw ;
tac-shape-plain lf-tactic: by-probe-log constant tac-k-probe-log
' probe-log tac-k-probe-log lf-tactic-action!
: probe-gap ( i -- ) drop lfa-e-tac-meta lf-tac-stop ;
tac-shape-plain lf-tactic: by-probe-gap constant tac-k-probe-gap
' probe-gap tac-k-probe-gap lf-tactic-action!
\ A block opened with recover false (its frame takes the flag of the block
\ below it while that is false).
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
\ A block run inside its step by a loop of its own, from the depth below it.
variable nested-done   \ true once the loop ran to its base and returned
: probe-nested ( i -- ) lfr-depth swap lf-tac-focused lfr-loop-from true nested-done ! ;
0 0 tac-block-cuts tac-shape-block lf-tactic: by-probe-nested constant tac-k-probe-nested
' probe-nested tac-k-probe-nested lf-tactic-action!

\ ---- 3. Shapes, modes and rows.
: shape3 ( kind -- want names flags )
  lf-tactic-shape@ dup shape-want @ over shape-names @ rot shape-block @ ;
T{ tac-k-brace shape3 -> 0 0 tac-block tac-block-cuts or tac-block-self or }T
T{ tac-k-focus shape3 tac-k-have-by shape3 -> 0 0 tac-block 1 1 tac-block tac-block-cuts or }T
T{ tac-k-brace lf-tactic-shape@ dup shape-build @ over shape-at @ rot shape-some @
   -> ' lft-build-block 0 0 }T
T{ tac-k-brace lf-tactic-shape@ lft-block-shape? tac-shape-plain lft-block-shape? 0 lft-block-shape?
   -> true false false }T
T{ tac-k-brace lf-tactic-shape@ lft-self-closing? tac-k-focus lf-tactic-shape@ lft-self-closing?
   -> true false }T
: mode@ ( kind -- mode ) lfr-row trow-mode @ ;
T{ tac-k-brace mode@ tac-k-focus mode@ tac-k-have-by mode@ tac-k-by mode@ tac-k-case mode@
   -> lf-mode-done lf-mode-focus lf-mode-nested lf-mode-nested 0 }T
: mode4 ( mode -- open end fail flags )
  dup mode-open @ over mode-end @ rot dup mode-fail @ swap mode-flags @ ;
T{ lf-mode-done mode4 -> ' drop ' lfr-done-end 0 lfr-admits }T
T{ lf-mode-nested mode4 -> ' drop ' lfr-nested-end 0 lfr-admits lfr-fresh-recover or }T
T{ lf-mode-focus mode4 t-mode mode4 -> ' drop ' lfr-focus-end 0 0
   ' t-open ' t-end ' t-fail lfr-no-recover }T
T{ tac-k-brace lf-tac-word s" {" compare tac-k-brace lf-tac-lean s" braces" compare
   tac-k-focus lf-tac-lean s" focus" compare tac-k-have-by lf-tac-lean s" have" compare
   -> 0 0 0 0 }T
T{ tac-k-brace lfr-holder? tac-k-have-by lfr-holder? tac-k-rfl lfr-holder? tac-k-case lfr-holder?
   -> true true false true }T

\ ---- 3. A brace's step: { ' h by-exact } (the brace at offset 0 of its
\ text, } at 15, its text to 16, its tactic from past {), and a have-by's.
T{ hh s" { ' h by-exact }" tactic-ran -> 0 }T
T{ lf-tactic-count 1 step@ dup tac-kind @ over tac-parent @ rot tac-inner @ -> 3 tac-k-brace 0 1 }T
T{ 1 step@ dup tac-arrow @ swap tac-to @ 1 at-of tuck - >r - r> -> 15 16 }T
T{ 1 step@ tac-from @ 0 at-of - 2 step@ tac-from @ 1 at-of - -> 2 1 }T
T{ 1 step@ dup tac-name @ over tac-count @ rot tac-word @ -> 0 0 0 }T
T{ 1 step@ dup tac-shape @ tac-k-brace lf-tactic-shape@ = swap tac-loc @ -> true 0 }T
T{ 1 step@ tac-entries @ 0> 2 step@ tac-parent @ -> true 1 }T
\ T by-have-by: j: its value T and its name j, its block's step inside it,
\ no closer's place (by-end ends it; its unsolved goals are told at it).
T{ hs s" b a = by-have-by: j ' Eq.symm ' h $ by-exact by-end ' j by-exact" tactic-ran -> 0 }T
T{ 1 step@ dup tac-kind @ over tac-count @ rot tac-arrow @ -> tac-k-have-by 2 -1 }T
T{ 1 0 lf-tac-arg syn-kind@ 1 1 lf-tac-arg s" j" lfa-intern = -> syn-k-binrel true }T
T{ 1 step@ tac-inner @ 2 step@ tac-parent @ 3 step@ tac-parent @ -> 1 1 0 }T
T{ 1 step@ tac-to @ 3 step@ tac-from @ = 3 at-of 1 step@ tac-to @ - -> true 5 }T
lf-tac-forget

\ ---- 1, 2. Outcomes and malformed input through the text.
\ A goal left at }: 89 at }; { } likewise (Lean's parser reads it); no
\ goal: 90 at {, and no frame was pushed for it.
T{ hh s" { b a = ' k by-have: x }" tactic-ran s" }" token? -> 89 true }T
T{ hh s" { }" tactic-ran s" }" token? -> 89 true }T
T{ hh s" ' h by-exact { ' h by-exact }" tactic-ran s" {" token? lfr-depth -> 90 true 1 }T
\ Closers: } with no brace (83), } at an alternative (83, its | second),
\ } at by-focus, by-end at a brace (83, its { second), by-end with only by
\ open, { open at end (82, its { second), | inside a brace (83).
T{ hh s" ' h by-exact }" tactic-ran s" }" token? -> 83 true }T
T{ hn s" n by-induction-with | zero => by-rfl } | succ m ih => by-rfl by-end" tactic-ran
   see@ 2 at-of = -> 83 true }T
T{ hh s" by-focus ' h by-exact }" tactic-ran -> 83 }T
T{ hh s" { ' h by-exact by-end" tactic-ran s" by-end" token? see@ 1 at-of = -> 83 true true }T
T{ hh s" ' h by-exact by-end" tactic-ran -> 83 }T
T{ hh s" { ' h by-exact" tactic-ran see@ 1 at-of = -> 82 true }T
T{ hn s" n by-induction-with | zero => { by-rfl | succ m ih => by-rfl by-end" tactic-ran
   s" |" token? -> 83 true }T
\ { right inside by-induction-with is Lean's pre-tactic, not supported yet
\ (72); { and } are no names (84) and name no binder (78).
T{ hn s" n by-induction-with { by-rfl } | zero => by-rfl | succ m ih => by-rfl by-end"
   tactic-ran -> 72 }T
T{ hh s" by-intro: { by-sorry" tactic-ran s" Nat explicit: } } } =" s" by-sorry" tactic-ran
   -> 84 78 }T
\ Empty by- blocks: 85 at by-end (Lean's parser wants a tactic).
T{ hh s" by-focus by-end" tactic-ran s" a b = by-have-by: j by-end ' j by-exact" hh 2swap
   tactic-ran -> 85 85 }T
\ have-by: its unsolved goals 89 at by-have-by:; no goal 90; _ as its
\ name not supported yet (99).
T{ hs s" b a = by-have-by: j a b = ' h by-have: x by-end ' j by-exact" tactic-ran
   s" by-have-by:" token? -> 89 true }T
T{ hh s" ' h by-exact a b = by-have-by: j ' h by-exact by-end" tactic-ran -> 90 }T
T{ hs s" b a = by-have-by: _ ' Eq.symm ' h $ by-exact by-end by-assumption" tactic-ran -> 99 }T
\ by-focus: 90 with no goal; the goals it leaves come back first.
T{ hh s" ' h by-exact by-focus ' h by-exact by-end" tactic-ran -> 90 }T
T{ hk s" by-constructor by-focus a b = ' h by-have: x by-end ' x by-exact ' k by-exact"
   tactic-ran -> 0 }T
\ ---- 6. Names: { cuts those given inside it, have-by its block's but its
\ own, by-focus none.
T{ hh2 s" by-constructor { a b = ' h by-have: x ' x by-exact } ' x by-exact" tactic-ran
   s" x" token? -> 1 true }T
T{ hs s" b a = by-have-by: j a b = ' h by-have: x ' Eq.symm ' x $ by-exact by-end ' x by-exact"
   tactic-ran s" x" token? -> 1 true }T
T{ hs s" b a = by-have-by: j a b = ' h by-have: x ' Eq.symm ' x $ by-exact by-end ' j by-exact"
   tactic-ran -> 0 }T
lf-tac-forget

\ ---- 4. The recover flag: true in every mode of a run (the proof's by is
\ a fresh Tactic.run), false outside one; the top block's mode and depth.
T{ lf-tac-recover? -> false }T
T{ hh s" by-probe ' h by-exact" tactic-ran seen-recover @ seen-mode @ seen-depth @
   -> 0 true lf-mode-nested 1 }T
T{ hh s" { by-probe ' h by-exact }" tactic-ran seen-recover @ seen-mode @ seen-depth @
   -> 0 true lf-mode-done 2 }T
T{ hh s" by-focus by-probe by-end ' h by-exact" tactic-ran seen-mode @ -> 0 lf-mode-focus }T
T{ hh s" a b = by-have-by: j by-probe ' h by-exact by-end ' j by-exact" tactic-ran
   seen-mode @ seen-depth @ -> 0 lf-mode-nested 2 }T
\ no-recover: false around xt, put back after; outside a run xt alone.
T{ hh s" by-probe-nr ' h by-exact" tactic-ran inner-recover @ seen-recover @ -> 0 false true }T
T{ true inner-recover ! ' probe-inner lf-tac-no-recover inner-recover @ -> false }T
\ first: the alternative tried from a save runs with recover false, the
\ last bare, with the block's (Lean's orElse, BuiltinTactic.lean:631-641).
T{ hh s" by-probe-first ' h by-exact" tactic-ran alt1 @ alt2 @ -> 0 false true }T
\ A block opened while recover is false takes false; a brace inside it
\ too; a have-by inside it is a fresh Tactic.run: true.
T{ hh s" by-probe-block by-probe ' h by-exact by-end" tactic-ran seen-recover @ -> 0 false }T
T{ hh s" by-probe-block { by-probe ' h by-exact } by-end" tactic-ran seen-recover @ -> 0 false }T
T{ hh s" by-probe-block a b = by-have-by: j by-probe ' h by-exact by-end ' j by-exact by-end"
   tactic-ran seen-recover @ -> 0 true }T
\ The logged class (lf-tac-log-fail): final when the block recovers, an
\ ordinary error when not.
T{ hh s" by-probe-log" tactic-ran was-final @ -> 96 true }T
T{ hh s" by-probe-block by-probe-log by-end" tactic-ran was-final @ -> 96 false }T
T{ lf-author-final? lf-tac-forget lf-author-final? -> true false }T
\ lfa-final with no error recorded marks nothing.
T{ lfa-final lf-author-final? -> false }T

\ ---- 4. A handler (the probe try): a Lean error inside it taken back, the
\ state put back to its save (two goals again, both then closed by h),
\ the run going on; a gap (93) and a final error (have-by's unsolved
\ goals, the design review's finding 1) never; a brace's error inside it
\ (recover false there: Lean's closeUsingOrAdmit throws it on) taken; its
\ end keeps the state.
T{ hh s" by-probe-try ' k by-exact by-end ' h by-exact" tactic-ran -> 0 }T
T{ hh2 s" by-constructor by-probe-try ' h by-exact ' k by-exact by-end ' h by-exact ' h by-exact"
   tactic-ran -> 0 }T
T{ hh s" by-probe-try by-probe-gap by-end ' h by-exact" tactic-ran -> 93 }T
T{ hs s" by-probe-try b a = by-have-by: j a b = ' h by-have: x by-end by-end ' h by-exact"
   tactic-ran -> 89 }T
T{ hh s" by-probe-try { ' k by-exact } by-end ' h by-exact" tactic-ran -> 0 }T
T{ hh s" by-probe-try ' h by-exact by-end" tactic-ran lfr-saves -> 0 0 }T
\ A brace inside a have-by inside the handler: the have-by recovers, so
\ the brace's error is final there (Lean's closeUsingOrAdmit logs it).
T{ hs s" by-probe-try b a = by-have-by: j { ' h by-exact } by-end by-end ' j by-exact"
   tactic-ran -> 96 }T
\ A block run by a loop of its own from the depth below it: its steps run
\ inside the step; an error in it goes no lower than its base there, and
\ the loop of the step around it takes it on (here the probe try).
T{ hh s" by-probe-nested ' h by-exact by-end" tactic-ran -> 0 }T
T{ false nested-done ! hh s" by-probe-try by-probe-nested ' k by-exact by-end by-end ' h by-exact"
   tactic-ran nested-done @ -> 0 false }T
T{ hh s" by-probe-nested ' k by-exact by-end" tactic-ran -> 96 }T
lf-tac-forget

\ ---- 5. Fuel: the run's steps and the declaration's budget at each k
\ below a passing run: 91 or 138 (exhausted) or the answer, never another.
: exhausted-or-0? ( code -- flag ) dup 0= if drop true else lf-author-outcome outcome-exhausted = then ;
: brace-text ( -- code ) hk s" by-constructor { ' h by-exact } { ' k by-exact }" tactic-ran ;
: fuel-ran ( k -- code ) lf-tactic-fuel! brace-text lf-tactic-fuel-default ;
: fuel-swept? ( -- flag ) true 6 0 do i fuel-ran exhausted-or-0? and loop 6 fuel-ran 0= and ;
T{ fuel-swept? -> true }T
: trivial-text ( -- code ) ha s" { by-trivial }" tactic-ran ;
: budget-ran ( k -- code ) lf-elab-fuel! trivial-text lf-meta-default-budget lf-elab-fuel! ;
: budget-swept? ( -- flag )
  true 1 begin dup 4096 < while dup budget-ran exhausted-or-0? rot and swap 2* repeat drop
  trivial-text 0= and ;
T{ budget-swept? -> true }T
lf-tac-forget

\ ---- 5. Every heap allocation refused in turn (the frames' and saves'
\ slabs given back first): the answer or full.
: blocks-anew ( -- ) trun-frames sweep-slab-anew trun-saves sweep-slab-anew ;
' blocks-anew sweep-slabs-xt !
: full-code? ( code -- flag ) dup if lf-author-outcome outcome-full = then ;
: text-full ( c-addr u c-addr' u' -- code outcome )
  tactic-ran dup full-code? if drop -1 outcome-full else outcome-ok then ;
: p-brace ( x -- code outcome ) drop hk s" by-constructor { ' h by-exact } { ' k by-exact }" text-full ;
: p-have-by ( x -- code outcome )
  drop hs s" b a = by-have-by: j ' Eq.symm ' h $ by-exact by-end ' j by-exact" text-full ;
: p-focus ( x -- code outcome ) drop hk s" by-constructor by-focus ' h by-exact by-end ' k by-exact"
  text-full ;
: p-trivial ( x -- code outcome ) drop ha s" { by-trivial }" text-full ;
T{ 0 ' p-brace heap-sweep swept? 0 ' p-have-by heap-sweep swept? -> true true }T
T{ 0 ' p-focus heap-sweep swept? 0 ' p-trivial heap-sweep swept? -> true true }T
lf-tac-forget
.( blocks-1 test.fs: all tests passed) cr

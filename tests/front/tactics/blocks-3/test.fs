\ Unit tests of tactic blocks, slice 3 (plan row TB2, piece F; design
\ docs/design/TACTIC_BLOCKS.md 4) over decide's slice of Init in an
\ authoring run, by the classes of docs/development/TEST_COVERAGE_REVIEW.md:
\ the runner's handlers (tactic-run.fs: lfr-arm, lfr-keep, lfr-put-back,
\ the modes of try, first and its alternatives, repeat and any_goals,
\ tfr-sorry, lfr-mark's 490), the reader's bare alternatives (tactic-
\ syntax.fs: tac-block-bare) and the words of tactics/blocks.fs, through
\ their text (tests/support/tactic-text.fs) and probe tactics:
\ 1. outcomes: each word accepted; 85, 89, 96, 469, 490 with their places;
\    every refusal (93, 88, 91, a Forth exception) through every handler;
\ 2. malformed input: a tactic before by-first's first |, an empty
\    alternative, an empty by-first, | outside by-first;
\ 3. records: the shapes, modes and rows; a bare alternative's step;
\ 4. interfaces: recover and errToSorry in each block, the save taken
\    before a handler's step and none before first's last alternative, a
\    rolled-back alternative or pass leaving nothing (goals, assignments,
\    names), tfr-held cleared by a handler, the walk of frames;
\ 5. resources: step fuel at every k below a passing run, a repeat that
\    never fails stopped by fuel (91), every heap allocation and every
\    frame and save claim refused in turn;
\ 6. state: names given in by-try and by-first kept after them.
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
: token ( -- c-addr u ) lfa-error lfa-err-token lfa-error lfa-err-length @ ;
: token? ( c-addr u -- flag ) token compare 0= ;
: step@ ( i -- addr ) lf-tactic-step ;
\ Statements: a = b with h : a = b, k : b = a; a = b ∧ b = a; b = a ∧ b = a
\ with h; b = a with h; (a = b ∧ a = b) ∧ b = a; (a = b ∧ a = b) ∧ (a = b
\ ∧ b = a); a = b ∧ b = a ∧ a = b; a = b ∧ a = b.
: hh ( -- c-addr u ) s" Nat explicit: a Nat explicit: b a b = explicit: h b a = explicit: k a b =" ;
: hk ( -- c-addr u )
  s" Nat explicit: a Nat explicit: b a b = explicit: h b a = explicit: k a b = b a = ∧" ;
: hb ( -- c-addr u ) s" Nat explicit: a Nat explicit: b a b = explicit: h b a = b a = ∧" ;
: hs ( -- c-addr u ) s" Nat explicit: a Nat explicit: b a b = explicit: h b a =" ;
: hr ( -- c-addr u )
  s" Nat explicit: a Nat explicit: b a b = explicit: h b a = explicit: k a b = a b = ∧ b a = ∧" ;
: hq ( -- c-addr u ) s" Nat explicit: a Nat explicit: b a b = explicit: h b a = explicit: k a b = a b = ∧ a b = b a = ∧ ∧" ;
: h3 ( -- c-addr u )
  s" Nat explicit: a Nat explicit: b a b = explicit: h b a = explicit: k a b = b a = a b = ∧ ∧" ;
: h2 ( -- c-addr u ) s" Nat explicit: a Nat explicit: b a b = explicit: h b a = explicit: k a b = a b = ∧" ;

\ ---- Probes: what the runner shows a step (recover, errToSorry, the
\ saves open, the depth), and steps that answer each refusal.
variable seen-recover  variable seen-sorry  variable seen-saves  variable seen-depth
: probe ( i -- ) drop lf-tac-recover? seen-recover ! lfr-top tfr-sorry @ seen-sorry !
  lfr-saves seen-saves ! lfr-depth seen-depth ! ;
tac-shape-plain lf-tactic: by-probe constant tac-k-probe
' probe tac-k-probe lf-tactic-action!
: probe-gap ( i -- ) drop lfa-e-tac-meta lf-tac-stop ;
tac-shape-plain lf-tactic: by-probe-gap constant tac-k-probe-gap
' probe-gap tac-k-probe-gap lf-tactic-action!
: probe-full ( i -- ) drop lfa-e-tac-full lf-tac-stop ;
tac-shape-plain lf-tactic: by-probe-full constant tac-k-probe-full
' probe-full tac-k-probe-full lf-tactic-action!
: probe-forth ( i -- ) drop -24 throw ;
tac-shape-plain lf-tactic: by-probe-forth constant tac-k-probe-forth
' probe-forth tac-k-probe-forth lf-tactic-action!
: final? ( code -- code flag ) lf-author-final? ;

\ ---- 3. Shapes, modes and rows.
: shape3 ( kind -- want names flags )
  lf-tactic-shape@ dup shape-want @ over shape-names @ rot shape-block @ ;
T{ tac-k-try shape3 tac-k-any-goals shape3 tac-k-repeat shape3
   -> 0 0 tac-block 0 0 tac-block 0 0 tac-block }T
T{ tac-k-first shape3 -> 0 0 tac-block tac-block-bars or tac-block-bare or }T
T{ tac-shape-alt shape-block @ -> tac-block }T
: mode@ ( kind -- mode ) lfr-row trow-mode @ ;
T{ tac-k-try mode@ tac-k-first mode@ tac-k-any-goals mode@ tac-k-repeat mode@
   -> lf-mode-try lf-mode-first lf-mode-any lf-mode-repeat }T
: mode4 ( mode -- open end fail flags )
  dup mode-open @ over mode-end @ rot dup mode-fail @ swap mode-flags @ ;
T{ lf-mode-try mode4 -> ' drop ' lfr-keep ' lfr-skip lfr-no-recover lfr-saving or }T
T{ lf-mode-first mode4 -> ' drop ' drop ' drop lfr-saving lfr-last-bare or }T
T{ lf-mode-tried mode4 -> ' drop ' lfr-alt-won 0 lfr-no-recover }T
T{ lf-mode-last mode4 -> ' drop ' lfr-alt-won 0 0 }T
T{ lf-mode-repeat mode4 -> ' drop ' lfr-repeat-end ' lfr-skip lfr-no-recover lfr-saving or }T
T{ lf-mode-any mode4 -> ' lfr-any-open ' lfr-any-end ' lfr-any-fail lfr-saving }T
: row-run@ ( kind -- xt ) lfr-row trow-run @ ;
T{ tac-k-try row-run@ tac-k-first row-run@ tac-k-any-goals row-run@ tac-k-repeat row-run@
   -> ' lf-tac-all ' lf-tac-all ' lf-tac-all ' lf-tac-all }T
T{ tac-k-first lf-tactic-alt@ tac-k-alt row-run@ -> ' lf-tac-alternative ' lfr-alt }T
T{ tac-k-try lf-tac-lean s" try" compare tac-k-first lf-tac-lean s" first" compare
   tac-k-any-goals lf-tac-lean s" any_goals" compare tac-k-repeat lf-tac-lean s" repeat" compare
   -> 0 0 0 0 }T
\ A bare alternative's step: kind |, its own shape, its parent by-first,
\ its | the place of an empty one (85, second place).
T{ hh s" by-first | ' h by-exact by-end" tactic-ran 2 step@ tac-kind @ 2 step@ tac-shape @
   2 step@ tac-parent @ 3 step@ tac-parent @ -> 0 tac-k-alt tac-shape-alt 1 2 }T

\ ---- 2. Malformed: a tactic before the first |, an empty alternative,
\ an empty by-first, | in a block of no bars (83).
T{ hh s" by-first ' h by-exact | ' h by-exact by-end" tactic-ran -> 72 }T
lf-tac-forget
T{ hh s" by-first | | ' h by-exact by-end" tactic-ran s" |" token? -> 85 true }T
lf-tac-forget
T{ hh s" by-first by-end" tactic-ran s" by-end" token? -> 85 true }T
lf-tac-forget
T{ hh s" by-try | ' h by-exact by-end" tactic-ran -> 83 }T
lf-tac-forget

\ ---- 1. by-try (Init/Tactics.lean:445): a Lean error taken back, the
\ state put back (a goal it closed open again), its error never final;
\ the block left open as a whole proof: 89 at end.
T{ hh s" by-try ' k by-exact by-end ' h by-exact" tactic-ran -> 0 }T
T{ hh s" by-try ' h by-exact by-end" tactic-ran -> 0 }T
T{ hk s" by-constructor by-try ' h by-exact ' h by-exact by-end ' h by-exact ' k by-exact"
   tactic-ran -> 0 }T
T{ hh s" by-try ' k by-exact by-end" tactic-ran -> 89 }T
lf-tac-forget
T{ hh s" by-try { ' k by-exact } by-end ' h by-exact" tactic-ran -> 0 }T
\ by-first (BuiltinTactic.lean:631-641): the first that ends; all fail:
\ the last one's error (96 at its by-exact, final at the proof's by); one
\ alone is that block; one that closes a goal and then fails is rolled
\ back whole (both goals open again).
T{ hh s" by-first | ' k by-exact | ' h by-exact by-end" tactic-ran -> 0 }T
T{ hh s" by-first | ' k by-exact | ' k by-exact by-end" tactic-ran -> 96 }T
lf-tac-forget
T{ hh s" by-first | ' h by-exact by-end" tactic-ran -> 0 }T
T{ hh s" by-first | ' k by-exact by-end" tactic-ran -> 96 }T
lf-tac-forget
T{ hk s" by-constructor by-first | ' h by-exact ' h by-exact | ' h by-exact ' k by-exact by-end"
   tactic-ran -> 0 }T
\ The first alternative that ends closes by-first: a later one never runs.
T{ hh s" by-first | ' h by-exact | by-probe-gap by-end" tactic-ran -> 0 }T
\ by-repeat (Repeat.lean:17-26): until a pass fails, that pass put back.
T{ hr s" by-repeat by-constructor by-end ' h by-exact ' h by-exact ' k by-exact" tactic-ran
   -> 0 }T
T{ hh s" by-repeat ' k by-exact by-end ' h by-exact" tactic-ran -> 0 }T
T{ hk s" by-repeat by-constructor ' h by-exact ' h by-exact by-end by-constructor ' h by-exact ' k by-exact"
   tactic-ran -> 0 }T
\ by-any-goals (BuiltinTactic.lean:256-270): each goal; the failed ones
\ kept; none ended: 469 at by-any-goals, also with no goal at all.
T{ hk s" by-constructor by-any-goals ' h by-exact by-end ' k by-exact" tactic-ran -> 0 }T
T{ hb s" by-constructor by-any-goals ' h by-exact by-end" tactic-ran s" by-any-goals" token?
   -> 469 true }T
lf-tac-forget
T{ hh s" ' h by-exact by-any-goals ' h by-exact by-end" tactic-ran -> 469 }T
lf-tac-forget
\ A failing by-all-goals (Lean's all_goals logs and aborts) and a <;>
\ chain inside a pass: taken back with the pass, the goal kept.
T{ hk s" by-constructor by-any-goals by-all-goals ' h by-exact by-end by-end ' k by-exact"
   tactic-ran -> 0 }T
T{ h3 s" by-and-intros by-any-goals by-all-goals ' h by-exact by-end by-end ' k by-exact"
   tactic-ran -> 0 }T
T{ hq s" by-constructor by-any-goals by-constructor <;> ' h by-exact by-end by-constructor ' h by-exact ' k by-exact"
   tactic-ran -> 0 }T
\ t <;> by-try and t <;> by-first (blocks as t2).
T{ hk s" by-constructor <;> by-try ' h by-exact by-end ' k by-exact" tactic-ran -> 0 }T
T{ hk s" by-constructor <;> by-first | ' k by-exact | ' h by-exact by-end" tactic-ran -> 0 }T
\ Three deep.
T{ hh s" by-try by-first | { ' k by-exact } | by-focus ' h by-exact by-end by-end by-end"
   tactic-ran -> 0 }T

\ ---- 4. Recover and errToSorry (Lean's withoutRecover; runTermElab,
\ ElabTerm.lean:31-39): try's and repeat's steps and first's alternatives
\ but the last without recover; any_goals keeps it; a have-by's
\ errToSorry is the block's and recover's, and its recover is its
\ errToSorry (review tb2-blocks3 finding 1: pinned Lean's x3-x5).
T{ hh s" by-try by-probe ' h by-exact by-end" tactic-ran seen-recover @ seen-sorry @ -> 0 false true }T
T{ hh s" by-repeat by-probe ' h by-exact by-end" tactic-ran seen-recover @ -> 0 false }T
T{ hh s" by-first | by-probe ' h by-exact | ' k by-exact by-end" tactic-ran seen-recover @
   -> 0 false }T
T{ hh s" by-first | ' k by-exact | by-probe ' h by-exact by-end" tactic-ran seen-recover @
   -> 0 true }T
T{ hh s" by-any-goals by-probe ' h by-exact by-end" tactic-ran seen-recover @ -> 0 true }T
T{ hh s" by-try a b = by-have-by: j by-probe ' h by-exact by-end by-end ' h by-exact"
   tactic-ran seen-recover @ seen-sorry @ -> 0 false false }T
T{ hh s" a b = by-have-by: j by-probe ' h by-exact by-end ' h by-exact" tactic-ran
   seen-recover @ seen-sorry @ -> 0 true true }T
T{ hh s" by-any-goals a b = by-have-by: j by-probe ' h by-exact by-end by-end ' h by-exact"
   tactic-ran seen-recover @ seen-sorry @ -> 0 true true }T
T{ hh s" by-try a b = by-have-by: j a b = by-have-by: i by-probe ' h by-exact by-end ' i by-exact by-end by-end ' h by-exact"
   tactic-ran seen-sorry @ -> 0 false }T
\ Q8 and the have-by inside a have-by: the term error is thrown there and
\ try takes it (Lean's q8 and q8_inner are accepted).
T{ hh s" by-try b a = by-have-by: j << ' h >> by-exact by-end by-end ' h by-exact" tactic-ran
   -> 0 }T
T{ hh s" by-try b a = by-have-by: j a b = by-have-by: i << ' h >> by-exact by-end ' k by-exact by-end by-end ' h by-exact"
   tactic-ran -> 0 }T
\ A brace's or all_goals' error in a have-by under a handler: thrown, as
\ recover there is errToSorry, false, and the handler takes the have back
\ (pinned Lean's x3, t09, t11, t12, x4, x5 and q2; 490 before the review
\ tb2-blocks3 finding 1). j is then unknown (76, Lean's Unknown identifier).
T{ hh s" by-try b a = by-have-by: j { ' h by-exact } by-end by-end ' h by-exact" tactic-ran
   -> 0 }T
T{ hh s" by-try b a = by-have-by: j { ' h by-exact } by-end ' k by-exact by-end ' h by-exact"
   tactic-ran -> 0 }T
T{ hh s" { by-try b a = by-have-by: j { ' h by-exact } by-end ' k by-exact by-end ' h by-exact }"
   tactic-ran -> 0 }T
T{ hk s" by-constructor <;> by-try b a = by-have-by: j { ' h by-exact } by-end ' j by-exact ' h by-exact by-end ' h by-exact ' k by-exact"
   tactic-ran -> 0 }T
T{ hh s" by-first | b a = by-have-by: j { ' h by-exact } by-end ' j by-exact | ' h by-exact by-end"
   tactic-ran -> 0 }T
T{ hh s" by-try b a = by-have-by: j { { ' h by-exact } } by-end by-end ' h by-exact"
   tactic-ran -> 0 }T
T{ hh s" by-try b a = by-have-by: j { ' h by-exact } by-end by-end ' j by-exact" tactic-ran
   final? -> 76 true }T
lf-tac-forget
T{ hh s" by-try b a = by-have-by: j by-all-goals ' h by-exact by-end by-end by-end ' j by-exact"
   tactic-ran final? -> 76 true }T
lf-tac-forget
\ An error Lean logs while a save is open: 490, final (the coordinator's
\ rule): a term in a pass, a brace in a pass, a have-by's goals in a pass.
T{ hh s" by-any-goals << ' h >> by-exact by-end" tactic-ran final? -> 490 true }T
lf-tac-forget
T{ hh s" by-any-goals { ' k by-exact } by-end ' h by-exact" tactic-ran final? -> 490 true }T
lf-tac-forget
T{ hh s" by-any-goals b a = by-have-by: j a b = ' h by-have: x by-end by-end" tactic-ran
   final? -> 490 true }T
lf-tac-forget
\ A have-by's unsolved goals inside try (errToSorry false): thrown, the
\ have taken back (pinned Lean's rec_try_have; h then meets b = a: 96).
T{ hh s" by-try b a = by-have-by: j a b = ' h by-have: x by-end by-end ' h by-exact"
   tactic-ran -> 0 }T
T{ hs s" by-try b a = by-have-by: j a b = ' h by-have: x by-end by-end ' h by-exact"
   tactic-ran -> 96 }T
lf-tac-forget
\ The same outside any save: Lean's rejection, final.
T{ hh s" << ' h >> by-exact" tactic-ran final? -> 467 true }T
lf-tac-forget
\ The save is taken before the step's log entry (lfr-step; review
\ tb2-blocks3 finding 2): a put-back drops the failed step's entry, so
\ the log holds the handler's own entry and the steps that ran well only.
: logged ( c-addr u c-addr' u' -- code n ) tactic-ran trun-log slab-count ;
T{ true lf-steps-record! hh s" ' h by-exact" logged -> 0 1 }T
T{ hh s" by-try ' k by-exact by-end ' h by-exact" logged -> 0 2 }T
T{ hh s" by-first | ' k by-exact | ' h by-exact by-end" logged -> 0 3 }T
T{ hh s" by-repeat ' k by-exact by-end ' h by-exact" logged false lf-steps-record! -> 0 2 }T
\ The saves: one before a handler's step, none before first's last
\ alternative, none left after a block.
T{ hh s" by-try by-probe ' h by-exact by-end" tactic-ran seen-saves @ lfr-saves -> 0 1 0 }T
T{ hh s" by-first | by-probe ' h by-exact | ' k by-exact by-end" tactic-ran seen-saves @
   -> 0 1 }T
T{ hh s" by-first | ' k by-exact | by-probe ' h by-exact by-end" tactic-ran seen-saves @
   lfr-saves -> 0 0 0 }T
T{ hh s" by-first | ' h by-exact | ' k by-exact by-end" tactic-ran lfr-saves -> 0 0 }T
\ ---- 6. Names given inside by-try and by-first stay after them.
T{ hh s" by-try a b = ' h by-have: x by-end ' x by-exact" tactic-ran -> 0 }T
T{ hh s" by-first | b a = ' k by-have: y ' k by-exact | a b = ' h by-have: z by-end ' z by-exact"
   tactic-ran -> 0 }T
T{ hh s" by-repeat by-probe ' k by-exact by-end ' h by-exact" tactic-ran seen-saves @ lfr-saves
   -> 0 1 0 }T
\ A handler clears the goals a chain of its held aside (lfr-fail-mode).
create fake-frame /tfr allot
T{ lf-mode-first fake-frame tfr-mode ! 7 fake-frame tfr-held ! fake-frame lfr-fail-mode
   fake-frame tfr-held @ -> -1 }T
\ lfr-keep and lfr-put-back: the save given up, -1 left (none held: no-op).
T{ -1 fake-frame tfr-save ! fake-frame lfr-keep fake-frame tfr-save @ -> -1 }T
\ A by-first alternative holding a <;> chain that fails: rolled back, the
\ next one runs on the goals as they were (frame fields outside a save).
T{ hk s" by-first | by-constructor <;> ' h by-exact | by-constructor ' h by-exact ' k by-exact by-end"
   tactic-ran -> 0 }T

\ ---- 1. Refusals pass through every handler: unsupported (93), no room
\ (88), a Forth exception, never taken for an alternative that failed.
: through ( c-addr u -- code ) hh 2swap tactic-ran ;
T{ s" by-try by-probe-gap by-end ' h by-exact" through -> 93 }T
T{ s" by-first | by-probe-gap | ' h by-exact by-end" through -> 93 }T
T{ s" by-any-goals by-probe-gap by-end ' h by-exact" through -> 93 }T
T{ s" by-repeat by-probe-gap by-end ' h by-exact" through -> 93 }T
T{ s" by-try by-probe-full by-end ' h by-exact" through -> 88 }T
T{ s" by-first | by-probe-full | ' h by-exact by-end" through -> 88 }T
T{ s" by-any-goals by-probe-full by-end ' h by-exact" through -> 88 }T
T{ s" by-repeat by-probe-full by-end ' h by-exact" through -> 88 }T
T{ s" by-try by-probe-forth by-end ' h by-exact" through -> 41 }T
T{ s" by-first | by-probe-forth | ' h by-exact by-end" through -> 41 }T
T{ s" by-any-goals by-probe-forth by-end ' h by-exact" through -> 41 }T
T{ s" by-repeat by-probe-forth by-end ' h by-exact" through -> 41 }T
lf-tac-forget

\ ---- 5. Fuel: a repeat that never fails is stopped (91); every k below
\ a passing run of each word gives 91 or 138 or the answer.
T{ 300 lf-tactic-fuel! hh s" by-repeat by-try ' k by-exact by-end by-end" tactic-ran
   lf-tactic-fuel-default -> 91 }T
lf-tac-forget
: exhausted-or-0? ( code -- flag ) dup 0= if drop true else lf-author-outcome outcome-exhausted = then ;
: all-text ( -- code )
  hk s" by-constructor by-try ' k by-exact by-end by-any-goals ' h by-exact by-end by-first | ' h by-exact | ' k by-exact by-end by-repeat ' k by-exact by-end"
  tactic-ran ;
T{ all-text -> 0 }T
: fuel-ran ( k -- code ) lf-tactic-fuel! all-text lf-tactic-fuel-default ;
: fuel-swept? ( -- flag ) true 20 0 do i fuel-ran exhausted-or-0? and loop 20 fuel-ran 0= and ;
T{ fuel-swept? -> true }T
lf-tac-forget

\ ---- 5. Every heap allocation refused in turn (the frames' and saves'
\ slabs given back first), every frame claim and every save claim refused
\ in turn: the answer or full, never another.
: blocks-anew ( -- ) trun-frames sweep-slab-anew trun-saves sweep-slab-anew ;
' blocks-anew sweep-slabs-xt !
: p-try ( x -- code outcome )
  drop hk s" by-constructor by-try ' h by-exact ' h by-exact by-end ' h by-exact ' k by-exact"
  text-full ;
: p-first ( x -- code outcome )
  drop hk s" by-constructor by-first | ' h by-exact ' h by-exact | ' h by-exact ' k by-exact by-end"
  text-full ;
: p-any ( x -- code outcome )
  drop hk s" by-constructor by-any-goals ' h by-exact by-end ' k by-exact" text-full ;
: p-repeat ( x -- code outcome )
  drop hr s" by-repeat by-constructor by-end ' h by-exact ' h by-exact ' k by-exact" text-full ;
T{ 0 ' p-try heap-sweep swept? 0 ' p-first heap-sweep swept? 0 ' p-any heap-sweep swept?
   0 ' p-repeat heap-sweep swept? -> true true true true }T
' trun-frames sweep-slab-xt !
T{ 0 ' p-try slab-sweep swept? 0 ' p-first slab-sweep swept? 0 ' p-any slab-sweep swept?
   0 ' p-repeat slab-sweep swept? -> true true true true }T
' trun-saves sweep-slab-xt !
T{ 0 ' p-try slab-sweep swept? 0 ' p-first slab-sweep swept? 0 ' p-any slab-sweep swept?
   0 ' p-repeat slab-sweep swept? -> true true true true }T
lf-tac-forget
.( blocks-3 test.fs: all tests passed) cr

\ Unit tests of n by-iterate tacs by-end (plan row TB2, small tactics 1;
\ src/front/tactics/iterate.fs) over decide's slice of Init in an
\ authoring run, by the classes of docs/development/TEST_COVERAGE_REVIEW.md,
\ through LeanForth text (tests/support/tactic-text.fs) and a probe tactic:
\ 1. outcomes: accepted; 90, 383, 89 with their places; a count that is no
\    numeral 99 (unsupported);
\ 2. malformed input: no count (86), an empty block (85), no by-end;
\ 3. records: the shape, the mode, the row and Lean's name;
\ 4. interfaces: the block's steps run exactly n times (none for 0),
\    nested counts multiply, the passes on the main goal of their moment;
\ 5. resources: step fuel at a count past it (91), every heap allocation
\    refused in turn (tests/support/meta-sweeps.fs): the answer or full;
\ 6. state: names given inside the block stay after it.
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
: hh ( -- c-addr u ) s" Nat explicit: a Nat explicit: b a b = explicit: h a b =" ;
: hk ( -- c-addr u )
  s" Nat explicit: a Nat explicit: b a b = explicit: h b a = explicit: k a b = b a = ∧" ;
: hr ( -- c-addr u )
  s" Nat explicit: a Nat explicit: b a b = explicit: h b a = explicit: k a b = a b = ∧ b a = ∧" ;

\ ---- Probe: a step that counts its runs.
variable runs
: probe ( i -- ) drop 1 runs +! ;
tac-shape-plain lf-tactic: by-probe-run constant tac-k-probe-run
' probe tac-k-probe-run lf-tactic-action!
: ran ( c-addr u c-addr' u' -- code n ) 0 runs ! tactic-ran runs @ ;

\ ---- 3. Records.
: shape3 ( kind -- want names flags )
  lf-tactic-shape@ dup shape-want @ over shape-names @ rot shape-block @ ;
T{ tac-k-iterate shape3 -> 1 0 tac-block }T
T{ tac-k-iterate lfr-row trow-mode @ tac-k-iterate lfr-row trow-run @ -> tit-mode ' lf-tac-all }T
T{ tit-mode mode-open @ tit-mode mode-end @ tit-mode mode-fail @ tit-mode mode-flags @
   -> ' tit-open ' tit-end 0 0 }T
T{ tac-k-iterate lf-tac-lean s" iterate" compare -> 0 }T

\ ---- 4. Interfaces: exactly n passes; 0 none; nested counts multiply.
T{ hh s" 3 by-iterate by-probe-run by-end ' h by-exact" ran -> 0 3 }T
T{ hh s" 0 by-iterate by-probe-run by-end ' h by-exact" ran -> 0 0 }T
T{ hh s" 2 by-iterate 3 by-iterate by-probe-run by-end by-probe-run by-end ' h by-exact" ran
   -> 0 8 }T
T{ hh s" 1 by-iterate by-probe-run by-probe-run by-end ' h by-exact" ran -> 0 2 }T
\ Each pass on the main goal of its moment: two constructors split twice.
T{ hr s" 2 by-iterate by-constructor by-end ' h by-exact ' h by-exact ' k by-exact" tactic-ran
   -> 0 }T

\ ---- 1. Outcomes: Lean's errors at the step that fails, inside the block.
T{ hh s" 2 by-iterate ' h by-exact by-end" tactic-ran s" by-exact" token? -> 90 true }T
lf-tac-forget
T{ hk s" 3 by-iterate by-constructor by-end" tactic-ran s" by-constructor" token? -> 383 true }T
lf-tac-forget
T{ hk s" 1 by-iterate by-constructor by-end ' h by-exact" tactic-ran -> 89 }T
lf-tac-forget
T{ hh s" a by-iterate ' h by-exact by-end" tactic-ran s" by-iterate" token? -> 99 true }T
lf-tac-forget

\ ---- 2. Malformed: no count, an empty block, no by-end.
T{ hh s" by-iterate ' h by-exact by-end" tactic-ran -> 86 }T
lf-tac-forget
T{ hh s" 2 by-iterate by-end ' h by-exact" tactic-ran s" by-end" token? -> 85 true }T
lf-tac-forget
T{ hh s" 2 by-iterate ' h by-exact" tactic-ran 0= -> false }T
lf-tac-forget

\ ---- 6. State: a name given inside stays after the block (a paren's).
T{ hh s" 1 by-iterate a b = Decidable by-have-by: d by-infer-instance by-end by-end ' d by-clear ' h by-exact"
   tactic-ran -> 0 }T

\ ---- 5. Resources: step fuel ends a count past it (91); heap refused in turn.
T{ hh s" 100000000 by-iterate by-skip by-end ' h by-exact" tactic-ran -> 91 }T
lf-tac-forget
: frames-anew ( -- ) lfa-brackets sweep-slab-anew ;
' frames-anew sweep-slabs-xt !
: p-two ( x -- code outcome )
  drop hr s" 2 by-iterate by-constructor by-end ' h by-exact ' h by-exact ' k by-exact" text-full ;
: p-zero ( x -- code outcome ) drop hh s" 0 by-iterate ' h by-exact by-end ' h by-exact" text-full ;
T{ 0 ' p-two heap-sweep swept? 0 ' p-zero heap-sweep swept? -> true true }T
lf-tac-forget
.( batch-small-1b test.fs: all tests passed) cr

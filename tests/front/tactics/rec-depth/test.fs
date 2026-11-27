\ Unit tests of the runner's bound on Lean's recursion depth (src/front/
\ tactic-run.fs's lf-tac-depth-most and the modes' weights; re-check of
\ the Forth review of small-tactics-1, 2026-11-26, finding 1) over
\ decide's slice of Init in an authoring run, by the classes of
\ docs/development/TEST_COVERAGE_REVIEW.md. Each text nests one kind of
\ block k deep, one per line (a .lf line of them would pass the reader's
\ line limit, error 39), around iterate 126 (Lean's 2n + 3 = 255 levels)
\ or around skip alone, on both sides of LeanForth's bound and past the
\ depth where pinned Lean 4.35.0 fails ("maximum recursion depth has
\ been reached"; the twins and their verdicts: rec-depth.lean, which
\ pinned Lean accepts, and rec-depth-wrong.lean, which it refuses, both
\ in this folder and checked by check.py --lean):
\ | block, around       | LeanForth accepts | 99 from | Lean accepts | fails |
\ | try, iterate 126    | 27                | 28      | 35           | 36    |
\ | any_goals, it. 126  | 27                | 28      | 41           | 42    |
\ | all_goals, it. 126  | 27                | 28      | 41           | 42    |
\ | first, it. 126      | 27                | 28      | 41           | 42    |
\ | focus, it. 126      | 27                | 28      | 41           | 42    |
\ | braces, it. 126     | 27                | 28      | 200          | 250   |
\ | have-by, it. 126    | 13                | 14      | 16           | 17    |
\ | <;> try, it. 126    | 13                | 14      | 16           | 18    |
\ | repeat, it. 126     | 21                | 22      | 27           | 28    |
\ | it. 126 around try  | 27                | 28      | 35           | 36    |
\ | have-by, skip       | 29                | 30      | 32           | 34    |
\ | try, skip           | 59                | 60      | 72           | 74    |
\ Lean's counts are of its one-line spelling (parentheses where its
\ parser needs them: try (X), first | (X), skip <;> try (X), (have z :
\ a = b := by { X; exact h }), repeat ((X); fail)), the costliest
\ measured; written in layout Lean accepts more (try 60, have-by 22).
\ 1. outcomes: accepted below the bound, 99 at the step whose block would
\    pass it, never caught by a handler around (try, first, any_goals,
\    repeat: 99 is not Lean's error); a huge count's weight cannot wrap;
\ 2. malformed input: none of its own (the reader's records);
\ 3. records: each mode's weight;
\ 4. interfaces: the weights add over the open blocks only;
\ 5. resources: the bound is the open blocks', not the steps run;
\ 6. state: after the refusal the frame is taken off and the goals are
\    as before the block (lfr-unopen).
\ Nothing here accepts a theorem: only the kernel's check does.
require ../../../support/tester.fs
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

\ ---- The text: a theorem, its proof's lines, run (test-only buffer).
8192 constant rd-room
create rd-text rd-room allot  variable rd-text#
: rd+ ( c-addr u -- )
  dup rd-text# @ + rd-room > abort" rec-depth test: text too long"
  tuck rd-text rd-text# @ + swap move rd-text# +! ;
: rd-line ( c-addr u -- ) rd+ s\" \n" rd+ ;
: rd-lines ( c-addr u n -- ) 0 ?do 2dup rd-line loop 2drop ;
: rd-thm ( c-addr u -- )
  0 rd-text# ! s" theorem t " rd+ rd+ s"  := by" rd-line ;
: rd-one ( -- ) s" Nat explicit: a Nat explicit: b a b = explicit: h a b =" rd-thm ;
: rd-two ( -- )
  s" Nat explicit: a Nat explicit: b a b = explicit: h a b = a b = ∧" rd-thm ;
: rd-run ( -- code )
  s" end t" rd-line lf-tac-forget lf-author-begin rd-text rd-text# @ lf-author-text drop
  lf-author-code ;
: rd-close ( -- code ) s" ' h by-exact" rd-line rd-run ;
: it126 ( -- ) s" 126 by-iterate by-skip by-end" rd-line ;
\ k blocks opened by the line open, X, then k lines close.
: nest ( open u close u k xt -- ) swap >r >r 2swap 2r@ drop rd-lines r> execute r> rd-lines ;
: around ( open u close u k -- code ) rd-one ['] it126 nest rd-close ;
: skip0 ( -- ) s" by-skip" rd-line ;
: around0 ( open u close u k -- code ) rd-one ['] skip0 nest rd-close ;
: tries ( k -- code ) >r s" by-try" s" by-end" r> around ;
: tries0 ( k -- code ) >r s" by-try" s" by-end" r> around0 ;
: haves ( k -- code ) >r s" a b = by-have-by: z" s" ' h by-exact by-end" r> around ;
: haves0 ( k -- code ) >r s" a b = by-have-by: z" s" ' h by-exact by-end" r> around0 ;
: anys ( k -- code ) >r s" by-any-goals" s" by-end" r> around ;
: alls ( k -- code ) >r s" by-all-goals" s" by-end" r> around ;
: firsts ( k -- code ) >r s" by-first |" s" by-end" r> around ;
: focuses ( k -- code ) >r s" by-focus" s" by-end" r> around ;
: thens ( k -- code ) >r s" by-skip <;> by-try" s" by-end" r> around ;
\ repeat: each pass fails at its second exact (no goals), so each repeat
\ ends after one pass, the state back (Lean's repeat ((X); fail)).
: repeats ( k -- code ) >r s" by-repeat" s" ' h by-exact ' h by-exact by-end" r> around ;
\ braces close the goal inside: the innermost holds the exact.
: it126h ( -- ) it126 s" ' h by-exact" rd-line ;
: braces ( k -- code ) >r rd-one s" {" s" }" r> ['] it126h nest rd-run ;
\ iterate 126 around k tries of skip.
: in-iterate ( k -- code )
  >r rd-one s" 126 by-iterate" rd-line s" by-try" s" by-end" r> ['] skip0 nest
  s" by-end" rd-line rd-close ;

\ ---- 3. Records: the bound and each mode's weight (in units of two of
\ Lean's levels).
T{ lf-tac-depth-most -> 240 }T
: weight ( step mode -- w )
  trun-frames slab-clear lfr-push tuck tfr-step ! lfr-weight ;
T{ 0 lf-mode-nested weight 5 lf-mode-nested weight -> 4 8 }T
T{ 5 lf-mode-try weight 5 lf-mode-any weight 5 lf-mode-first weight -> 4 4 4 }T
T{ 5 lf-mode-tried weight 5 lf-mode-last weight 5 lf-mode-repeat weight -> 0 0 5 }T
T{ 5 lf-mode-done weight 5 lf-mode-brace weight 5 lf-mode-focus weight -> 4 4 4 }T
T{ 5 lf-mode-per-goal weight 5 lf-mode-then weight -> 4 4 }T
T{ lf-mode-repeat mode-weight @ tit-mode mode-weight @ -> ' lfr-repeat-weight ' tit-weight }T
trun-frames slab-clear

\ ---- 1, 4. Outcomes on both sides of the bound, around iterate 126
\ (the proof's by 4 + iterate 128: 132 of 240).
T{ 27 tries -> 0 }T
T{ 28 tries s" by-iterate" token? -> 99 true }T   lf-tac-forget
T{ 35 tries 36 tries -> 99 99 }T   lf-tac-forget
T{ 27 anys 28 anys 42 anys 48 anys -> 0 99 99 99 }T   lf-tac-forget
T{ 27 alls 28 alls 42 alls -> 0 99 99 }T   lf-tac-forget
T{ 27 firsts 28 firsts 42 firsts -> 0 99 99 }T   lf-tac-forget
T{ 27 focuses 28 focuses 42 focuses -> 0 99 99 }T   lf-tac-forget
T{ 27 braces 28 braces -> 0 99 }T   lf-tac-forget
T{ 13 haves -> 0 }T
T{ 14 haves s" by-iterate" token? -> 99 true }T   lf-tac-forget
T{ 17 haves 18 haves -> 99 99 }T   lf-tac-forget
T{ 13 thens 14 thens 18 thens -> 0 99 99 }T   lf-tac-forget
T{ 21 repeats 22 repeats -> 0 99 }T   lf-tac-forget
\ Blocks opened inside an iterate weigh on top of it: 99 at the try.
T{ 20 in-iterate 27 in-iterate -> 0 0 }T
T{ 28 in-iterate s" by-try" token? -> 99 true }T   lf-tac-forget
T{ 36 in-iterate -> 99 }T   lf-tac-forget
\ No iterate (older than iterate, the same bound): have-by and try.
T{ 29 haves0 -> 0 }T
T{ 30 haves0 s" by-have-by:" token? -> 99 true }T   lf-tac-forget
T{ 40 haves0 -> 99 }T   lf-tac-forget
T{ 59 tries0 -> 0 }T
T{ 60 tries0 s" by-try" token? -> 99 true }T   lf-tac-forget
T{ 70 tries0 80 tries0 -> 99 99 }T   lf-tac-forget
\ with_reducible weighs 2 (review of small tactics 2, Low 2): 118 nested
\ pass, 119 are 99 at the innermost (u-rd-wr.lf; Lean takes 167).
: wrs0 ( k -- code ) >r s" by-with-reducible" s" by-end" r> around0 ;
T{ 118 wrs0 -> 0 }T
T{ 119 wrs0 s" by-with-reducible" token? -> 99 true }T   lf-tac-forget

\ ---- 1, 5. The largest count (nine digits, the reader's most) weighs the
\ bound and 2 (so that no sum wraps on a 32-bit host): 99 at once, three
\ nested too, never the step fuel's 91.
T{ rd-one s" 999999999 by-iterate by-skip by-end" rd-line rd-close
   s" by-iterate" token? -> 99 true }T   lf-tac-forget
T{ rd-one s" 999999999 by-iterate" 3 rd-lines s" by-skip" rd-line s" by-end" 3 rd-lines
   rd-close -> 99 }T   lf-tac-forget

\ ---- 6. State: the refused frame taken off (the root and 59 tries stay
\ open) and a focus's goals put back (both goals, not its first alone).
: refused-focus ( -- code )
  rd-two s" by-constructor" rd-line s" by-try" 59 rd-lines
  s" by-focus ' h by-exact by-end" rd-line s" by-end" 59 rd-lines rd-close ;
T{ refused-focus s" by-focus" token? -> 99 true }T
T{ lfr-depth lf-goals run-count -> 60 2 }T   lf-tac-forget
.( rec-depth test.fs: all tests passed) cr

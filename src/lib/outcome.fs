\ One outcome vocabulary for every walker and checker (ADR 0008). Values
\ 0-3 are the ones all modules already used. An outcome is a status, not a
\ flag: 0 means success here but false for a flag, so test an outcome with
\ ok? or compare it with a named outcome, never with IF directly. Running
\ out of fuel (exhausted: more time would help) and running out of room
\ (full: more memory or a larger limit would help) are distinct, and
\ neither is ever ok. Chains of steps that stop at the first failure:
\ outcome-and, outcome-steps, ok-and, ok-with, the ok-then and ok-keep
\ words, and the loops ok-each and ok-fold; the tests over every index,
\ all? (a flag) and ok-all? (a flag and an outcome), with ok-true? their
\ stop test, and over some index, any? and ok-any? (ok-found? its stop
\ test); 2dup-under gives a step of these loops a copy of its two values;
\ outcome-first! keeps a first
\ failure in a cell and ok-store a step's result only on ok; no-result,
\ ok-or-none and room-result give a step's result with its outcome.
\ No state, no dependencies.
\ Example: each cell of a table checked, stopping at the first failure.
\   create table 3 , 5 , -1 , 7 ,
\   : cell-ok ( table k -- table outcome ) cells over + @ 0> flag>outcome ;
\   table 2 ' cell-ok ok-each nip .  table 4 ' cell-ok ok-each nip .
\   outcome-full outcome-text type   \ prints: 0 1 full

0 constant outcome-ok           \ succeeded; for a comparison, shown equal
1 constant outcome-invalid      \ malformed input or corrupted state
2 constant outcome-exhausted    \ out of fuel: the processing budget ran out
3 constant outcome-unknown      \ supported, but this cautious rule cannot decide
4 constant outcome-rejected     \ shown wrong: ill-typed or definitely different
5 constant outcome-unsupported  \ uses a feature LeanForth does not implement yet
6 constant outcome-full         \ out of room: a store, stack, depth or size limit

: outcome? ( n -- flag ) outcome-ok outcome-full 1+ within ;
: ok? ( outcome -- flag ) outcome-ok = ;
\ Any value outside the vocabulary becomes invalid, so a corrupted or
\ unexpected status can never read as success.
: outcome-sane ( n -- outcome ) dup outcome? 0= if drop outcome-invalid then ;
\ A validity flag as an outcome: only a true flag (all bits set) is ok;
\ false, or a status passed by mistake, is invalid.
: flag>outcome ( flag -- outcome ) true = if outcome-ok else outcome-invalid then ;
\ A room flag as an outcome: only a true flag is ok; false, or a status
\ passed by mistake, is full.
: room>outcome ( flag -- outcome ) true = if outcome-ok else outcome-full then ;
\ Whether a visit bounded by fuel and by room (a frame, a depth or a level)
\ can go ahead: no fuel left (zero or a corrupted negative fuel) is
\ exhausted whatever the room, so the fuel decides when both are short;
\ otherwise no room is full.
: visit-outcome ( fuel room? -- outcome )
  swap 0> if room>outcome else drop outcome-exhausted then ;
\ Continue only on ok: keep x and give true, or replace x by the failing
\ outcome and give false.
: ok-then? ( x outcome -- x true | outcome false )
  dup ok? if drop true else nip false then ;
\ The same with two values kept, and with three.
: ok-then2? ( x1 x2 outcome -- x1 x2 true | outcome false )
  dup ok? if drop true else nip nip false then ;
: ok-then3? ( x1 x2 x3 outcome -- x1 x2 x3 true | outcome false )
  dup ok? if drop true else nip nip nip false then ;
\ Two outcomes as one: the first that is not ok, else ok.
: outcome-and ( outcome1 outcome2 -- outcome ) over ok? if nip else drop then ;
\ Run the steps ( x -- outcome ) listed at a (0 ends the list) in order
\ until one is not ok: that outcome, or ok. Example: `create checks
\ ' size-ok , ' sum-ok , 0 ,` then `file checks outcome-steps`.
: outcome-steps ( x a -- outcome )
  dup @ 0= if 2drop outcome-ok exit then
  2dup @ execute dup ok? 0= if nip nip exit then drop cell+ recurse ;
\ Run the step xt ( i*x -- j*x outcome ) only when the outcome so far is
\ ok; else keep that outcome, the values below it untouched. Example:
\ `outcome-ok ['] size-ok ok-and ['] sum-ok ok-and`.
: ok-and ( i*x outcome xt -- j*x outcome ) over ok? if nip execute else drop then ;
\ The same for a step ( x -- outcome ) of x, which stays below for the
\ next. Example: `file outcome-ok ['] size-ok ok-with ['] sum-ok ok-with nip`.
: ok-with ( x outcome xt -- x outcome ) over ok? if nip over swap execute else drop then ;
\ The same for a step that gives a result, with one or two values kept
\ below it for the next step: keep them and give true, or drop them, keep
\ the result beside the failing outcome and give false.
: ok-keep? ( x result outcome -- x result true | result outcome false )
  dup ok? if drop true else rot drop false then ;
: ok-keep2? ( x1 x2 result outcome -- x1 x2 result true | result outcome false )
  dup ok? if drop true else 2swap 2drop false then ;
\ A failure that has no result: -1 in the result's place.
: no-result ( outcome -- -1 outcome ) -1 swap ;
\ A step's result kept only on ok: on any other outcome -1 takes its
\ place, so a failure never hands on a half-made value.
: ok-or-none ( x outcome -- x outcome | -1 outcome ) dup ok? 0= if nip no-result then ;
\ A result that needed room, as a store gives it ( x true | false ): x and
\ ok, or -1 and full.
: room-result ( x true | false -- x outcome )
  if outcome-ok else outcome-full no-result then ;
\ A copy of the two values under the top one, put under it: what a step
\ of the loops below reads when it keeps two values under its index k.
\ Example: `: in-at? ( x addr k -- x addr flag ) 2dup-under cells + @ = ;`.
: 2dup-under ( x1 x2 k -- x1 x2 x1 x2 k ) >r 2dup r> ;
\ Run the step xt ( i*x k -- i*x outcome ) for k = 0, 1, ... n-1 while it
\ gives ok: ok, or the first outcome that is not ok, after which no step
\ runs. The values below k are the steps' to read and replace, keeping
\ their number (a step that changes them makes a fold). n <= 0 runs
\ nothing. The xt is the index of an outer loop run once and read with J,
\ so each step finds i*x and k alone on the data stack. Example, a check
\ of each cell of a table: `table 3 ' cell-ok ok-each nip` with
\ `: cell-ok ( table k -- table outcome ) cells over + @ checked ;`.
: ok-each ( i*x n xt -- i*x outcome )
  dup 1+ swap ?do 0 max 0 ?do i j execute dup ok? 0= if unloop unloop exit then drop
  loop loop outcome-ok ;
\ A fold with a context: x := xt ( x k y -- x' outcome ) for k = 0, 1,
\ ... n-1, y given to every step, while ok: the last x' and ok, or the
\ failing step's x' (-1 when it has none) and its outcome. n <= 0 gives x
\ and ok. Example, applying f to each argument of a job: `f n job
\ ['] apply-arg ok-fold` with apply-arg ( f k job -- f' outcome ).
: ok-fold ( x n y xt -- x' outcome )
  dup 1+ swap ?do swap 0 max 0 ?do tuck i swap j execute ok-keep? 0= if
  unloop unloop exit then swap loop loop drop outcome-ok ;
\ Go on only after a true answer that is ok: true; else false, the
\ outcome (ok after a plain false) and false, so a failing step never
\ reads as a plain false. The stop test of ok-all? and slab.fs's
\ slab-all?.
: ok-true? ( flag outcome -- true | false outcome false )
  over 0<> over ok? and if 2drop true else nip false swap false then ;
\ Whether the test xt ( i*x k -- i*x flag ) holds for k = 0, 1, ... n-1:
\ true, or false at the first k it fails, after which none runs. n <= 0
\ gives true. The values below k are the tests' to read, as ok-each's,
\ and the xt is kept the same way. Example, whether the first three
\ cells of a table are positive: `table 3 ' cell-pos? all? nip` with
\ `: cell-pos? ( table k -- table flag ) cells over + @ 0> ;`.
: all? ( i*x n xt -- i*x flag )
  dup 1+ swap ?do 0 max 0 ?do i j execute 0= if false unloop unloop exit then
  loop loop true ;
\ Whether the test xt ( i*x k -- i*x flag ) holds for some k = 0, 1, ...
\ n-1: true at the first k it holds, after which none runs; else false.
\ n <= 0 gives false. The values below k and the xt as in all?. Example,
\ whether a table's first three cells hold a negative one: `table 3 '
\ cell-neg? any? nip` with `: cell-neg? ( table k -- table flag ) cells
\ over + @ 0< ;`.
: any? ( i*x n xt -- i*x flag )
  dup 1+ swap ?do 0 max 0 ?do i j execute if true unloop unloop exit then
  loop loop false ;
\ The same for k = lo, lo+1, ... hi-1 (none when hi <= lo), for a search
\ that starts part way. Example, whether a table holds a negative cell
\ from index 2 on: `table 2 n ' cell-neg? any-in? nip`.
: any-in? ( i*x lo hi xt -- i*x flag )
  dup 1+ swap ?do over max swap ?do i j execute if true unloop unloop exit then
  loop loop false ;
\ The same as all? for a test that may fail, xt ( i*x k -- i*x flag outcome ):
\ true and ok when every test gives true and ok; else false beside the
\ first answer's outcome that stops the loop, ok for a plain false. n <=
\ 0 gives true and ok. Example, Level.beq of a constant's universe
\ arguments: `s1 s2 n ' level-at ok-all? 2swap 2drop` with level-at
\ ( s1 s2 k -- s1 s2 flag outcome ).
: ok-all? ( i*x n xt -- i*x flag outcome )
  dup 1+ swap ?do 0 max 0 ?do i j execute ok-true? 0= if unloop unloop exit then
  loop loop true outcome-ok ;
\ Stop at a true answer that is ok (true, ok and true) or at any failure
\ (false, its outcome and true, so a failure never reads as an answer);
\ go on after a false answer that is ok (false). The stop test of ok-any?.
: ok-found? ( flag outcome -- true outcome true | false outcome true | false )
  dup ok? 0= if nip false swap true exit then drop 0<> dup if outcome-ok true then ;
\ The same as any? for a test that may fail, xt ( i*x k -- i*x flag
\ outcome ): true and ok at the first true answer that is ok; false and
\ the outcome of the first failure; after either none runs; false and ok
\ when no answer is true. n <= 0 gives false and ok. Example, whether an
\ argument mentions the type: `node n k ' arg-mentions? ok-any? 2swap
\ 2drop` with arg-mentions? ( node n i -- node n flag outcome ).
: ok-any? ( i*x n xt -- i*x flag outcome )
  dup 1+ swap ?do 0 max 0 ?do i j execute ok-found? if unloop unloop exit then
  loop loop false outcome-ok ;
\ Keep the first failure in a cell: store the outcome only while the cell
\ holds ok, so a later outcome, ok or not, never hides an earlier failure.
: outcome-first! ( outcome a-addr -- ) dup @ ok? if ! else 2drop then ;
\ Store a step's result x at a-addr only on ok, and give the outcome: on
\ any other outcome x is dropped and the cell left as it was, so a failure
\ never stores a half-made value. Example, a field set from a reader:
\ `json read-size rec size-field swap ok-store`.
: ok-store ( x a-addr outcome -- outcome ) ok-then? if ! outcome-ok else nip then ;
\ The outcome's name, as diagnostics write it. A value outside the
\ vocabulary is named "invalid", as outcome-sane reads it, and so is any
\ value the CASE does not list. One arm per outcome, two to a line: seven
\ names need four lines, which is shorter and plainer than a table.
: outcome-text ( outcome -- c-addr u )
  outcome-sane case
    outcome-ok of s" ok" endof  outcome-invalid of s" invalid" endof
    outcome-exhausted of s" exhausted" endof  outcome-unknown of s" unknown" endof
    outcome-rejected of s" rejected" endof  outcome-unsupported of s" unsupported" endof
    outcome-full of s" full" endof  s" invalid" rot endcase ;
\ Drop an argument and report invalid input.
: drop-invalid ( x -- outcome ) drop outcome-invalid ;

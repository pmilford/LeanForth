\ One outcome vocabulary for every walker and checker (ADR 0008). Values
\ 0-3 are the ones all modules already used. An outcome is a status, not a
\ flag: 0 means success here but false for a flag, so test an outcome with
\ ok? or compare it with a named outcome, never with IF directly. Running
\ out of fuel (exhausted: more time would help) and running out of room
\ (full: more memory or a larger limit would help) are distinct, and
\ neither is ever ok. Chains of steps that stop at the first failure:
\ outcome-and, outcome-steps, ok-and, ok-with, the ok-then and ok-keep
\ words, and the loops ok-each and ok-fold; outcome-first! keeps a first
\ failure in a cell.
\ No state, no dependencies.

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
\ Run the step xt ( i*x k -- i*x outcome ) for k = 0, 1, ... n-1 while it
\ gives ok: ok, or the first outcome that is not ok, after which no step
\ runs. The values below k are the steps' to read and replace, keeping
\ their number (a step that changes them makes a fold). n <= 0 runs
\ nothing. The xt is the index of an outer loop run once and read with J,
\ so each step finds i*x and k alone on the data stack. Example, a check
\ of each cell of a table: `table 3 ['] cell-ok ok-each nip` with
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
\ Keep the first failure in a cell: store the outcome only while the cell
\ holds ok, so a later outcome, ok or not, never hides an earlier failure.
: outcome-first! ( outcome a-addr -- ) dup @ ok? if ! else 2drop then ;
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

\ Compare untrusted Forth concrete level evaluation with Lean's level table.
\ The emitted integers are diagnostics, never checked theorem judgments.
include ../../src/core/levels.fs
include ../../src/core/level-scope.fs
include ../../src/core/level-value.fs
decimal
variable table-left
variable table-right
variable table-kind

\ Build a concrete numeral as successors of zero, returning its arena index.
: table-level ( n -- index )
  0 swap 0 ?do lf-level-succ 0= if -1 throw then loop ;

\ Emit case metadata and the successful experimental concrete value.
: table-emit ( kind left right root -- )
  50000 lf-level-value if drop -1 throw then >r
  rot . swap . . r> . cr ;

\ Construct independent small max/imax cases to avoid arena accumulation.
: emit-concrete-cases ( -- )
  6 0 do 6 0 do 2 0 do
    k table-left ! j table-right ! i table-kind !
    lf-level-reset
    table-left @ table-level table-right @ table-level
    table-kind @ if lf-level-imax else lf-level-max then
    0= if -1 throw then
    >r table-kind @ table-left @ table-right @ r> table-emit
  loop loop loop ;

\ Construct nested cases whose node indices differ from their values.
: emit-nested-cases ( -- )
  lf-level-reset
  2 table-level drop
  2 0 lf-level-imax 0= if -1 throw then drop
  1 3 lf-level-imax 0= if -1 throw then >r 2 0 0 r> table-emit
  3 1 lf-level-max 0= if -1 throw then >r 2 1 0 r> table-emit
  2 3 lf-level-imax 0= if -1 throw then >r 2 2 0 r> table-emit
  3 2 lf-level-max 0= if -1 throw then >r 2 3 0 r> table-emit ;
lf-lscope-context-reset
emit-concrete-cases
emit-nested-cases
bye

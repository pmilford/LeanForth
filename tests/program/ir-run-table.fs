\ Three-way comparison of task 2.5.4 (docs/programming/PROGRAM_IR_RUN.md),
\ the Forth half: the reader translates src/program/clamp.fs and
\ examples.fs into IR, the IR interpreter runs each case, and wherever the
\ host can run the word too, the host's result must be the same data
\ stack, item for item. Every case is printed as
\   program word fuel x1 ... xn -> ok y1 ... ym   |   -> fail failure
\ (stacks bottom first) for tests/program/ir_run_differential.py, which
\ under make check gives the same lines to Lean's evaluation of the model
\ (tests/reference/program-ir-run.lean) and requires identical output.
\ Lines starting with # are the summary. Finite tests, not a proof.
\
\ Cases: the input sets of the existing tables (clamp-table.fs,
\ example-reference-table.fs, extra-program-range-table.fs,
\ add-reference-table.fs, abs-reference-table.fs,
\ factorial-reference-table.fs, gcd-reference-table.fs), each below a
\ sentinel 12345; pseudo-random inputs (xorshift64, seed ir-run-seed) for
\ the six words and their helpers; and failure cases for the model alone:
\ too few inputs, fuel sweeps, division outside the model and an unknown
\ word. Finally two planted faults in the primitive table must make the
\ host comparison fail. Requires 64-bit cells.
require ../../src/program/ir-reader.fs
require ../../src/program/ir-run.fs
require ../../src/program/clamp.fs
require ../../src/program/examples.fs
decimal
1 cells 8 <> [if] .( ir-run-table requires 64-bit cells ) cr bye [then]
[undefined] ir-run-seed [if] 20261102 constant ir-run-seed [then]

\ Loading a source file through the reader into the interpreter.
: load-source ( c-addr u -- )
  irx-load-start ['] irx-load-line -rot lf-ir-read-file
  outcome-ok <> abort" the reader refused the source"
  irx-load-finish outcome-ok <> abort" the interpreter refused the reader's IR" ;

\ The case being run.
2variable case-program
2variable case-word
variable case-xt          \ the host word, or 0 when only the model may run it
variable case-fuel
variable case-count
create case-inputs 8 cells allot
128 constant ample        \ enough fuel for every host case
: case-input ( i -- x ) cells case-inputs + @ ;
: inputs ( x1..xn n -- )
  dup case-count ! 0 ?do case-count @ 1- i - cells case-inputs + ! loop ;
: use-word ( xt c-addr u -- ) case-word 2! case-xt ! ample case-fuel ! ;
: model-only ( c-addr u -- ) 0 -rot use-word ;

variable quiet            \ true while planted faults run: nothing printed
variable cases
variable host-cases
variable mismatches

\ Printing.
: .int ( n -- ) 0 .r ;
: .case ( -- )
  case-program 2@ type space case-word 2@ type space case-fuel @ .int
  case-count @ 0 ?do space i case-input .int loop ;
: machine-item ( i -- x ) irx-item 0= abort" no such item" ;
: .stack ( -- ) ." ok" irx-depth 0 ?do space i machine-item .int loop ;
: .result ( outcome -- )
  ."  -> " ok? if .stack else ." fail " irx-result irx-result-text type then ;
: report ( outcome -- ) quiet @ if drop else .case .result cr then ;

\ The host's stack after the word, against the interpreter's.
: host-item ( x0..xn-1 i -- x0..xn-1 xi ) depth 2 - swap - pick ;
: item-differs? ( x0..xn-1 i -- x0..xn-1 flag ) dup >r host-item r> machine-item <> ;
: agree? ( x0..xn-1 -- x0..xn-1 flag )
  depth irx-depth <> if false exit then
  depth 0 ?do i item-differs? if false unloop exit then loop true ;
: clear-host ( x0..xn-1 -- ) depth 0 ?do drop loop ;
: host-inputs ( -- x1..xn ) case-count @ 0 ?do i case-input loop ;
: mismatch ( -- )
  1 mismatches +! quiet @ 0= if ." # mismatch: " .case cr then ;
: host-check ( outcome -- )
  case-xt @ 0= if drop exit then 1 host-cases +!
  ok? 0= if mismatch exit then depth 0<> abort" the test's own stack is not empty"
  host-inputs case-xt @ execute agree? >r clear-host r> 0= if mismatch then ;

: machine-inputs ( -- ) irx-clear case-count @ 0 ?do i case-input irx-push drop loop ;
: run-case ( -- )
  1 cases +! machine-inputs case-fuel @ case-word 2@ irx-run dup report host-check ;

\ Pseudo-random values: xorshift64, from ir-run-seed.
variable rng
ir-run-seed rng !
: xorshift ( -- u ) rng @ dup 13 lshift xor dup 7 rshift xor dup 17 lshift xor dup rng ! ;
: below ( n -- u ) xorshift 0 rot um/mod drop ;
: near-edge ( -- n ) 4 below 2 below if lf-example-min + else lf-example-max swap - then ;
: any-value ( -- n )
  4 below case
    0 of 41 below 20 - endof
    1 of xorshift endof
    2 of near-edge endof
    xorshift 32 rshift 2147483648 - swap endcase ;
: natural ( -- n ) any-value dup 0< if invert then ;

\ Values the existing tables use.
create bounds32 -2147483648 , -2147483647 , -1 , 0 , 1 , 2147483646 , 2147483647 ,
: bound32 ( i -- n ) cells bounds32 + @ ;
create bounds64 lf-example-min , lf-example-min 1+ , -1 , 0 , 1 ,
  lf-example-max 1- , lf-example-max ,
: bound64 ( i -- n ) cells bounds64 + @ ;
create bounds-add lf-example-min , lf-example-min 1+ ,
  -2147483648 , -2147483647 , -1 , 0 , 1 , 2147483646 , 2147483647 ,
  lf-example-max 1- , lf-example-max ,
: bound-add ( i -- n ) cells bounds-add + @ ;

\ Triples: value lower upper, for lf-clamp and lf-in-range.
variable tv  variable tl  variable tu
: triple ( -- ) 12345 tv @ tl @ tu @ 4 inputs run-case ;
: small-triples ( -- )
  4 -3 do i tl ! 4 -3 do i tu ! 4 -3 do i tv ! triple loop loop loop ;
variable bound-xt          \ the boundary table of table-triples
: bound ( i -- n ) bound-xt @ execute ;
: table-triples ( xt -- )
  bound-xt ! 7 0 do i bound tl ! 7 0 do i bound tu ! 7 0 do i bound tv ! triple loop loop
  loop ;
: random-triples ( n -- )
  0 ?do 12345 any-value any-value any-value 4 inputs run-case loop ;

: clamp-cases ( -- )
  s" clamp" case-program 2! ['] lf-clamp s" lf-clamp" use-word
  small-triples ['] bound32 table-triples 300 random-triples ;
: in-range-cases ( -- )
  ['] lf-in-range s" lf-in-range" use-word
  small-triples ['] bound32 table-triples ['] bound64 table-triples 300 random-triples
  ['] lf-within-closed? s" lf-within-closed?" use-word 100 random-triples ;

\ Pairs a b.
: pair ( a b -- ) 12345 -rot 3 inputs run-case ;
: random-pairs ( n -- ) 0 ?do any-value any-value pair loop ;
: add-cases ( -- )
  ['] lf-checked-add s" lf-checked-add" use-word
  9 -8 do 9 -8 do j i pair loop loop
  11 0 do 11 0 do j bound-add i bound-add pair loop loop 300 random-pairs
  ['] lf-add-overflow? s" lf-add-overflow?" use-word 100 random-pairs
  ['] lf-add-above? s" lf-add-above?" use-word 50 random-pairs
  ['] lf-add-below? s" lf-add-below?" use-word 50 random-pairs ;
: gcd-cases ( -- )
  ['] lf-gcd s" lf-gcd" use-word
  9 -3 do 9 -3 do j i pair loop loop
  lf-example-max 0 pair  0 lf-example-max pair  lf-example-max lf-example-max pair
  lf-example-max 1 pair  lf-example-min 1 pair  1 lf-example-min pair
  200 random-pairs 100 0 do natural natural pair loop
  ['] lf-euclid s" lf-euclid" use-word 100 0 do natural natural pair loop ;

\ Single inputs.
: single ( n -- ) 12345 swap 2 inputs run-case ;
: abs-cases ( -- )
  ['] lf-checked-abs s" lf-checked-abs" use-word
  129 -128 do i single loop
  lf-example-min single  lf-example-min 1+ single  lf-example-min 2 + single
  lf-example-max 2 - single  lf-example-max 1- single  lf-example-max single
  300 0 do any-value single loop ;
: small-or-any ( -- n ) 2 below if 30 below else any-value then ;
: factorial-cases ( -- )
  ['] lf-factorial s" lf-factorial" use-word
  22 -128 do i single loop  lf-example-min single  lf-example-min 1+ single
  300 0 do small-or-any single loop
  ['] lf-factorial-from s" lf-factorial-from" use-word
  100 0 do any-value 65 below 5 - pair loop
  ['] lf-product-over? s" lf-product-over?" use-word
  100 0 do any-value natural 1 max pair loop ;
: constant-cases ( -- )
  ['] lf-example-max s" lf-example-max" use-word 12345 1 inputs run-case
  ['] lf-example-min s" lf-example-min" use-word 12345 1 inputs run-case ;

\ Failures and fuel, for the model alone.
: fuel-sweep ( n -- ) 0 ?do i case-fuel ! run-case loop ;
: clamp-failures ( -- )
  s" lf-clamp" model-only 1 2 2 inputs run-case  0 case-fuel ! 4 3 1 3 inputs run-case
  1 0 1 3 inputs 3 fuel-sweep
  s" lf-missing" model-only 0 inputs run-case 0 case-fuel ! run-case ;
: example-failures ( -- )
  s" lf-gcd" model-only 7 1 inputs run-case  48 18 2 inputs 10 fuel-sweep
  s" lf-euclid" model-only -5 3 2 inputs run-case  5 -3 2 inputs run-case
  s" lf-product-over?" model-only 5 0 2 inputs run-case  5 -2 2 inputs run-case
  -5 2 2 inputs run-case
  s" lf-factorial" model-only 5 1 inputs 11 fuel-sweep  0 inputs run-case
  s" lf-checked-add" model-only 3 4 2 inputs 7 fuel-sweep  3 1 inputs run-case
  s" lf-checked-abs" model-only 0 inputs run-case lf-example-min 1 inputs 5 fuel-sweep
  s" lf-in-range" model-only 1 2 2 inputs run-case 1 0 2 3 inputs 4 fuel-sweep
  s" lf-within-closed?" model-only 1 2 2 inputs run-case
  s" lf-example-min" model-only 0 inputs 4 fuel-sweep
  s" lf-missing" model-only 7 1 inputs run-case ;

: clamp-program ( -- ) s" src/program/clamp.fs" load-source clamp-cases clamp-failures ;
: example-program ( -- )
  s" src/program/examples.fs" load-source s" examples" case-program 2!
  in-range-cases add-cases gcd-cases abs-cases factorial-cases constant-cases
  example-failures ;

\ Planted faults: with MAX and MIN exchanged, or * replaced by +, in the
\ interpreter's primitive table, the host comparison must fail.
: prim-action ( c-addr u -- addr )
  irx-prims irx-find 0= abort" no primitive" irx-prims store-slot irx-prim-action ;
\ The host check needs an empty data stack, so the counts go to variables.
variable caught-max-min
variable caught-times
: caught ( addr -- ) mismatches @ swap ! 0 mismatches ! ;
: swap-max-min ( -- ) s" max" prim-action s" min" prim-action 2dup @ swap @ rot ! swap ! ;
: plant-max-min ( -- ) swap-max-min clamp-program caught-max-min caught swap-max-min ;
: plant-times ( -- )
  ['] + s" *" prim-action ! example-program caught-times caught
  ['] irx-times s" *" prim-action ! ;
: plant-faults ( -- )
  mismatches @ >r 0 mismatches ! true quiet ! plant-max-min plant-times
  false quiet ! r> mismatches !
  ." # planted faults detected: max/min " caught-max-min @ .int
  ."  times " caught-times @ .int cr
  caught-max-min @ 0= caught-times @ 0= or abort" a planted fault was not detected" ;

\ The counts after clamp-program alone, for the clamp receipt.
: clamp-summary ( -- )
  ." # clamp cases " cases @ .int ."  host " host-cases @ .int ."  mismatches "
  mismatches @ .int cr ;
: summary ( -- )
  ." # cases " cases @ .int ."  host " host-cases @ .int
  ."  mismatches " mismatches @ .int ."  seed " ir-run-seed .int cr ;
: main ( -- )
  clamp-program clamp-summary example-program summary plant-faults
  mismatches @ abort" the interpreter and the host disagree" ;
main bye

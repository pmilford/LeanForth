\ Run the IR interpreter (src/program/ir-run.fs) on a file of cases
\   program word fuel x1 ... xn -> anything
\ where program is the path of an IR text file, and print each case with
\ the interpreter's result after the arrow, in the format of
\ tests/program/ir-run-table.fs. tests/program/ir_run_differential.py uses
\ it for randomly generated programs and gives the same lines to Lean's
\ evaluation of the model. Usage, from the repository root:
\   gforth tests/program/ir-run-cases.fs -e 's" CASES" run-case-file bye'
\ A planted fault (plant-fault) changes one primitive's host word first;
\ the comparison must then fail. A program the interpreter refuses to load
\ stops the run.
require ../../src/program/ir-run.fs
decimal

\ The program loaded last, by path.
create program-path 256 chars allot
variable program-length
: loaded? ( c-addr u -- flag ) program-path program-length @ compare 0= ;
: remember ( c-addr u -- ) dup program-length ! program-path swap chars move ;
: use-program ( c-addr u -- )
  2dup loaded? if 2drop exit then dup 255 > abort" path too long"
  2dup remember irx-load-file outcome-ok <> abort" the interpreter refused a program" ;

\ Tokens of a case line, by the interpreter's own splitter.
: next-token ( c-addr u -- c-addr' u' token-addr token-u )
  irx-split 2swap 1 /string 0 max 2swap ;
: case-digits ( c-addr u -- n ) 0 0 2swap >number nip abort" not a number" drop ;
: case-number ( c-addr u -- n )
  2dup 1 min s" -" compare 0= if 1 /string case-digits negate else case-digits then ;

\ A case: the text before the arrow, then the inputs on the machine's stack.
: arrow ( c-addr u -- args-addr args-u ) 2dup s"  -> " search 0= abort" no arrow" nip - ;
: push-inputs ( c-addr u -- )
  begin dup while next-token case-number irx-push drop repeat 2drop ;
: run-line ( c-addr u -- )
  arrow 2dup type ."  -> " next-token use-program next-token 2>r next-token case-number
  >r irx-clear push-inputs r> 2r> irx-run ok? if
    ." ok" irx-depth 0 ?do space i irx-item 0 .r loop
  else ." fail " irx-result irx-result-text type then cr ;

create case-text 512 chars allot
: run-case-file ( c-addr u -- )
  r/o open-file throw >r
  begin case-text 510 r@ read-line throw while case-text swap run-line repeat
  drop r> close-file throw ;

\ Planted faults: replace the host word of a primitive.
: plant-fault ( xt c-addr u -- ) irx-prims irx-find 0= abort" no primitive"
  irx-prims store-slot irx-prim-action ! ;

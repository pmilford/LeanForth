\ Tests of the program IR interpreter (src/program/ir-run.fs): loading the
\ reader's golden IR and its live output, every loading diagnostic, every
\ primitive's edge cases, every failure of the model, the exact fuel that
\ calls and loops spend, the capacities, and separate contexts. Lean's
\ agreement on all of this is checked by tests/program/ir_run_differential.py.
include ../support/tester.fs
require ../../src/program/ir-reader.fs
require ../../src/program/ir-run.fs
decimal

\ Writing IR text a line at a time.
: >ir ( c-addr u -- ) irx-load-line ;
: program ( -- ) irx-load-start s" lf-ir 0.1" >ir s" source t.fs" >ir ;
: loaded ( -- outcome ) irx-load-finish ;
\ Running: the stack is set from the host stack, n items.
: given ( x1..xn n -- ) irx-clear 0 ?do irx-push drop loop ;
: out-stack ( -- x1..xn ) irx-depth 0 ?do i irx-item loop ;
\ given pushes in reverse, so stacks are written with reversed helpers.
: in1 ( a -- ) 1 given ;
: in2 ( a b -- ) swap 2 given ;
: in3 ( a b c -- ) rot rot swap 3 given ;
: run ( fuel c-addr u -- outcome ) irx-run ;

\ Golden IR of the six example words, and the reader's live output.
T{ s" tests/program/ir/clamp.ir" irx-load-file -> outcome-ok }T
T{ 5 0 3 in3 1 s" lf-clamp" run out-stack -> outcome-ok 3 -1 }T
T{ -5 0 3 in3 1 s" lf-clamp" run out-stack -> outcome-ok 0 -1 }T
T{ 5 4 3 in3 1 s" lf-clamp" run out-stack -> outcome-ok 0 }T
T{ s" tests/program/ir/examples.ir" irx-load-file -> outcome-ok }T
T{ 48 18 in2 21 s" lf-gcd" run out-stack -> outcome-ok 6 -1 }T
T{ 4 in1 8 s" lf-factorial" run out-stack -> outcome-ok 24 -1 }T
T{ 0 given 2 s" lf-example-max" run out-stack -> outcome-ok max-n }T
T{ 0 given 3 s" lf-example-min" run out-stack -> outcome-ok max-n invert }T
: load-source ( c-addr u -- reader loader )
  irx-load-start ['] irx-load-line -rot lf-ir-read-file irx-load-finish ;
T{ s" src/program/examples.fs" load-source -> outcome-ok outcome-ok }T
T{ max-n 1 in2 9 s" lf-checked-add" run out-stack -> outcome-ok 0 }T
T{ max-n 1- 1 in2 9 s" lf-checked-add" run out-stack -> outcome-ok max-n -1 }T
T{ s" src/program/clamp.fs" load-source -> outcome-ok outcome-ok }T

\ Loading diagnostics. Each refusal leaves no program to run.
: just ( c-addr u -- outcome ) program >ir loaded ;
: in-body ( c-addr u -- outcome ) program s" word f" >ir >ir s" end" >ir loaded ;
T{ program loaded -> outcome-ok }T
T{ s" word f" just -> outcome-invalid }T
T{ irx-load-start s" lf-ir 0.2" >ir s" source t.fs" >ir loaded -> outcome-invalid }T
T{ irx-load-start s" lf-ir 0.1" >ir s" source " >ir loaded -> outcome-invalid }T
T{ irx-load-start s" lf-ir 0.1" >ir loaded -> outcome-invalid }T
T{ s"   prim dup" just -> outcome-invalid }T
T{ s"   prim dup" in-body -> outcome-ok }T
T{ 0 s" f" run -> outcome-exhausted }T
T{ 7 in1 1 s" f" run out-stack -> outcome-ok 7 7 }T
T{ s"   prim DUP" in-body -> outcome-invalid }T
T{ 7 in1 1 s" f" run -> outcome-invalid }T
T{ s"   prim pick" in-body -> outcome-invalid }T
T{ s"   frob" in-body -> outcome-invalid }T
T{ s"   lit 12a" in-body -> outcome-invalid }T
T{ s"   lit -" in-body -> outcome-invalid }T
T{ s"   lit -9223372036854775807" in-body -> outcome-ok }T
T{ s"   lit 9223372036854775808" in-body -> outcome-unsupported }T
T{ s"   lit 99999999999999999999" in-body -> outcome-unsupported }T
T{ s"   lit 9x" in-body -> outcome-invalid }T
T{ s"  prim dup" in-body -> outcome-invalid }T
T{ s"    prim dup" in-body -> outcome-invalid }T
T{ s"   prim  dup" in-body -> outcome-invalid }T
T{ s"   prim dup " in-body -> outcome-invalid }T
T{ s"   prim dup x" in-body -> outcome-invalid }T
T{ s"   prim dup @3:4" in-body -> outcome-ok }T
T{ s"   prim dup @3" in-body -> outcome-invalid }T
T{ s"   prim dup @3:4x" in-body -> outcome-invalid }T
T{ s"   prim dup @:4" in-body -> outcome-invalid }T
T{ s"   exit 1" in-body -> outcome-invalid }T
T{ s"   else" in-body -> outcome-invalid }T
T{ s"   then" in-body -> outcome-invalid }T
T{ s"   while" in-body -> outcome-invalid }T
T{ s"   repeat" in-body -> outcome-invalid }T
T{ s"   if" in-body -> outcome-invalid }T
T{ s"   word g" in-body -> outcome-invalid }T
T{ program s" word f" >ir s"   if" >ir s"   then" >ir s" end" >ir loaded -> outcome-ok }T
T{ program s" word f" >ir s"   if" >ir s"     else" >ir s"   then" >ir s" end" >ir loaded
   -> outcome-invalid }T
T{ program s" word f" >ir s"   if" >ir s"   else" >ir s"   else" >ir s"   then" >ir
  s" end" >ir loaded
   -> outcome-invalid }T
T{ program s" word f" >ir s"   begin" >ir s"   repeat" >ir s" end" >ir loaded ->
  outcome-invalid }T
T{ program s" word f" >ir s"   begin" >ir s"   while" >ir s"   then" >ir s" end" >ir
  loaded
   -> outcome-invalid }T
T{ program s" word f" >ir s"   if" >ir s" end" >ir loaded -> outcome-invalid }T
T{ program s" word f" >ir loaded -> outcome-invalid }T
T{ program s" word f" >ir s"  end" >ir loaded -> outcome-invalid }T
T{ program s" word f" >ir s" end" >ir s" word f" >ir s" end" >ir loaded
   -> outcome-invalid }T
T{ program s" word f g" >ir s" end" >ir loaded -> outcome-invalid }T
T{ program s"  word f" >ir s" end" >ir loaded -> outcome-invalid }T
T{ program s" word abcdefghijklmnopqrstuvwxyz012345" >ir s" end" >ir loaded ->
  outcome-full }T
T{ program s" word abcdefghijklmnopqrstuvwxyz01234" >ir s" end" >ir loaded
   -> outcome-ok }T
T{ s" tests/program/no-such-file.ir" irx-load-file -> outcome-invalid }T
\ Only the first problem counts, and the line it was on.
T{ program s" word f" >ir s"   frob" >ir s"   prim nope" >ir loaded irx-load-lines
   -> outcome-invalid 4 }T

\ Capacities.
: lines ( c-addr u n -- ) 0 ?do 2dup >ir loop 2drop ;
T{ program s" word f" >ir s"   prim dup" irx-code-capacity lines s" end" >ir loaded ->
  outcome-ok }T
T{ program s" word f" >ir s"   prim dup" irx-code-capacity 1+ lines s" end" >ir loaded
   -> outcome-full }T
\ c-addr u indented by depth levels of two spaces, in the buffer deep.
create deep 80 chars allot
: indented ( c-addr u depth -- c-addr' u' )
  2* >r deep r@ bl fill tuck deep r@ chars + swap chars move r> + deep swap ;
: open-ifs ( n -- ) 0 ?do s" if" i 1+ indented >ir loop ;
: close-ifs ( n -- ) dup 0 ?do s" then" 2 pick i - indented >ir loop drop ;
T{ program s" word f" >ir irx-open-capacity open-ifs irx-open-capacity close-ifs s" end"
  >ir loaded
   -> outcome-ok }T
T{ program s" word f" >ir irx-open-capacity 1+ open-ifs loaded -> outcome-full }T
\ "word wN" for definition number N.
: named ( n -- c-addr u ) 0 <# #s [char] w hold bl hold [char] d hold [char] r hold
  [char] o hold [char] w hold #> ;
: define-words ( n -- ) 0 ?do i named >ir s" end" >ir loop ;
T{ program irx-def-capacity define-words loaded -> outcome-ok }T
T{ program irx-def-capacity 1+ define-words loaded -> outcome-full }T

\ One-word programs for the run tests: "word f" with the given lines.
: f( ( -- ) program s" word f" >ir ;
: )f ( -- ) s" end" >ir loaded outcome-ok <> abort" test program refused" ;
: f ( fuel -- outcome ) s" f" run ;

\ Stack primitives.
T{ f( s"   prim rot" >ir )f 1 2 3 in3 1 f out-stack -> outcome-ok 2 3 1 }T
T{ f( s"   prim tuck" >ir )f 1 2 in2 1 f out-stack -> outcome-ok 2 1 2 }T
T{ f( s"   prim over" >ir s"   prim nip" >ir )f 1 2 in2 1 f out-stack -> outcome-ok 1 1 }T
T{ f( s"   prim 2dup" >ir s"   prim 2drop" >ir s"   prim swap" >ir )f 1 2 in2 1 f
  out-stack
   -> outcome-ok 2 1 }T
T{ f( s"   prim >r" >ir s"   prim r@" >ir s"   prim r>" >ir s"   prim +" >ir )f 5 in1 1 f
  out-stack
   -> outcome-ok 10 }T
\ Arithmetic wraps on the host's cells.
T{ f( s"   prim +" >ir )f max-n 1 in2 1 f out-stack -> outcome-ok max-n invert }T
T{ f( s"   prim -" >ir )f max-n invert 1 in2 1 f out-stack -> outcome-ok max-n }T
T{ f( s"   prim *" >ir )f max-n 2 in2 1 f out-stack -> outcome-ok -2 }T
T{ f( s"   prim *" >ir )f -3 7 in2 1 f out-stack -> outcome-ok -21 }T
T{ f( s"   prim negate" >ir )f max-n invert in1 1 f out-stack
   -> outcome-ok max-n invert }T
T{ f( s"   prim abs" >ir )f max-n invert in1 1 f out-stack -> outcome-ok max-n invert }T
T{ f( s"   prim abs" >ir )f -7 in1 1 f out-stack -> outcome-ok 7 }T
T{ f( s"   prim 1+" >ir )f max-n in1 1 f out-stack -> outcome-ok max-n invert }T
T{ f( s"   prim 1-" >ir )f max-n invert in1 1 f out-stack -> outcome-ok max-n }T
\ Division only where the model defines it.
T{ f( s"   prim /" >ir )f 7 2 in2 1 f out-stack -> outcome-ok 3 }T
T{ f( s"   prim mod" >ir )f 7 2 in2 1 f out-stack -> outcome-ok 1 }T
T{ f( s"   prim /" >ir )f 0 5 in2 1 f out-stack -> outcome-ok 0 }T
T{ f( s"   prim /" >ir )f 7 0 in2 1 f irx-result -> outcome-unsupported irx-unmodeled }T
T{ f( s"   prim /" >ir )f -7 2 in2 1 f -> outcome-unsupported }T
T{ f( s"   prim mod" >ir )f 7 -2 in2 1 f -> outcome-unsupported }T
\ Comparisons give -1 or 0; bits act on the two's-complement pattern.
T{ f( s"   prim <>" >ir )f 1 2 in2 1 f out-stack -> outcome-ok -1 }T
T{ f( s"   prim <" >ir )f max-n invert 0 in2 1 f out-stack -> outcome-ok -1 }T
T{ f( s"   prim 0>" >ir )f 0 in1 1 f out-stack -> outcome-ok 0 }T
T{ f( s"   prim 0<>" >ir )f -5 in1 1 f out-stack -> outcome-ok -1 }T
T{ f( s"   prim xor" >ir )f 12 10 in2 1 f out-stack -> outcome-ok 6 }T
T{ f( s"   prim invert" >ir )f 0 in1 1 f out-stack -> outcome-ok -1 }T
T{ f( s"   prim rshift" >ir )f -1 1 in2 1 f out-stack -> outcome-ok max-n }T
T{ f( s"   prim rshift" >ir )f -1 irx-cell-bits 1- in2 1 f out-stack -> outcome-ok 1 }T
T{ f( s"   prim rshift" >ir )f -1 irx-cell-bits in2 1 f -> outcome-unsupported }T
T{ f( s"   prim rshift" >ir )f -1 -1 in2 1 f -> outcome-unsupported }T
T{ f( s"   prim max" >ir s"   prim true" >ir s"   prim false" >ir )f 3 9 in2 1 f out-stack
   -> outcome-ok 9 -1 0 }T
T{ f( s"   lit -7" >ir s"   prim min" >ir )f 3 in1 1 f out-stack -> outcome-ok -7 }T

\ Underflow: data and return stacks, at each primitive's arity.
T{ f( s"   prim rot" >ir )f 1 2 in2 1 f irx-result -> outcome-invalid irx-underflow }T
T{ f( s"   prim r>" >ir )f 0 given 1 f irx-result -> outcome-invalid irx-underflow }T
T{ f( s"   prim r@" >ir )f 0 given 1 f -> outcome-invalid }T
T{ f( s"   if" >ir s"   then" >ir )f 0 given 1 f irx-result -> outcome-invalid
  irx-underflow }T
\ A word cannot see its caller's return stack, and must leave its own empty.
T{ program s" word g" >ir s"   prim r>" >ir s" end" >ir s" word f" >ir s"   prim >r" >ir
   s"   call g" >ir s"   prim r>" >ir )f 5 in1 2 f irx-result -> outcome-invalid
   irx-underflow }T
T{ program s" word g" >ir s"   lit 1" >ir s" end" >ir s" word f" >ir s"   prim >r" >ir
   s"   call g" >ir s"   prim r>" >ir )f 5 in1 2 f out-stack -> outcome-ok 1 5 }T
T{ f( s"   prim >r" >ir )f 5 in1 1 f irx-result -> outcome-invalid irx-unbalanced }T
T{ f( s"   prim >r" >ir s"   exit" >ir )f 5 in1 1 f irx-result -> outcome-invalid
  irx-unbalanced }T
\ A constant runs on empty stacks and must leave exactly one value.
: c( ( -- ) program s" constant c" >ir ;
: c ( fuel -- outcome ) s" c" run ;
T{ c( s"   lit 4" >ir s"   lit 5" >ir s"   prim *" >ir )f 9 in1 1 c out-stack ->
  outcome-ok 9 20 }T
T{ c( s"   prim dup" >ir )f 9 in1 1 c irx-result -> outcome-invalid irx-underflow }T
T{ c( s"   lit 1" >ir s"   lit 2" >ir )f 0 given 1 c irx-result -> outcome-invalid
  irx-bad-constant }T
T{ c( )f 0 given 1 c irx-result -> outcome-invalid irx-bad-constant }T
T{ c( s"   lit 1" >ir s"   exit" >ir )f 0 given 1 c irx-result -> outcome-invalid
  irx-bad-constant }T
T{ c( s"   lit 1" >ir s"   lit 1" >ir s"   prim >r" >ir )f 0 given 1 c irx-result
   -> outcome-invalid irx-bad-constant }T
\ Unknown words: an undefined callee fails only when called, after the
\ fuel check.
T{ f( s"   call nowhere" >ir )f 0 given 2 f irx-result
   -> outcome-invalid irx-unknown-word }T
T{ f( s"   call nowhere" >ir )f 0 given 1 f irx-result -> outcome-exhausted
  irx-out-of-fuel }T
T{ f( s"   prim drop" >ir s"   call nowhere" >ir )f 0 given 1 f irx-result
   -> outcome-invalid irx-underflow }T
T{ 0 given 1 s" nowhere" run irx-result -> outcome-invalid irx-unknown-word }T
T{ 0 given 0 s" nowhere" run irx-result -> outcome-exhausted irx-out-of-fuel }T
\ A later definition may be called, and a word may call itself.
T{ program s" word f" >ir s"   call g" >ir s" end" >ir s" word g" >ir s"   lit 3" >ir )f
   0 given 2 f out-stack -> outcome-ok 3 }T
T{ f( s"   call f" >ir )f 0 given 5 f irx-result -> outcome-exhausted irx-out-of-fuel }T

\ EXIT leaves the word from inside IF and loops; IF takes any nonzero flag.
T{ f( s"   if" >ir s"     lit 1" >ir s"     exit" >ir s"   then" >ir s"   lit 2" >ir )f
   5 in1 1 f out-stack -> outcome-ok 1 }T
T{ f( s"   if" >ir s"     lit 1" >ir s"   else" >ir s"     lit 2" >ir s"   then" >ir
  s"   lit 3" >ir )f
   0 in1 1 f out-stack -> outcome-ok 2 3 }T
T{ f( s"   begin" >ir s"     prim dup" >ir s"   while" >ir s"     lit 9" >ir s"     exit"
  >ir
   s"   repeat" >ir )f 4 in1 2 f out-stack -> outcome-ok 4 9 }T

\ Fuel. A call spends one unit; a loop needs one unit per completed body
\ plus one for its last test, and what the body spent is gone for the rest
\ of the block; an IF branch's own spending is not.
: count( ( -- )
  f( s"   begin" >ir s"     prim dup" >ir s"   while" >ir s"     prim 1-" >ir
  s"   repeat" >ir ;
\ g calls h, so a call of g needs two units of fuel.
: g-h ( -- ) s" end" >ir s" word g" >ir s"   call h" >ir s" end" >ir s" word h" >ir ;
T{ count( )f 3 in1 5 f out-stack -> outcome-ok 0 }T
T{ count( )f 3 in1 4 f irx-result -> outcome-exhausted irx-out-of-fuel }T
T{ count( s"   call g" >ir g-h )f 3 in1 5 f irx-result -> outcome-exhausted
  irx-out-of-fuel }T
T{ count( s"   call g" >ir g-h )f 3 in1 6 f out-stack -> outcome-ok 0 }T
\ An IF part that loops twice: its spending does not reach the call after it.
: branch( ( -- )
  f( s"   if" >ir s"     lit 2" >ir s"     begin" >ir s"       prim dup" >ir
  s"     while" >ir s"       prim 1-" >ir s"     repeat" >ir s"     prim drop" >ir
  s"   then" >ir
  s"   call g" >ir g-h ;
T{ branch( )f -1 in1 4 f out-stack -> outcome-ok }T
T{ branch( )f -1 in1 3 f irx-result -> outcome-exhausted irx-out-of-fuel }T
T{ count( )f 3 in1 -1 f -> outcome-invalid }T

\ Room: the machine's stacks and frames are finite; the model's are not.
T{ f( s"   begin" >ir s"     lit 1" >ir s"   while" >ir s"     lit 0" >ir s"   repeat" >ir
  )f
   0 given 1000 f irx-result -> outcome-full irx-no-room }T
T{ f( s"   begin" >ir s"     lit 1" >ir s"   while" >ir s"     lit 0" >ir s"     prim >r"
  >ir
   s"   repeat" >ir )f 0 given 1000 f -> outcome-full }T
T{ f( s"   call f" >ir )f 0 given 1000 f -> outcome-full }T
: fill-machine ( -- ) irx-clear irx-data-capacity 0 ?do i irx-push drop loop ;
T{ fill-machine 7 irx-push irx-depth -> outcome-full irx-data-capacity }T

\ Where the last run stopped.
T{ program s" word f" >ir s"   lit 1 @3:5" >ir s"   prim / @3:7" >ir )f
   0 given 1 f irx-last -> outcome-invalid 3 7 }T

\ A program belongs to the context that loaded it.
T{ f( s"   lit 6" >ir )f 0 given 1 f -> outcome-ok }T
variable other
T{ context-new swap other ! -> 0 }T
T{ other @ context-use 0 given 1 f lf-context @ context-main <> -> outcome-invalid true }T
T{ context-main context-use 0 given 1 f out-stack -> outcome-ok 6 }T
T{ other @ context-free -> 0 }T

\ Before any load, or without one, nothing runs.
T{ program 0 given 1 f -> outcome-invalid }T

bye

\ Tests of the program IR reader (src/program/ir-reader.fs): the golden IR
\ of the six example words, every diagnostic with its location, the
\ capacities, and that no source token is ever executed. Run from the
\ repository root, like every test file.
include ../support/tester.fs
require ../../src/program/ir-reader.fs

\ Golden files: every emitted line must equal the next line of the file.
variable golden-file
variable golden-mismatches
create golden-text 256 chars allot
: golden-next ( -- c-addr u flag )
  golden-text 254 golden-file @ read-line throw golden-text -rot ;
: golden-miss ( c-addr u c-addr u -- )
  ." expected: " type cr ." got:      " type cr 1 golden-mismatches +! ;
: golden-check ( c-addr u -- )
  golden-next 0= if 2drop s" (end of file)" golden-miss exit then
  2over 2over compare if golden-miss else 2drop 2drop then ;
: golden ( c-addr u -- ) r/o open-file throw golden-file ! 0 golden-mismatches ! ;
: golden-end ( -- mismatches )
  golden-next nip nip if 1 golden-mismatches +! then
  golden-file @ close-file throw golden-mismatches @ ;
: read-golden ( c-addr u c-addr u -- outcome mismatches )
  golden ['] golden-check -rot lf-ir-read-file golden-end ;

T{ s" src/program/clamp.fs" s" tests/program/ir/clamp.ir" read-golden -> outcome-ok 0 }T
T{ s" src/program/examples.fs" s" tests/program/ir/examples.ir" read-golden
   -> outcome-ok 0 }T
T{ lf-ir-reason -> ir-why-none }T

\ Lines fed one at a time; the last emitted line is kept for inspection.
create last-text 128 chars allot
variable last-length
: keep-last ( c-addr u -- ) 127 min dup last-length ! last-text swap chars move ;
: written ( -- c-addr u ) last-text last-length @ ;
: start ( -- ) ['] keep-last s" t.fs" lf-ir-start ;
: feed ( c-addr u -- ) lf-ir-feed ;
\ The outcome, the reason and where it stopped.
: verdict ( -- outcome reason line column ) lf-ir-finish lf-ir-reason lf-ir-where ;

\ Accepted input, comments anywhere, a definition over several lines.
T{ start s" : double ( n -- 2n ) dup + ; \ a comment" feed verdict
   -> outcome-ok ir-why-none 1 0 }T
T{ written s" end @1:28" compare -> 0 }T
T{ start s" : f" feed s"   -5 07 if exit then" feed s" ;" feed verdict
   -> outcome-ok ir-why-none 3 0 }T
T{ start s" : f 1 ;" feed s" : g f f ;" feed s" decimal" feed verdict
   -> outcome-ok ir-why-none 3 0 }T
T{ start s" 3 constant three  : f three ;" feed verdict -> outcome-ok ir-why-none 1 0 }T
T{ start s" : f begin dup while 1- repeat ;" feed verdict -> outcome-ok ir-why-none 1 0 }T
T{ start s" : f if else then ;" feed verdict -> outcome-ok ir-why-none 1 0 }T
T{ start verdict -> outcome-ok ir-why-none 0 0 }T

\ Each diagnostic, with the line and column of the token that caused it.
T{ start s" : f   foo ;" feed verdict -> outcome-unsupported ir-why-unknown 1 7 }T
T{ written s" unsupported @1:7: not a known word or 32-bit decimal: foo" compare
   -> 0 }T
T{ start s" : f DUP ;" feed verdict -> outcome-unsupported ir-why-unknown 1 5 }T
T{ start s" : f 2147483648 ;" feed verdict -> outcome-unsupported ir-why-unknown 1 5 }T
T{ start s" : f 2147483647 -2147483647 $10 ;" feed verdict
   -> outcome-unsupported ir-why-unknown 1 28 }T
T{ start s" : f begin dup until ;" feed verdict
   -> outcome-unsupported ir-why-not-ir 1 15 }T
T{ start s" : f 10 0 do loop ;" feed verdict -> outcome-unsupported ir-why-not-ir 1 10 }T
T{ start s" dup" feed verdict -> outcome-unsupported ir-why-left-over 1 0 }T
T{ start s" dup" feed s" : f ;" feed verdict
   -> outcome-unsupported ir-why-left-over 2 1 }T
T{ start s" 1 2" feed verdict -> outcome-unsupported ir-why-left-over 1 0 }T
T{ start s" if" feed verdict -> outcome-unsupported ir-why-outside 1 1 }T
T{ start s" : f ; f" feed verdict -> outcome-unsupported ir-why-outside 1 7 }T
T{ start s" : f decimal ;" feed verdict -> outcome-unsupported ir-why-inside 1 5 }T
T{ start s" : f 1 constant x ;" feed verdict -> outcome-unsupported ir-why-inside 1 7 }T
T{ start s" : f then ;" feed verdict -> outcome-invalid ir-why-unbalanced 1 5 }T
T{ start s" : f else ;" feed verdict -> outcome-invalid ir-why-unbalanced 1 5 }T
T{ start s" : f if else else then ;" feed verdict
   -> outcome-invalid ir-why-unbalanced 1 13 }T
T{ start s" : f begin while while repeat ;" feed verdict
   -> outcome-invalid ir-why-unbalanced 1 17 }T
T{ start s" : f begin dup while then ;" feed verdict
   -> outcome-invalid ir-why-unbalanced 1 21 }T
T{ start s" : f if ;" feed verdict -> outcome-invalid ir-why-unbalanced 1 8 }T
T{ start s" : f begin repeat ;" feed verdict -> outcome-invalid ir-why-unbalanced 1 11 }T
T{ start s" : f dup while ;" feed verdict -> outcome-invalid ir-why-unbalanced 1 9 }T
T{ start s" : f begin while then ;" feed verdict
   -> outcome-invalid ir-why-unbalanced 1 17 }T
T{ start s" : f : g ;" feed verdict -> outcome-invalid ir-why-nested 1 5 }T
T{ start s" : f dup" feed verdict -> outcome-invalid ir-why-unclosed 1 0 }T
T{ start s" :" feed verdict -> outcome-invalid ir-why-unclosed 1 0 }T
T{ start s" 1 constant" feed verdict -> outcome-invalid ir-why-unclosed 1 0 }T
T{ start s" : f ( dup" feed verdict -> outcome-unsupported ir-why-comment 1 5 }T
T{ start s" : f f ;" feed verdict -> outcome-unsupported ir-why-recursive 1 5 }T
T{ start s" : f ; : f ;" feed verdict -> outcome-unsupported ir-why-redefined 1 9 }T
T{ start s" : dup ;" feed verdict -> outcome-unsupported ir-why-redefined 1 3 }T
T{ start s" : abcdefghijklmnopqrstuvwxyz0123456 ;" feed verdict
   -> outcome-unsupported ir-why-long-name 1 3 }T
T{ start s" constant x" feed verdict -> outcome-invalid ir-why-no-value 1 1 }T
T{ start s" 1 constant dup" feed verdict -> outcome-unsupported ir-why-redefined 1 12 }T

\ Only the first diagnostic counts, and its line is the last one written.
T{ start s" : f foo bar" feed s" if" feed verdict
   -> outcome-unsupported ir-why-unknown 1 5 }T
T{ written s" unsupported @1:5: not a known word or 32-bit decimal: foo" compare
   -> 0 }T

\ No source token is ever executed: these would end or break the test.
T{ start s" : f bye ;" feed verdict -> outcome-unsupported ir-why-unknown 1 5 }T
T{ start s" bye" feed verdict -> outcome-unsupported ir-why-unknown 1 1 }T
T{ start s" 0 0 ! 1 throw" feed verdict -> outcome-unsupported ir-why-not-ir 1 5 }T

\ Capacities: nesting, definitions, kept tokens, line length.
: open-ifs ( n -- ) 0 ?do s" if" feed loop ;
: close-ifs ( n -- ) 0 ?do s" then" feed loop ;
T{ start s" : f" feed 8 open-ifs 8 close-ifs s" ;" feed verdict
   -> outcome-ok ir-why-none 18 0 }T
T{ start s" : f" feed 9 open-ifs verdict -> outcome-full ir-why-capacity 10 1 }T
\ ": wN ;" for definition number N.
char ; constant semicolon-char
: def-line ( n -- c-addr u )
  0 <# semicolon-char hold bl hold #s [char] w hold bl hold [char] : hold #> ;
: define-words ( n -- ) 0 ?do i def-line feed loop ;
T{ start 32 define-words verdict -> outcome-ok ir-why-none 32 0 }T
T{ start 33 define-words verdict -> outcome-full ir-why-capacity 33 3 }T
T{ start s" 1 2 3 4 5 6 7 8 constant x" feed verdict -> outcome-ok ir-why-none 1 0 }T
T{ start s" 1 2 3 4 5 6 7 8 9 constant x" feed verdict
   -> outcome-full ir-why-capacity 1 17 }T
create long-text 200 chars allot  long-text 200 bl fill
T{ start long-text 127 feed verdict -> outcome-ok ir-why-none 1 0 }T
T{ start long-text 128 feed verdict -> outcome-invalid ir-why-unreadable 1 0 }T
T{ start long-text 200 feed verdict -> outcome-invalid ir-why-unreadable 1 0 }T
T{ ' keep-last s" tests/program/no-such-file.fs" lf-ir-read-file lf-ir-reason
   -> outcome-invalid ir-why-unreadable }T
T{ written s" invalid @0:0: file not readable or line too long" compare -> 0 }T

\ The deepest indentation the reader writes fits its space string.
: deepest ( -- c-addr u ) s"                   prim dup @10:1" ;
T{ start s" : f" feed 8 open-ifs s" dup" feed written deepest compare -> 0 }T

bye

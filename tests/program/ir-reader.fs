\ Tests of the program IR reader (src/program/ir-reader.fs): the golden IR
\ of the six example words, every diagnostic with its location, the
\ capacities, ASCII case folding, refused characters, names and numbers,
\ independence from the caller's BASE, STATE and search order, that no
\ source token is ever executed, and a reader stopped until it starts in
\ every context. Gforth itself also loads every source the reader accepts
\ here, and must neither throw nor keep values; files with every kind of
\ line end are tested by ir_reader_files.py. Run from the repository
\ root, like every test file.
include ../support/tester.fs

\ Gforth loading a file the reader accepted, with the host's own words,
\ before the two below replace them; the path is relative to the current
\ directory, as for the reader.
2variable host-path
: host-file ( -- ) host-path 2@ r/o open-file throw include-file ;

\ Files opened and closed, counted to show that the reader closes a file
\ even when its output word throws. The reader, compiled after these two
\ words, calls them instead of the host's (Gforth's redefinition warnings
\ are turned off around them).
variable opened
variable closed
[defined] warnings [if] warnings @ false warnings ! [then]
: open-file ( c-addr u fam -- fileid ior ) open-file dup 0= if 1 opened +! then ;
: close-file ( fileid -- ior ) 1 closed +! close-file ;
[defined] warnings [if] warnings ! [then]
: open-files ( -- n ) opened @ closed @ - ;
require ../../src/program/ir-reader.fs

\ Before lf-ir-start the reader is stopped: a fed line is not read, and
\ finishing gives invalid.
T{ s" : f 1 ;" lf-ir-feed lf-ir-finish lf-ir-reason lf-ir-where
   -> outcome-invalid ir-why-stopped 0 0 }T

\ No word of the host's search order reads as a literal the reader
\ accepts: Gforth would find such a word before it read the number, as
\ the reader finds a definition of the file first (Gforth 1.0 runs its
\ name recognizer first, 0.7.3 its dictionary search). Gforth 0.7.3 lacks
\ TRAVERSE-WORDLIST; there a word list is a chain of names from
\ WORDLIST-ID, each name's first cell pointing to the one before.
[undefined] traverse-wordlist [if]
: traverse-wordlist ( xt wid -- )
  wordlist-id @ begin dup while 2dup swap execute 0= if 2drop exit then @ repeat 2drop ;
[then]
variable host-names        \ names seen
variable literal-names     \ names that read as a literal
: literal-name? ( nt -- true )
  1 host-names +! name>string ir-literal? if drop 1 literal-names +! then true ;
: scan-order ( -- ) get-order 0 ?do ['] literal-name? swap traverse-wordlist loop ;
T{ scan-order literal-names @ host-names @ 3000 > -> 0 true }T

\ The host loads every source the reader accepts. The lines fed since the
\ last start are kept; once the reader accepts them, Gforth evaluates them
\ one by one, with BASE ten, into a new word list searched before
\ FORTH-WORDLIST, so that they shadow nothing here; a file is loaded the
\ same way with INCLUDED. Loading must not throw (Gforth would stop the
\ file there) and must leave the data stack as deep as it was (Gforth
\ would keep the values). host-words is the last such word list.
48 constant source-capacity      \ lines fed in one test
128 constant source-chars
create source-text source-capacity source-chars * chars allot
create source-lengths source-capacity cells allot
variable source-lines
variable host-words
: forget-source ( -- ) 0 source-lines ! ;
: source-slot ( i -- c-addr ) source-chars * chars source-text + ;
: source-length ( i -- addr ) cells source-lengths + ;
: source-line ( i -- c-addr u ) dup source-slot swap source-length @ ;
: remember-line ( c-addr u -- )
  source-lines @ dup source-capacity < 0= abort" too many lines fed"
  >r source-chars min dup r@ source-length ! r> source-slot swap chars move
  1 source-lines +! ;
: host-lines ( -- ) source-lines @ 0 ?do i source-line evaluate loop ;
\ A new word list, searched first and current.
: host-scope ( -- )
  wordlist dup host-words ! dup set-current forth-wordlist swap 2 set-order ;
\ Run xt: its THROW code and how many cells it left (0 after a THROW).
: host-try ( xt -- code delta ) depth >r catch depth r> - ;
[defined] warnings [if]
: quietly ( xt -- code delta ) warnings @ >r false warnings ! host-try r> warnings ! ;
[else]
: quietly ( xt -- code delta ) host-try ;
[then]
\ Drop the n cells a load left below its code.
: drop-left ( x1 .. xn code n -- code n ) 2>r 2r@ nip 0 max 0 ?do drop loop 2r> ;
\ Back to interpretation, should a load stop inside a definition.
: stop-compiling ( -- ) postpone [ ;
\ Load with xt; then restore BASE, the search order and the compilation
\ word list.
: host-load ( xt -- code delta )
  >r get-order r> get-current >r base @ >r decimal host-scope
  quietly drop-left stop-compiling r> base ! r> set-current 2>r set-order 2r> ;
\ An accepted source the host refused: say why, and give no outcome.
999 constant host-refused
: host-refusal ( outcome code delta -- host-refused )
  ." host load: throw " swap . ." cells left " . cr drop host-refused ;
: host-accepts ( outcome xt -- outcome' )
  host-load 2dup or if host-refusal else 2drop then ;
: host-checked ( outcome xt -- outcome' ) over ok? if host-accepts else drop then ;
\ A word that the last source the host loaded defines.
: host-find ( c-addr u -- xt ) host-words @ search-wordlist 0= abort" not in the source" ;

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
\ The source c-addr u against its golden IR c-addr2 u2; the host loads it.
: read-golden ( c-addr u c-addr2 u2 -- outcome mismatches )
  golden 2dup host-path 2! ['] golden-check -rot lf-ir-read-file
  ['] host-file host-checked golden-end ;

T{ s" src/program/clamp.fs" s" tests/program/ir/clamp.ir" read-golden -> outcome-ok 0 }T
T{ s" src/program/examples.fs" s" tests/program/ir/examples.ir" read-golden
   -> outcome-ok 0 }T
T{ s" tests/program/ir/all-primitives.fs" s" tests/program/ir/all-primitives.ir"
   read-golden -> outcome-ok 0 }T
T{ lf-ir-reason open-files -> ir-why-none 0 }T

\ Lines fed one at a time; the last emitted line is kept for inspection.
create last-text 128 chars allot
variable last-length
: keep-last ( c-addr u -- ) 127 min dup last-length ! last-text swap chars move ;
: written ( -- c-addr u ) last-text last-length @ ;
: start-reader ( xt c-addr u -- ) forget-source lf-ir-start ;
: start ( -- ) ['] keep-last s" t.fs" start-reader ;
: feed ( c-addr u -- ) 2dup remember-line lf-ir-feed ;
\ The outcome, the reason and where it stopped; the host loads what the
\ reader accepted.
: verdict ( -- outcome reason line column )
  lf-ir-finish ['] host-lines host-checked lf-ir-reason lf-ir-where ;

\ Or every emitted line, each followed by "|", to compare whole outputs.
2048 constant transcript-chars
create transcript transcript-chars chars allot
variable transcript#
: transcribe-text ( c-addr u -- )
  dup transcript# @ + transcript-chars > abort" transcript full"
  transcript transcript# @ chars + swap dup transcript# +! chars move ;
: transcribe ( c-addr u -- ) transcribe-text s" |" transcribe-text ;
: transcript-text ( -- c-addr u ) transcript transcript# @ ;
: start-transcript ( -- ) 0 transcript# ! ['] transcribe s" t.fs" start-reader ;
: transcribed? ( c-addr u -- flag ) transcript-text compare 0= ;
: contains? ( c-addr u c-addr2 u2 -- flag ) search nip nip ;
\ A second transcript kept for comparison.
create reference transcript-chars chars allot
variable reference#
: keep-reference ( -- ) transcript-text dup reference# ! reference swap chars move ;
: as-reference? ( -- flag ) reference reference# @ transcribed? ;

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
T{ start s" : f 1 >r r@ r> 2drop ;" feed verdict -> outcome-ok ir-why-none 1 0 }T
T{ start s" 1 dup + constant two" feed verdict -> outcome-ok ir-why-none 1 0 }T
T{ start verdict -> outcome-ok ir-why-none 0 0 }T

\ Each diagnostic, with the line and column of the token that caused it.
T{ start s" : f   foo ;" feed verdict -> outcome-unsupported ir-why-unknown 1 7 }T
T{ written s" unsupported @1:7: not a known word or 32-bit decimal: foo" compare
   -> 0 }T
T{ start s" : f 2147483648 ;" feed verdict -> outcome-unsupported ir-why-unknown 1 5 }T
T{ start s" : f 2147483647 -2147483647 $10 ;" feed verdict
   -> outcome-unsupported ir-why-unknown 1 28 }T
T{ start s" : f begin dup until ;" feed verdict
   -> outcome-unsupported ir-why-not-ir 1 15 }T
T{ start s" : f 10 0 do loop ;" feed verdict -> outcome-unsupported ir-why-not-ir 1 10 }T
T{ start s" dup" feed verdict -> outcome-unsupported ir-why-borrowed 1 1 }T
T{ start s" 1 dup" feed verdict -> outcome-unsupported ir-why-left-over 1 0 }T
T{ start s" 1" feed s" : f ;" feed verdict
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
T{ start s" : f begin dup while then ;" feed verdict
   -> outcome-invalid ir-why-unbalanced 1 21 }T
T{ start s" : f if ;" feed verdict -> outcome-invalid ir-why-unbalanced 1 8 }T
T{ start s" : f begin repeat ;" feed verdict -> outcome-invalid ir-why-unbalanced 1 11 }T
T{ start s" : f dup while ;" feed verdict -> outcome-invalid ir-why-unbalanced 1 9 }T
T{ start s" : f begin while then ;" feed verdict
   -> outcome-invalid ir-why-unbalanced 1 17 }T
T{ start s" : f begin dup while else repeat ;" feed verdict
   -> outcome-invalid ir-why-unbalanced 1 21 }T
T{ start s" : f : g ;" feed verdict -> outcome-invalid ir-why-nested 1 5 }T
T{ start s" : f dup" feed verdict -> outcome-invalid ir-why-unclosed 1 0 }T
T{ start s" : f ( dup" feed verdict -> outcome-unsupported ir-why-comment 1 5 }T
T{ start s" : f f ;" feed verdict -> outcome-unsupported ir-why-recursive 1 5 }T
T{ start s" : f ; : f ;" feed verdict -> outcome-unsupported ir-why-redefined 1 9 }T
T{ start s" : dup ;" feed verdict -> outcome-unsupported ir-why-redefined 1 3 }T
T{ start s" : abcdefghijklmnopqrstuvwxyz0123456 ;" feed verdict
   -> outcome-unsupported ir-why-long-name 1 3 }T
T{ start s" constant x" feed verdict -> outcome-unsupported ir-why-no-value 1 1 }T
T{ start s" 1 constant dup" feed verdict -> outcome-unsupported ir-why-redefined 1 12 }T

\ The name after : or CONSTANT must be on the same line, as Gforth needs.
T{ start s" :" feed verdict -> outcome-invalid ir-why-no-name 1 1 }T
T{ written s" invalid @1:1: a name must follow on the same line" compare -> 0 }T
T{ start s" :" feed s" f 1 ;" feed verdict -> outcome-invalid ir-why-no-name 1 1 }T
T{ start s" 1 constant" feed s" x" feed verdict -> outcome-invalid ir-why-no-name 1 3 }T

\ The return-stack words only inside definitions, where the IR models them.
T{ start s" 1 >r r> constant x" feed verdict -> outcome-unsupported ir-why-outside 1 3 }T
T{ start s" 1 r@ constant x" feed verdict -> outcome-unsupported ir-why-outside 1 3 }T

\ The tokens before CONSTANT leave exactly one value and take none from
\ outside the file; Gforth would take or leave the others silently.
T{ start s" 1 2 constant x" feed verdict -> outcome-unsupported ir-why-one-value 1 5 }T
T{ start s" 1 drop constant x" feed verdict -> outcome-unsupported ir-why-one-value 1 8 }T
T{ start s" + constant x" feed verdict -> outcome-unsupported ir-why-borrowed 1 1 }T
T{ start s" 1 2drop constant x" feed verdict -> outcome-unsupported ir-why-borrowed 1 3 }T
T{ start s" 3 constant k k 2dup + constant x" feed verdict
   -> outcome-unsupported ir-why-borrowed 1 16 }T

\ Every data-stack primitive but / and MOD once before CONSTANT, each line
\ leaving one value only if each primitive takes and gives the cells it
\ should.
: effect-lines ( -- )
  s" 1 1 swap over nip tuck 2drop constant c1" feed
  s" 1 1 1 rot 2dup 2drop + + constant c2" feed
  s" 1 1 - 1 * constant c3  1 negate abs 1+ 1- constant c4" feed
  s" 1 1 = 1 <> 0= 0<> constant c5  1 1 < 1 > 0< 0> constant c6" feed
  s" 1 1 and 1 or 1 xor invert constant c7  1 1 rshift 1 max 1 min constant c8" feed
  s" true false 2drop false dup drop constant c9" feed ;
T{ start effect-lines verdict -> outcome-ok ir-why-none 6 0 }T

\ No division before CONSTANT: Gforth divides while it loads the file, and
\ a division by zero, or of the smallest cell by -1, stops the load there
\ (THROW -10 or -11 on both hosts), whereas the IR divides only when the
\ constant is called. Inside a definition, Gforth divides only when the
\ word runs, which the host load below confirms.
T{ start s" 1 0 / constant x" feed verdict -> outcome-unsupported ir-why-dividing 1 5 }T
T{ written s" unsupported @1:5: a division outside a definition: /" compare -> 0 }T
T{ start s" 1 0 mod constant x" feed verdict
   -> outcome-unsupported ir-why-dividing 1 5 }T
T{ start s" 7 2 / constant x" feed verdict -> outcome-unsupported ir-why-dividing 1 5 }T
T{ start s" 3 constant k k 1 MOD constant x" feed verdict
   -> outcome-unsupported ir-why-dividing 1 18 }T
T{ start s" : f 1 0 / 1 0 mod ;" feed verdict -> outcome-ok ir-why-none 1 0 }T
\ The other primitives cannot stop the load: shifts by any count and
\ wrapping arithmetic give some value on both hosts, and the counting
\ above keeps the stack from underflowing. Where the IR leaves such a
\ value unmodeled, a call of the constant fails in the model, so nothing
\ about it can be proved.
T{ start s" 1 64 rshift constant a  1 -1 rshift constant b" feed
   s" 2147483647 dup * dup * negate abs 1+ constant c" feed verdict
   -> outcome-ok ir-why-none 2 0 }T

\ One WHILE per loop: Forth-2012 allows more, IR 0.1 does not.
T{ start s" : f begin dup while 1- while repeat then ;" feed verdict
   -> outcome-unsupported ir-why-two-whiles 1 24 }T
T{ start s" : f begin while while repeat ;" feed verdict
   -> outcome-unsupported ir-why-two-whiles 1 17 }T
T{ start s" : f begin begin while repeat while repeat ;" feed verdict
   -> outcome-ok ir-why-none 1 0 }T

\ Only the first diagnostic counts, and its line is the last one written.
T{ start s" : f foo bar" feed s" if" feed verdict
   -> outcome-unsupported ir-why-unknown 1 5 }T
T{ written s" unsupported @1:5: not a known word or 32-bit decimal: foo" compare
   -> 0 }T

\ Names are found with A-Z folded to a-z, as Gforth finds them, and written
\ in lower case. The clamp spelled in lower, upper and mixed case gives
\ byte-identical IR.
: clamp-lower ( -- )
  s" : lf-clamp ( value lower upper -- result true | false )" feed
  s"   2dup > if 2drop drop false exit then" feed
  s"   >r max r> min true ;" feed ;
: clamp-upper ( -- )
  s" : LF-CLAMP ( VALUE LOWER UPPER -- RESULT TRUE | FALSE )" feed
  s"   2DUP > IF 2DROP DROP FALSE EXIT THEN" feed
  s"   >R MAX R> MIN TRUE ;" feed ;
: clamp-mixed ( -- )
  s" : Lf-Clamp ( Value lower UPPER -- result True | false )" feed
  s"   2Dup > If 2drop DROP False Exit Then" feed
  s"   >r Max R> mIN tRUE ;" feed ;
T{ start-transcript clamp-lower verdict -> outcome-ok ir-why-none 3 0 }T
keep-reference
T{ start-transcript clamp-upper verdict as-reference?
   -> outcome-ok ir-why-none 3 0 true }T
T{ start-transcript clamp-mixed verdict as-reference?
   -> outcome-ok ir-why-none 3 0 true }T
T{ reference reference# @ s" |word lf-clamp @1:1|  prim 2dup @2:3|" contains? -> true }T
T{ start-transcript s" : f DUP ;" feed verdict -> outcome-ok ir-why-none 1 0 }T
T{ s" lf-ir 0.1|source t.fs|word f @1:1|  prim dup @1:5|end @1:9|" transcribed? -> true }T
T{ start-transcript s" : Foo 1 ; 2 CONSTANT Two : g FOO two TWO ;" feed verdict
   -> outcome-ok ir-why-none 1 0 }T
T{ transcript-text s" |word foo @1:1|" contains? -> true }T
T{ transcript-text s" |constant two @1:22|  lit 2 @1:11|end @1:22|" contains? -> true }T
T{ transcript-text s" |  call foo @1:30|  call two @1:34|  call two @1:38|" contains?
   -> true }T

\ A definition whose folded name is already known is refused, wherever
\ the clash is: with a primitive, a control word, an earlier word or
\ constant. These are the reviewer's three examples and more.
T{ start s" : True 0 ;" feed verdict -> outcome-unsupported ir-why-redefined 1 3 }T
T{ written s" unsupported @1:3: name already defined: True" compare -> 0 }T
T{ start s" : Dup drop ; : f dup ;" feed verdict
   -> outcome-unsupported ir-why-redefined 1 3 }T
T{ start s" : foo 1 ; : FOO 2 ; : g foo ;" feed verdict
   -> outcome-unsupported ir-why-redefined 1 13 }T
T{ start s" : IF ;" feed verdict -> outcome-unsupported ir-why-redefined 1 3 }T
T{ start s" 1 constant DUP" feed verdict -> outcome-unsupported ir-why-redefined 1 12 }T
T{ start s" 1 constant k 2 constant K" feed verdict
   -> outcome-unsupported ir-why-redefined 1 25 }T
T{ start s" : k ; 1 constant K" feed verdict
   -> outcome-unsupported ir-why-redefined 1 18 }T
T{ start s" 1 constant k : K ;" feed verdict
   -> outcome-unsupported ir-why-redefined 1 16 }T
T{ start s" : f ; : g ; : F ;" feed verdict
   -> outcome-unsupported ir-why-redefined 1 15 }T
T{ start s" : f F ;" feed verdict -> outcome-unsupported ir-why-recursive 1 5 }T
\ The reviewer's evil clamp: a word True that Gforth would call from the
\ clamp's TRUE. The reader stops at its definition and writes no clamp.
T{ start-transcript s" : True 0 ;" feed clamp-lower verdict
   -> outcome-unsupported ir-why-redefined 1 3 }T
T{ s" lf-ir 0.1|source t.fs|unsupported @1:3: name already defined: True|" transcribed?
   -> true }T
\ A host word outside the reader's vocabulary may be defined: the file's
\ IR is unaffected, but Gforth uses the new DEPTH or . in anything compiled
\ after the file, which must therefore be loaded last (PROGRAM_IR.md; the
\ receipts' trusted-reader assumption). Here it went into a word list of
\ its own, so the host-load check that follows is unaffected.
T{ start s" : depth 0 ;  : . drop ;  : lf-one 1 ;" feed verdict
   -> outcome-ok ir-why-none 1 0 }T

\ Every character must be printable ASCII, a space or a tab: NUL, CR, DEL
\ and bytes of 128 or more are refused anywhere on a line, comments too,
\ and the diagnostic never contains them.
create odd-text 64 chars allot
: odd-line ( c-addr u -- c-addr' u ) tuck odd-text swap chars move odd-text swap ;
: poke ( c-addr u char i -- c-addr u ) chars 2over drop + c! ;
T{ start s" : f?dup ;" odd-line 0 3 poke feed verdict
   -> outcome-unsupported ir-why-character 1 4 }T
T{ written s" unsupported @1:4: a character outside printable ASCII" compare -> 0 }T
T{ start s" : f ? dup ;" odd-line 0 4 poke feed verdict
   -> outcome-unsupported ir-why-character 1 5 }T
T{ start s" : f dup ;?" odd-line 13 9 poke feed verdict
   -> outcome-unsupported ir-why-character 1 10 }T
T{ start s" : f 1 \ x?2 ;" odd-line 13 9 poke feed verdict
   -> outcome-unsupported ir-why-character 1 10 }T
T{ start s" : f?dup ;" odd-line 127 3 poke feed verdict
   -> outcome-unsupported ir-why-character 1 4 }T
T{ start s" : caf? ;" odd-line 233 5 poke feed verdict
   -> outcome-unsupported ir-why-character 1 6 }T
T{ start s" : f ( ? ) ;" odd-line 200 6 poke feed verdict
   -> outcome-unsupported ir-why-character 1 7 }T
T{ start s" \ ?" odd-line 255 2 poke feed verdict
   -> outcome-unsupported ir-why-character 1 3 }T
\ Tabs separate tokens, as spaces do.
T{ start s" :?f?dup?;" odd-line 9 1 poke 9 3 poke 9 7 poke feed verdict
   -> outcome-ok ir-why-none 1 0 }T
T{ written s" end @1:9" compare -> 0 }T

\ Literals: at most ten digits, so a long one cannot wrap to a small value.
T{ start-transcript s" : f 0000000007 -0000000007 ;" feed verdict
   -> outcome-ok ir-why-none 1 0 }T
T{ transcript-text s" |  lit 7 @1:5|  lit -7 @1:16|end @1:28|" contains? -> true }T
T{ start s" : f 00000000007 ;" feed verdict -> outcome-unsupported ir-why-unknown 1 5 }T
T{ start s" : f 9999999999 ;" feed verdict -> outcome-unsupported ir-why-unknown 1 5 }T
T{ start s" : f 18446744073709551621 ;" feed verdict
   -> outcome-unsupported ir-why-unknown 1 5 }T
T{ start s" : f 340282366920938463463374607431768211461 ;" feed verdict
   -> outcome-unsupported ir-why-unknown 1 5 }T
T{ start s" : f -340282366920938463463374607431768211457 ;" feed verdict
   -> outcome-unsupported ir-why-unknown 1 5 }T
T{ start-transcript s" : f -0 ;" feed verdict -> outcome-ok ir-why-none 1 0 }T
T{ transcript-text s" |  lit 0 @1:5|" contains? s" f" host-find execute -> true 0 }T

\ Every other number syntax of Gforth is refused: prefixes, characters,
\ doubles, floats, a plus sign, a doubled minus, C's hexadecimal, and the
\ smallest 32-bit cell, whose magnitude is beyond the limit.
create probe-text 64 chars allot
variable probe#
: probe+ ( c-addr u -- ) probe-text probe# @ chars + swap dup probe# +! chars move ;
\ Whether ": f token ;" is refused as unknown at the token.
: number-refused? ( c-addr u -- flag )
  0 probe# ! s" : f " probe+ probe+ s"  ;" probe+ start probe-text probe# @ feed
  verdict 5 = swap 1 = and swap ir-why-unknown = and swap outcome-unsupported = and ;
T{ s" #10" number-refused? s" $ff" number-refused? s" %101" number-refused?
   s" &10" number-refused? -> true true true true }T
T{ s" 'a'" number-refused? s" 1." number-refused? s" 1.5" number-refused?
   s" 1e" number-refused? s" 1e0" number-refused? -> true true true true true }T
T{ s" +5" number-refused? s" --5" number-refused? s" 0x10" number-refused?
   s" 0b1" number-refused? s" -2147483648" number-refused? -> true true true true true }T

\ Names that read as numbers. Gforth finds a name before it reads a number
\ (1.0 runs its name recognizer first, 0.7.3 its dictionary search), and
\ so does the reader: a token the file defined is a call, any other a
\ literal. The host's own run of each word agrees with the IR.
T{ start-transcript s" : 5 7 ;" feed s" : g 5 05 ;" feed verdict
   -> outcome-ok ir-why-none 2 0 }T
T{ transcript-text s" |word g @2:1|  call 5 @2:5|  lit 5 @2:7|" contains? -> true }T
T{ s" g" host-find execute -> 7 5 }T
T{ start-transcript s" 9 constant -0  : g -0 0 ;" feed verdict
   -> outcome-ok ir-why-none 1 0 }T
T{ transcript-text s" |  call -0 @1:20|  lit 0 @1:23|" contains? -> true }T
T{ s" g" host-find execute -> 9 0 }T
\ Names in Gforth's other number and recognizer syntaxes are names too.
T{ start-transcript s" : 1e 1 ;  : $10 2 ;  : 'a' 3 ;  : ->x 4 ;  : forth:dup 5 ;" feed
   s" : g 1e $10 'a' ->x forth:dup ;" feed verdict -> outcome-ok ir-why-none 2 0 }T
T{ transcript-text s" |  call 1e @2:5|  call $10 @2:8|  call 'a' @2:12|" contains?
   -> true }T
T{ s" g" host-find execute -> 1 2 3 4 5 }T

\ The output is decimal whatever BASE is, and BASE is left as it was.
hex
T{ start-transcript s" : f 16 255 ;" feed verdict base @ -> 0 0 1 0 10 }T
decimal
T{ s" lf-ir 0.1|source t.fs|word f @1:1|  lit 16 @1:5|  lit 255 @1:8|end @1:12|"
   transcribed? -> true }T

\ No source token is ever executed: these would end or break the test.
T{ start s" : f bye ;" feed verdict -> outcome-unsupported ir-why-unknown 1 5 }T
T{ start s" bye" feed verdict -> outcome-unsupported ir-why-unknown 1 1 }T
T{ start s" 0 0 ! 1 throw" feed verdict -> outcome-unsupported ir-why-not-ir 1 5 }T
\ Not even while a definition is being compiled: an IMMEDIATE word that
\ feeds a line runs with STATE nonzero, where an EVALUATEd line would run
\ the source's immediate words.
: feed-while-compiling ( -- ) start s" [ 1 throw ]" feed ; immediate
: compiled ( -- ) feed-while-compiling ;
T{ verdict -> outcome-unsupported ir-why-unknown 1 1 }T
\ Nor does the search order matter.
wordlist constant no-words
: feed-without-words ( -- )
  get-order no-words 1 set-order start s" : f dup ;" feed set-order ;
T{ feed-without-words verdict -> outcome-ok ir-why-none 1 0 }T

\ A file is closed even when the output word throws; the exception passes on.
variable lines-left
: refuse-third ( c-addr u -- ) 2drop -1 lines-left +! lines-left @ 0= if 7 throw then ;
: read-refusing ( -- code )
  3 lines-left ! ['] refuse-third s" src/program/clamp.fs" ['] lf-ir-read-file catch
  >r 2drop drop r> ;
T{ open-files read-refusing open-files -> 0 7 0 }T

\ Capacities: nesting, definitions, kept tokens, line length, path length.
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
T{ start s" 1 dup dup dup + + + negate constant x" feed verdict
   -> outcome-ok ir-why-none 1 0 }T
T{ start s" 1 dup dup dup + + + negate abs constant x" feed verdict
   -> outcome-full ir-why-capacity 1 28 }T
T{ start s" 1 2 3 4 5 6 7 8 9 constant x" feed verdict
   -> outcome-full ir-why-capacity 1 17 }T
create long-text 200 chars allot  long-text 200 bl fill
T{ start long-text 127 feed verdict -> outcome-ok ir-why-none 1 0 }T
T{ start long-text 128 feed verdict -> outcome-invalid ir-why-unreadable 1 0 }T
T{ start long-text 200 feed verdict -> outcome-invalid ir-why-unreadable 1 0 }T
T{ ' keep-last s" tests/program/no-such-file.fs" lf-ir-read-file lf-ir-reason
   -> outcome-invalid ir-why-unreadable }T
T{ written s" invalid @0:0: file not readable or line too long" compare -> 0 }T
create long-path 100 chars allot  long-path 100 char a fill
T{ ' keep-last long-path 89 start-reader verdict -> outcome-ok ir-why-none 0 0 }T
T{ ' keep-last long-path 90 lf-ir-read-file lf-ir-reason lf-ir-where open-files
   -> outcome-full ir-why-capacity 0 0 0 }T
T{ written 36 min s" full @0:0: reader capacity exceeded:" compare -> 0 }T

\ The deepest indentation the reader writes fits its space string.
: deepest ( -- c-addr u ) s"                   prim dup @10:1" ;
T{ start s" : f" feed 8 open-ifs s" dup" feed written deepest compare -> 0 }T

\ Each context has its own reader record, stopped until lf-ir-start; a read
\ in another context leaves the main context's read where it was. Last,
\ because making a context ends declarations.
T{ start s" : f 1 ;" feed -> }T
context-new throw constant other
other context-use
T{ lf-ir-reader lf-context @ - 0 context-bytes within -> true }T
T{ s" : g ;" lf-ir-feed lf-ir-finish lf-ir-reason -> outcome-invalid ir-why-stopped }T
T{ start s" : g 2 ;" feed verdict -> outcome-ok ir-why-none 1 0 }T
context-main context-use
T{ lf-ir-finish lf-ir-reason lf-ir-where -> outcome-ok ir-why-none 1 0 }T
T{ other context-free -> 0 }T

bye

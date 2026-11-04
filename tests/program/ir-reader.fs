\ Tests of the program IR reader (src/program/ir-reader.fs): the golden IR
\ of the six example words, every diagnostic with its location, the
\ capacities, ASCII case folding, refused characters, names and numbers,
\ independence from the caller's BASE, STATE and search order, that no
\ source token is ever executed, a busy reader refusing every reader
\ word, an output word that throws, uses the reader, changes the stack
\ depth, returns in another context or reuses a transient path, read
\ errors, lines refused unread, exceptions that stop a read, the end of a
\ read, and a reader stopped until it starts in every context. Gforth
\ itself also loads every source the reader accepts here, and must
\ neither throw nor keep values; files with every kind of line end are
\ tested by ir_reader_files.py. Run from the repository root, like every
\ test file.
include ../support/tester.fs

\ Gforth loading a file the reader accepted, with the host's own words,
\ before the two below replace them; the path is relative to the current
\ directory, as for the reader.
2variable host-path
: host-file ( -- ) host-path 2@ r/o open-file throw include-file ;

\ Files opened and closed, counted to show that the reader closes a file
\ even when its output word throws, and the reads of the file opened last.
\ A read after the 64th of one file fails, as a read error would, so that
\ a file that never ends cannot hang these tests. Once interrupt-next is
\ set, the next read or number conversion throws -28, as Ctrl-C would;
\ once interrupt-open is set, the next OPEN-FILE; once interrupt-catch is
\ set, the next CATCH, before it sets up its handler, as Ctrl-C arriving
\ just then would; once interrupt-false is set, the next FALSE, which is
\ how the reader makes itself idle. The reader, compiled after these six
\ words, calls them instead of the host's (Gforth's redefinition warnings
\ are turned off around them).
variable opened
variable closed
variable reads
64 constant reads-max
variable interrupt-next
variable interrupt-open
variable interrupt-catch
variable interrupt-false
: interrupting ( addr -- ) dup @ if false swap ! -28 throw then drop ;
[defined] warnings [if] warnings @ false warnings ! [then]
: open-file ( c-addr u fam -- fileid ior )
  interrupt-open interrupting open-file dup 0= if 1 opened +! 0 reads ! then ;
: close-file ( fileid -- ior ) 1 closed +! close-file ;
: read-file ( c-addr u fileid -- u2 ior )
  interrupt-next interrupting
  1 reads +! reads @ reads-max > if drop 2drop 0 -1 else read-file then ;
: >number ( ud c-addr u -- ud' c-addr' u' ) interrupt-next interrupting >number ;
: catch ( i*x xt -- j*x code ) interrupt-catch interrupting catch ;
: false ( -- 0 ) interrupt-false interrupting 0 ;
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
T{ start s" ;" feed verdict -> outcome-unsupported ir-why-outside 1 1 }T
T{ start s" exit" feed verdict -> outcome-unsupported ir-why-outside 1 1 }T
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
\ Both ends of the range fold: A and Z, as Gforth folds them.
T{ start-transcript s" : Zap 1 ; : Az ZAP zap ;" feed verdict
   -> outcome-ok ir-why-none 1 0 }T
T{ transcript-text s" |word zap @1:1|" contains? -> true }T
T{ transcript-text s" |word az @1:11|  call zap @1:16|  call zap @1:20|" contains?
   -> true }T
T{ start s" : z ; : Z ;" feed verdict -> outcome-unsupported ir-why-redefined 1 9 }T

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

\ When the output word throws, the exception passes on, a file being read
\ is closed, and the read stops as invalid, from the header on.
variable lines-left
: refuse-third ( c-addr u -- ) 2drop -1 lines-left +! lines-left @ 0= if 7 throw then ;
: boom ( c-addr u -- ) 2drop 99 throw ;
\ Drop the three cells CATCH restored below the code thrown.
: thrown ( x1 x2 x3 code -- code ) >r 2drop drop r> ;
\ The code the output word xt threw while clamp.fs was read, or while a
\ read started; were nothing thrown, the outcome (none when starting) and 0.
: read-catching ( xt -- code )
  s" src/program/clamp.fs" ['] lf-ir-read-file catch dup if thrown then ;
: start-catching ( xt -- code ) s" t.fs" ['] lf-ir-start catch dup if thrown then ;
T{ 3 lines-left ! open-files ' refuse-third read-catching open-files -> 0 7 0 }T
T{ lf-ir-finish lf-ir-reason -> outcome-invalid ir-why-output }T
T{ ' boom read-catching lf-ir-finish lf-ir-reason open-files
   -> 99 outcome-invalid ir-why-output 0 }T
T{ ' boom start-catching s" : f ;" lf-ir-feed lf-ir-finish lf-ir-reason
   -> 99 outcome-invalid ir-why-output }T

\ While a reader word runs, and so while its output word runs, the reader
\ of its context is busy, and lf-ir-reason says so.
variable seen
: note-reason ( c-addr u -- ) 2drop lf-ir-reason seen ! ;
T{ ' note-reason s" t.fs" start-reader seen @ lf-ir-finish lf-ir-reason
   -> ir-why-busy outcome-ok ir-why-none }T
\ The output word must not use the reader. Given its first "end", each
\ word below feeds a line, finishes, starts a read or reads a file, keeps
\ the code that throws, and returns. Each call is refused (THROW -2) and
\ changes nothing: the read goes on with the line it was reading, and
\ fails as invalid ("output word failed") at once. Unrefused, the fed
\ line overwrote the ; that the diagnostic quotes, and a start erased the
\ read; so every transcript must equal the first.
variable used
variable refusal     \ the code thrown by the reader word called at the first "end"
\ Transcribe the line c-addr u; true the first time it contains c-addr2 u2.
: at-first ( c-addr u c-addr2 u2 -- flag )
  2over transcribe search nip nip used @ 0= and dup if true used ! then ;
: at-first-end ( c-addr u -- flag ) s" end" at-first ;
: feed-catching ( c-addr u -- code ) ['] lf-ir-feed catch dup if nip nip then ;
: feed-at-end ( c-addr u -- )
  at-first-end if s" 1 1 1 1 1 ;" feed-catching refusal ! then ;
: finish-at-end ( c-addr u -- )
  at-first-end if ['] lf-ir-finish catch dup 0= if nip then refusal ! then ;
: start-at-end ( c-addr u -- ) at-first-end if ['] 2drop start-catching refusal ! then ;
: read-at-end ( c-addr u -- )
  at-first-end if ['] 2drop read-catching dup 0= if nip then refusal ! then ;
: read-using ( xt -- outcome reason line column )
  0 transcript# ! false used ! 0 refusal ! s" t.fs" start-reader
  s" : f 7 ;  : g f f + ;" feed verdict ;
: transcript-tail ( n -- c-addr u ) transcript-text rot /string ;
T{ ' feed-at-end read-using refusal @ -> outcome-invalid ir-why-output 1 7 -2 }T
T{ transcript-text 47 min s" lf-ir 0.1|source t.fs|word f @1:1|  lit 7 @1:5|" compare
   47 transcript-tail s" end @1:7|invalid @1:7: output word failed: ;|" compare -> 0 0 }T
keep-reference
T{ ' finish-at-end read-using refusal @ as-reference?
   -> outcome-invalid ir-why-output 1 7 -2 true }T
T{ ' start-at-end read-using refusal @ as-reference?
   -> outcome-invalid ir-why-output 1 7 -2 true }T
T{ ' read-at-end read-using refusal @ as-reference? open-files
   -> outcome-invalid ir-why-output 1 7 -2 true 0 }T
\ The reviewer's case: at its first "word" line, the output word starts a
\ read whose output word would leave a cell, catches the code thrown and
\ returns. The start is refused, so the other output word never runs, and
\ the read fails. Before the refusal, the read ended ok, its IR giving f
\ the value of NEGATE alone where Gforth gives -5.
: read-f ( xt -- outcome reason line column )
  0 transcript# ! false used ! 0 refusal ! s" t.fs" start-reader
  s" : f 5" feed s" negate ;" feed verdict ;
variable nested-lines
: leave-once ( c-addr u -- ) \ but leaves a cell the first time
  2drop 1 nested-lines +! nested-lines @ 1 = if 0 then ;
: nest-at-word ( c-addr u -- )
  s" word" at-first if 0 nested-lines ! ['] leave-once start-catching refusal ! then ;
T{ ' nest-at-word read-f refusal @ nested-lines @
   -> outcome-invalid ir-why-output 1 3 -2 0 }T
T{ s" lf-ir 0.1|source t.fs|word f @1:1|invalid @1:3: output word failed: f|" transcribed?
   -> true }T
\ Uncaught, the refusal passes on through the reader, the read fails, and
\ the reader is no longer busy.
: start-at-word ( c-addr u -- ) s" word" at-first if ['] 2drop s" u.fs" lf-ir-start then ;
T{ 0 transcript# ! false used ! ' start-at-word s" t.fs" start-reader
   s" : f 5" feed-catching lf-ir-finish lf-ir-reason
   -> -2 outcome-invalid ir-why-output }T
\ The count of calls is a second guard: were the busy check bypassed, here
\ by an output word that clears the flag itself (writing into the
\ reader's record, which is not otherwise detected), the start it makes
\ would still fail the read, which that start erased (so its location
\ is 0:0). Unchecked, the read ended ok with f as NEGATE alone.
: bypass-at-word ( c-addr u -- )
  s" word" at-first if false ir-busy ! ['] 2drop s" u.fs" lf-ir-start then ;
T{ ' bypass-at-word read-f -> outcome-invalid ir-why-output 0 0 }T
\ The output word must take its two cells and leave none. One that leaves
\ a cell, or takes one more, fails the read and makes the reader abort
\ (THROW -2) when it returns.
: leave-cell ( c-addr u -- x ) 2drop 0 ;
: take-cell ( x c-addr u -- ) 2drop drop ;
T{ ' leave-cell start-catching lf-ir-reason lf-ir-finish lf-ir-reason
   -> -2 ir-why-output outcome-invalid ir-why-output }T
T{ ' take-cell start-catching lf-ir-reason lf-ir-finish lf-ir-reason
   -> -2 ir-why-output outcome-invalid ir-why-output }T

\ An exception that stops a reader word, such as THROW -28 from Ctrl-C
\ during a blocked OPEN-FILE or READ-FILE, stops the read as invalid too,
\ and passes on: here at the opening of a file, at its first read, after
\ which it is closed, and at the first number of a fed line; nothing is
\ left open, and finishing would otherwise give ok.
T{ true interrupt-open ! ' 2drop read-catching open-files lf-ir-finish lf-ir-reason
   -> -28 0 outcome-invalid ir-why-interrupted }T
T{ true interrupt-next ! ' 2drop read-catching open-files lf-ir-finish lf-ir-reason
   -> -28 0 outcome-invalid ir-why-interrupted }T
T{ start true interrupt-next ! s" 1 constant k" feed-catching lf-ir-finish lf-ir-reason
   -> -28 outcome-invalid ir-why-interrupted }T
\ So does one that comes after the work of a reader word has returned but
\ before the reader is made idle: the outcome the work gave is lost, and
\ the reader is idle again, not busy. Here the read was ok, and the work
\ of lf-ir-finish runs no FALSE, so the first one is the reader's going idle.
T{ start s" : f 1 ;" feed true interrupt-false ! ' lf-ir-finish catch
   lf-ir-finish lf-ir-reason -> -28 outcome-invalid ir-why-interrupted }T

\ lf-ir-finish ends a read: finishing again gives the same outcome, and a
\ line fed afterwards stops the reader and is not written about.
T{ start s" : f 1 ;" feed lf-ir-finish lf-ir-finish -> outcome-ok outcome-ok }T
T{ s" : g f ;" lf-ir-feed lf-ir-finish lf-ir-reason lf-ir-where
   -> outcome-invalid ir-why-finished 1 0 }T
T{ written s" end @1:7" compare -> 0 }T
T{ ' keep-last s" src/program/clamp.fs" lf-ir-read-file s" : g ;" lf-ir-feed
   lf-ir-finish lf-ir-reason -> outcome-ok outcome-invalid ir-why-finished }T
T{ start s" : f" feed lf-ir-finish s" ;" lf-ir-feed lf-ir-finish lf-ir-reason
   -> outcome-invalid outcome-invalid ir-why-unclosed }T

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
\ A fed line's length is unsigned: -1 is too long, so the line is refused
\ unread, neither copied nor read past its end. The line and block
\ buffers keep what lf-ir-start left there, not the blanks of long-text.
T{ start s" : f ;" drop -1 lf-ir-feed verdict -> outcome-invalid ir-why-unreadable 1 0 }T
T{ start long-text -1 lf-ir-feed ir-text c@ bl = ir-block c@ -> false 0 }T
\ So even a bad address only fails the read: here address 0, from which
\ the copy of a line cut to the buffer's size once threw -9.
T{ start 0 -1 ' lf-ir-feed catch verdict -> 0 outcome-invalid ir-why-unreadable 1 0 }T
T{ start 0 128 ' lf-ir-feed catch verdict -> 0 outcome-invalid ir-why-unreadable 1 0 }T
\ So does ir-scan, which lf-ir-feed calls: a line of length -1 is
\ refused, not read until a character that stops it (NUL here).
T{ start s" : f ;?" odd-line 0 5 poke drop -1 ir-scan verdict
   -> outcome-invalid ir-why-unreadable 1 0 }T
T{ ' keep-last s" tests/program/no-such-file.fs" lf-ir-read-file lf-ir-reason
   -> outcome-invalid ir-why-unreadable }T
T{ written s" invalid @0:0: file not readable or line too long" compare -> 0 }T
\ A directory opens but cannot be read: the read error stops the reader,
\ and the directory is closed.
T{ -1 reads ! ' keep-last s" src" lf-ir-read-file lf-ir-reason lf-ir-where
   reads @ open-files -> outcome-invalid ir-why-unreadable 0 0 1 0 }T
T{ written s" invalid @0:0: file not readable or line too long" compare -> 0 }T
\ A line is refused as soon as it is too long even without a CR, so a file
\ without LF is not read to its end: /dev/zero is refused after two blocks.
T{ ' keep-last s" /dev/zero" lf-ir-read-file lf-ir-reason lf-ir-where reads @ open-files
   -> outcome-invalid ir-why-unreadable 1 0 2 0 }T
create long-path 100 chars allot  long-path 100 char a fill
T{ ' keep-last long-path 89 start-reader verdict -> outcome-ok ir-why-none 0 0 }T
T{ ' keep-last long-path 90 lf-ir-read-file lf-ir-reason lf-ir-where open-files
   -> outcome-full ir-why-capacity 0 0 0 }T
T{ written 36 min s" full @0:0: reader capacity exceeded:" compare -> 0 }T

\ A path may be in a transient buffer too: the reader copies it before
\ its output word first runs, so the header line and OPEN-FILE use the
\ path given even when the output word reuses the pictured-numeric buffer
\ that holds it. Uncopied, the header named t.f0 and the file read was
\ src/program/clamp.f0.
: hold-text ( c-addr u -- ) begin dup while 1- 2dup chars + c@ hold repeat 2drop ;
: pictured ( c-addr u -- c-addr' u ) 0 0 2swap <# hold-text #> ;
: renumber ( -- ) 0 0 <# #s #> 2drop ;   \ writes 0 at the buffer's end
: transcribe-renumbering ( c-addr u -- ) transcribe renumber ;
: golden-renumbering ( c-addr u -- ) golden-check renumber ;
T{ 0 transcript# ! ' transcribe-renumbering s" t.fs" pictured start-reader
   s" : f ;" feed verdict -> outcome-ok ir-why-none 1 0 }T
T{ transcript-text 22 min s" lf-ir 0.1|source t.fs|" compare -> 0 }T
T{ s" tests/program/ir/clamp.ir" golden
   ' golden-renumbering s" src/program/clamp.fs" pictured lf-ir-read-file
   golden-end open-files -> outcome-ok 0 0 }T

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
\ The refusal is for the busy context only: an output word may use the
\ reader of another context, and return in its own.
variable elsewhere   \ the outcome of the read made in the other context
: read-elsewhere ( -- )
  other context-use ['] 2drop s" h.fs" lf-ir-start s" : h 3 ;" lf-ir-feed
  lf-ir-finish elsewhere ! context-main context-use ;
: use-elsewhere ( c-addr u -- ) s" word" at-first if read-elsewhere then ;
T{ ' use-elsewhere read-f elsewhere @ -> outcome-ok ir-why-none 2 0 outcome-ok }T
\ But not a way back in: the other read's output word switches to the main
\ context, feeds a line there (refused, since the main reader is busy),
\ catches the refusal and switches back. That counts as a call of the
\ main reader, so the main read fails; the other read is untouched.
\ Without the feed, both end ok.
variable hop-feed   \ whether the other read's output word feeds the main reader
variable hopped     \ whether it has run
: hop-back ( c-addr u -- )
  2drop hopped @ if exit then true hopped ! context-main context-use
  hop-feed @ if s" : z ;" feed-catching refusal ! then other context-use ;
: hop-there ( -- outcome )
  other context-use ['] hop-back s" o.fs" lf-ir-start s" : q 1 ;" lf-ir-feed
  lf-ir-finish context-main context-use ;
: hop-at-word ( c-addr u -- ) s" word" at-first if hop-there elsewhere ! then ;
: hop ( flag -- outcome reason line column outcome' code )
  hop-feed ! false hopped ! 0 elsewhere ! ['] hop-at-word read-f elsewhere @ refusal @ ;
T{ true hop -> outcome-invalid ir-why-output 1 3 outcome-ok -2 }T
T{ false hop -> outcome-ok ir-why-none 2 0 outcome-ok 0 }T

\ Words that check that a reader left busy for good says so and refuses
\ every reader word (THROW -2), and that make and free a context for it.
: refused-start ( -- code ) ['] 2drop s" t.fs" ['] lf-ir-start catch dup if thrown then ;
: refused-read ( -- code ) ['] 2drop read-catching dup 0= if nip then ;
: refused-feed ( -- code ) s" : g ;" feed-catching ;
: refused-finish ( -- code ) ['] lf-ir-finish catch dup 0= if nip then ;
: refusals ( -- reason code code code code )
  lf-ir-reason refused-start refused-read refused-feed refused-finish ;
: in? ( context -- flag ) lf-context @ = ;
: fresh ( -- context ) context-new throw dup context-use ;
\ Leave the context, which must not be the main one, and free it.
: discard ( context -- ior ) context-main context-use context-free ;

\ An exception that arrives just after a reader word has made the reader
\ busy, before its handler is set up (here from the CATCH that sets it
\ up), leaves the reader busy for good. Before the busy flag, such an
\ exception lost the fed line, and the read could still end ok; a finish
\ cut short so let a later line be read.
: armed ( i*x xt -- j*x ) true interrupt-catch ! execute ;
fresh constant cut-feed
T{ start s" : f 1 ;" feed s" : g 2 ;" ' lf-ir-feed ' armed catch nip nip nip -> -28 }T
T{ refusals -> ir-why-busy -2 -2 -2 -2 }T
T{ cut-feed discard -> 0 }T
fresh constant cut-finish
T{ start s" : f 1 ;" feed ' lf-ir-finish ' armed catch nip -> -28 }T
T{ refusals -> ir-why-busy -2 -2 -2 -2 }T
T{ cut-finish discard -> 0 }T
\ So does one that arrives after the work threw, before the handler has
\ made the reader idle: here the output word throws, and the next FALSE
\ is the handler's going idle. Its exception passes on in place of the
\ output word's.
: throw-armed ( c-addr u -- ) 2drop true interrupt-false ! 99 throw ;
fresh constant cut-handler
T{ ' throw-armed start-catching -> -28 }T
T{ refusals -> ir-why-busy -2 -2 -2 -2 }T
T{ cut-handler discard -> 0 }T

\ The output word must return in the context it was called in. One that
\ returns in another makes the reader abort (THROW -2) there, touching no
\ record: the reader it left stays busy for good, and a file being read
\ is closed. Here a read of clamp.fs in a new context is left at its
\ first "word" line for the main context, whose read stays as it was.
variable switch-to   \ the context to switch to at the next "lit" or "word" line, or 0
: switch-line? ( c-addr u -- flag ) 2dup s" lit" contains? -rot s" word" contains? or ;
: switching ( c-addr u -- )
  switch-line? switch-to @ and ?dup if 0 switch-to ! context-use then ;
T{ start s" : f 1 ;" feed -> }T
fresh constant left
T{ context-main switch-to ! ' switching read-catching context-main in? open-files
   -> -2 true 0 }T
T{ lf-ir-finish lf-ir-reason lf-ir-where -> outcome-ok ir-why-none 1 0 }T
left context-use
T{ refusals -> ir-why-busy -2 -2 -2 -2 }T
T{ left discard -> 0 }T
\ The same with fed lines, from the main context to the other and back.
\ Unchecked, the second feed below resumed the first read, whose IR then
\ gave c the value 5, where Gforth gives -5. Both readers stay busy, the
\ main context's too, so this comes last.
T{ ' switching s" a.fs" lf-ir-start  other context-use  ' switching s" b.fs" lf-ir-start
   context-main context-use  other switch-to !  s" 5 negate constant c" feed-catching
   other in? lf-ir-reason -> -2 true ir-why-none }T
T{ context-main switch-to !  s" 7 constant d" feed-catching context-main in? -> -2 true }T
T{ refusals -> ir-why-busy -2 -2 -2 -2 }T
other context-use
T{ refusals -> ir-why-busy -2 -2 -2 -2 }T
T{ other discard -> 0 }T

bye

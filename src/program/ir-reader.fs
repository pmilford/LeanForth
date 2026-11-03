\ Reader from restricted Forth source to the program IR, version 0.1
\ (docs/programming/PROGRAM_IR.md). Untrusted: it translates text and
\ proves nothing; a program receipt names it as a trusted assumption.
\
\ It reads colon definitions and constants built only from the primitives,
\ control words and decimal literals of IR 0.1 and writes the IR's text
\ form one line at a time through an output word ( c-addr u -- ), with the
\ line and column of every source token. Anything else stops it with one
\ diagnostic line and an outcome: unsupported for Forth outside IR 0.1,
\ invalid for malformed Forth or an unreadable file, full when one of
\ the fixed capacities below is reached. Lines written before a diagnostic
\ are incomplete and must not be used. If the output word throws, the
\ exception passes to the caller (a file being read is closed first).
\
\ It must accept less than Gforth (1.0 and 0.7.3) does, never more, and
\ give what it accepts Gforth's meaning:
\ - It splits each line into tokens itself, at spaces and tabs, as both
\   hosts do. A line holding any other character outside printable ASCII
\   (NUL, CR, DEL, any byte of 128 or more) is refused, even in a comment,
\   so no character whose treatment differs between hosts reaches a token.
\   Nothing reaches the host's interpreter, so no source token is ever
\   executed, whatever the caller's STATE, BASE or search order.
\ - Names are looked up with ASCII case folded (A-Z equals a-z), as
\   Gforth looks them up, and written in lower case. A definition whose
\   folded name is already known is refused, so a source cannot shadow a
\   word under another spelling.
\ - Literals are plain decimal: at most ten digits, at most 2147483647 in
\   size. The tokens before CONSTANT must leave exactly one value.
\ Gforth must load the source with BASE ten, its default search order and
\ its own standard words, as it does when it starts; nothing here can
\ check that.
\
\ Requires ../lib/lib.fs. State: lf-ir-vocabulary and lf-ir-reasons, two
\ tables filled while this file loads and never changed afterwards, and
\ lf-ir-reader, the one reader record, reached only through the accessors
\ below. One read at a time; not re-entrant.

decimal
require ../lib/lib.fs

\ Classes of the words the reader knows.
0 constant ir-prim        \ an IR primitive on the data stack: dup, +, max, ...
1 constant ir-rstack      \ an IR primitive on the return stack: >r r> r@
2 constant ir-colon
3 constant ir-semicolon
4 constant ir-if
5 constant ir-else
6 constant ir-then
7 constant ir-begin
8 constant ir-while
9 constant ir-repeat
10 constant ir-exit
11 constant ir-constant
12 constant ir-paren       \ a ( comment )
13 constant ir-backslash   \ a \ comment
14 constant ir-decimal
15 constant ir-other       \ standard Forth that IR 0.1 does not model
16 constant ir-classes

\ Named text. The vocabulary, the diagnostic messages and the definitions
\ read so far are stores of these records.
40 constant ir-text-chars
begin-structure /ir-entry
  field: ir-entry-class     \ a class above; for a definition ir-colon or ir-constant
  field: ir-entry-effect    \ a primitive's data-stack effect, see ir-data
  field: ir-entry-length    \ characters used in ir-entry-name
  ir-text-chars chars +field ir-entry-name
end-structure
/ir-entry aligned constant /ir-slot

: ir-entry-text ( entry -- c-addr u ) dup ir-entry-name swap ir-entry-length @ ;
: ir-entry= ( c-addr u entry -- flag ) ir-entry-text compare 0= ;
: ir-text! ( c-addr u entry -- )
  over ir-text-chars > abort" lf-ir: text too long"
  2dup ir-entry-length ! ir-entry-name swap chars move ;

\ Whether record index of a store holds the text c-addr u. It takes four
\ items because ir-find's DO loop keeps its index and limit on the return
\ stack, where the text and the store cannot also be parked.
: ir-same? ( c-addr u store index -- c-addr u store flag )
  over store-slot 2over rot ir-entry= ;
\ The index of the first record of a store whose text is c-addr u.
: ir-find ( c-addr u store -- index true | false )
  dup store-count @ 0 ?do i ir-same? if drop 2drop i true unloop exit then loop
  drop 2drop false ;
\ The same, but keeping the text when it is not there.
: ir-look ( c-addr u store -- index true | c-addr u false )
  >r 2dup r> ir-find dup if 2swap 2drop then ;

\ The vocabulary, spelled in lower case.
80 /ir-slot 0 store: lf-ir-vocabulary
: ir-slot ( store -- entry ) store-new-slot 0= abort" lf-ir: table full" drop ;
: ir-add ( class c-addr u -- entry )
  lf-ir-vocabulary ir-slot dup >r ir-text! r> tuck ir-entry-class ! ;
: ir-word ( class c-addr u -- ) ir-add drop ;
\ A primitive and its data-stack effect, written as two digits: the cells
\ it takes, then the cells it gives (2dup takes 2 and gives 4: 24).
: ir-effect! ( effect entry -- ) ir-entry-effect ! ;
: ir-data ( effect c-addr u -- ) ir-prim -rot ir-add ir-effect! ;
: ir-return ( effect c-addr u -- ) ir-rstack -rot ir-add ir-effect! ;
: ir-entry ( index -- entry ) lf-ir-vocabulary store-slot ;
: ir-class ( index -- class ) ir-entry ir-entry-class @ ;
: ir-word-text ( index -- c-addr u ) ir-entry ir-entry-text ;
: ir-effect ( index -- taken given ) ir-entry ir-entry-effect @ 10 /mod swap ;

ir-colon s" :" ir-word        ir-semicolon s" ;" ir-word    ir-if s" if" ir-word
ir-else s" else" ir-word      ir-then s" then" ir-word      ir-begin s" begin" ir-word
ir-while s" while" ir-word    ir-repeat s" repeat" ir-word  ir-exit s" exit" ir-word
ir-constant s" constant" ir-word  ir-paren s" (" ir-word    ir-backslash s" \" ir-word
ir-decimal s" decimal" ir-word
\ The 38 primitives of IR 0.1, in the order of Prim in program-ir.lean.
12 s" dup" ir-data     10 s" drop" ir-data    22 s" swap" ir-data
23 s" over" ir-data    21 s" nip" ir-data     23 s" tuck" ir-data
33 s" rot" ir-data     24 s" 2dup" ir-data    20 s" 2drop" ir-data
10 s" >r" ir-return    01 s" r>" ir-return    01 s" r@" ir-return
21 s" +" ir-data       21 s" -" ir-data       21 s" *" ir-data
21 s" /" ir-data       21 s" mod" ir-data     11 s" negate" ir-data
11 s" abs" ir-data     11 s" 1+" ir-data      11 s" 1-" ir-data
21 s" =" ir-data       21 s" <>" ir-data      21 s" <" ir-data
21 s" >" ir-data       11 s" 0=" ir-data      11 s" 0<>" ir-data
11 s" 0<" ir-data      11 s" 0>" ir-data      21 s" and" ir-data
21 s" or" ir-data      21 s" xor" ir-data     11 s" invert" ir-data
21 s" rshift" ir-data  21 s" max" ir-data     21 s" min" ir-data
01 s" true" ir-data    01 s" false" ir-data
\ Common standard words outside IR 0.1, named so the diagnostic says so.
ir-other s" until" ir-word  ir-other s" again" ir-word  ir-other s" do" ir-word
ir-other s" ?do" ir-word    ir-other s" loop" ir-word   ir-other s" +loop" ir-word
ir-other s" leave" ir-word  ir-other s" unloop" ir-word ir-other s" i" ir-word
ir-other s" j" ir-word      ir-other s" case" ir-word   ir-other s" of" ir-word
ir-other s" endof" ir-word  ir-other s" endcase" ir-word ir-other s" recurse" ir-word
ir-other s" variable" ir-word ir-other s" create" ir-word ir-other s" value" ir-word
ir-other s" @" ir-word      ir-other s" !" ir-word      ir-other s" lshift" ir-word

\ Diagnostic reasons; each message is stored at its reason's index.
24 /ir-slot 0 store: lf-ir-reasons
: ir-reason ( c-addr u -- ) lf-ir-reasons ir-slot ir-text! ;
0 constant ir-why-none       s" no diagnostic" ir-reason
1 constant ir-why-unknown    s" not a known word or 32-bit decimal" ir-reason
2 constant ir-why-not-ir     s" a Forth word outside IR 0.1" ir-reason
3 constant ir-why-outside    s" not allowed outside a definition" ir-reason
4 constant ir-why-inside     s" not allowed inside a definition" ir-reason
5 constant ir-why-unbalanced s" unbalanced control structure" ir-reason
6 constant ir-why-nested     s" a definition inside a definition" ir-reason
7 constant ir-why-unclosed   s" definition not closed" ir-reason
8 constant ir-why-comment    s" comment not closed on its line" ir-reason
9 constant ir-why-recursive  s" recursive call" ir-reason
10 constant ir-why-redefined s" name already defined" ir-reason
11 constant ir-why-long-name s" name longer than 31 characters" ir-reason
12 constant ir-why-no-value  s" constant without a value" ir-reason
13 constant ir-why-left-over s" values left outside a definition" ir-reason
14 constant ir-why-capacity  s" reader capacity exceeded" ir-reason
15 constant ir-why-unreadable s" file not readable or line too long" ir-reason
16 constant ir-why-character s" a character outside printable ASCII" ir-reason
17 constant ir-why-no-name   s" a name must follow on the same line" ir-reason
18 constant ir-why-two-whiles s" a second WHILE in one loop" ir-reason
19 constant ir-why-one-value s" not exactly one value before CONSTANT" ir-reason
20 constant ir-why-borrowed  s" takes values from outside the file" ir-reason
21 constant ir-reasons
lf-ir-reasons store-count @ ir-reasons <> [if] .( lf-ir: reason table ) abort [then]
: ir-reason-text ( reason -- c-addr u ) lf-ir-reasons store-slot ir-entry-text ;

\ Capacities.
31 constant ir-name-chars       \ longest definition name
32 constant ir-def-capacity     \ definitions per file
8 constant ir-control-capacity  \ open IF and BEGIN structures
8 constant ir-pending-capacity  \ tokens before CONSTANT
96 constant ir-out-chars        \ longest output line
128 constant ir-line-chars      \ source lines must be shorter than this
ir-def-capacity /ir-slot store-size constant /ir-defs

\ A token kept until CONSTANT: a primitive (value: vocabulary index), a
\ literal (value: the number) or a call (value: definition index).
0 constant ir-kept-prim
1 constant ir-kept-lit
2 constant ir-kept-call
begin-structure /ir-token
  field: ir-token-kind
  field: ir-token-value
  field: ir-token-line
  field: ir-token-column
end-structure

\ What the next token is.
0 constant ir-mode-top        \ between definitions
1 constant ir-mode-word       \ the name after :
2 constant ir-mode-body       \ inside a colon definition
3 constant ir-mode-constant   \ the name after CONSTANT
4 constant ir-modes

begin-structure /lf-ir-reader
  field: irr-emit          \ output word ( c-addr u -- ), one line per call
  field: irr-outcome       \ outcome-ok until the first diagnostic
  field: irr-reason        \ why it stopped, or ir-why-none
  field: irr-line          \ number of the current line, from 1
  field: irr-column        \ column of the current token, from 1; 0 at end of file
  field: irr-start         \ the current line's first character
  2 cells +field irr-rest  \ the part of the line not read yet: c-addr u, with 2@ 2!
  field: irr-mode
  field: irr-current       \ definition being compiled, or -1
  field: irr-mark-line     \ where it started
  field: irr-mark-column
  field: irr-depth         \ open control structures
  ir-control-capacity cells +field irr-control
  field: irr-kept#
  field: irr-values        \ cells the kept tokens leave on the data stack
  ir-pending-capacity /ir-token * +field irr-kept
  field: irr-out#
  \ Character buffers are padded to whole cells, so later fields stay aligned.
  ir-out-chars chars aligned +field irr-out
  ir-line-chars chars aligned +field irr-folded   \ the current token in lower case
  /ir-defs +field irr-defs         \ a store of /ir-slot records
  \ A line read from a file, then the two characters READ-LINE may add.
  ir-line-chars 2 + chars +field irr-text
end-structure
create lf-ir-reader /lf-ir-reader allot

\ Accessors: the only words that name lf-ir-reader.
: ir-outcome ( -- addr ) lf-ir-reader irr-outcome ;
: ir-why ( -- addr ) lf-ir-reader irr-reason ;
: ir-line# ( -- addr ) lf-ir-reader irr-line ;
: ir-column ( -- addr ) lf-ir-reader irr-column ;
: ir-start ( -- addr ) lf-ir-reader irr-start ;
: ir-rest ( -- c-addr u ) lf-ir-reader irr-rest 2@ ;
: ir-rest! ( c-addr u -- ) lf-ir-reader irr-rest 2! ;
: ir-mode ( -- addr ) lf-ir-reader irr-mode ;
: ir-current ( -- addr ) lf-ir-reader irr-current ;
: ir-mark ( -- line column )
  lf-ir-reader dup irr-mark-line @ swap irr-mark-column @ ;
: ir-mark! ( line column -- )
  lf-ir-reader tuck irr-mark-column ! irr-mark-line ! ;
: ir-depth ( -- addr ) lf-ir-reader irr-depth ;
: ir-control ( -- addr ) lf-ir-reader irr-control ;
: ir-kept# ( -- addr ) lf-ir-reader irr-kept# ;
: ir-values ( -- addr ) lf-ir-reader irr-values ;
: ir-kept ( i -- token ) /ir-token * lf-ir-reader irr-kept + ;
: ir-out# ( -- addr ) lf-ir-reader irr-out# ;
: ir-out ( -- c-addr ) lf-ir-reader irr-out ;
: ir-folded ( -- c-addr ) lf-ir-reader irr-folded ;
: ir-defs ( -- store ) lf-ir-reader irr-defs ;
: ir-text ( -- c-addr ) lf-ir-reader irr-text ;
: ir-emit ( c-addr u -- ) lf-ir-reader irr-emit @ execute ;
: ir-here ( -- line column ) ir-line# @ ir-column @ ;

\ Stopping. Only the first diagnostic counts; later tokens are skipped.
: ir-ok? ( -- flag ) ir-outcome @ ok? ;
: ir-stop ( outcome reason -- ) ir-ok? if ir-why ! ir-outcome ! else 2drop then ;
: ir-unsupported ( reason -- ) outcome-unsupported swap ir-stop ;
: ir-invalid ( reason -- ) outcome-invalid swap ir-stop ;
: ir-full ( -- ) outcome-full ir-why-capacity ir-stop ;

\ The output line under construction. Text that would not fit stops the
\ reader instead of overrunning the buffer.
: ir-room ( -- u ) ir-out-chars ir-out# @ - ;
: ir-copy ( c-addr u -- ) ir-out ir-out# @ chars + swap dup ir-out# +! chars move ;
: ir-append ( c-addr u -- ) dup ir-room > if 2drop ir-full else ir-copy then ;
: ir-send ( -- ) ir-out ir-out# @ ir-emit 0 ir-out# ! ;
: ir-flush ( -- ) ir-ok? if ir-send else 0 ir-out# ! then ;

\ Pieces of a line. Numbers are written in decimal whatever BASE is.
: ir-decimal-text ( n -- c-addr u )
  base @ >r decimal dup abs 0 <# #s rot sign #> r> base ! ;
: ir-number ( n -- ) ir-decimal-text ir-append ;
: ir-indent ( depth -- ) 1+ 2* s"                     " drop swap ir-append ;
: ir-location ( line column -- )
  s"  @" ir-append swap ir-number s" :" ir-append ir-number ;
: ir-done ( -- ) ir-here ir-location ir-flush ;
: ir-keyword ( c-addr u depth -- ) ir-indent ir-append ir-done ;
: ir-keyword-line ( c-addr u -- ) ir-depth @ ir-keyword ;
: ir-start-line ( c-addr u -- ) ir-depth @ ir-indent ir-append ;
: ir-end ( -- ) s" end" ir-append ir-done ;
: ir-def ( index -- entry ) ir-defs store-slot ;
: ir-def-text ( index -- c-addr u ) ir-def ir-entry-text ;

\ The diagnostic line: "unsupported @line:column: reason: token", or
\ without ": token" (ir-diagnose) for a failure that has no token.
: ir-clipped ( c-addr u -- ) ir-room min ir-copy ;
: ir-report ( c-addr u -- )
  0 ir-out# ! ir-outcome @ outcome-text ir-clipped ir-here ir-location
  s" : " ir-clipped ir-why @ ir-reason-text ir-clipped
  dup if s" : " ir-clipped ir-clipped else 2drop then ir-send ;
: ir-diagnose ( -- ) s" " ir-report ;

\ Characters. Tokens are separated by spaces and tabs; every other
\ character of a line must be printable ASCII, ! to ~.
9 constant ir-tab
: ir-blank? ( char -- flag ) dup bl = swap ir-tab = or ;
: ir-printable? ( char -- flag ) [char] ! [char] ~ 1+ within ;
: ir-plain? ( char -- flag ) dup ir-printable? swap ir-blank? or ;
: ir-inside? ( char -- flag ) ir-blank? 0= ;
: ir-unclosed? ( char -- flag ) [char] ) <> ;
\ c-addr u without its leading characters for which xt ( char -- flag ) holds.
: ir-skip ( c-addr u xt -- c-addr' u' )
  >r begin dup while over c@ r@ execute while 1 /string repeat then r> drop ;

\ Case folding: Gforth finds names ignoring the case of A-Z only.
: ir-upper? ( char -- flag ) [char] A [char] Z 1+ within ;
: ir-lower ( char -- char' ) dup ir-upper? if [char] a [char] A - + then ;
: ir-lower! ( c-addr -- ) dup c@ ir-lower swap c! ;
: ir-lower-all ( c-addr u -- ) chars over + swap ?do i ir-lower! 1 chars +loop ;
\ A copy of a token in lower case, valid until the next token.
: ir-fold ( c-addr u -- c-addr' u )
  ir-folded swap 2dup 2>r chars move 2r> 2dup ir-lower-all ;

\ Literals: a minus sign or none, then one to ten decimal digits, at most
\ 2147483647 in size so that the same source suits 32-bit cells. Ten
\ digits always fit in a double cell, so the conversion cannot wrap.
2147483647 constant ir-literal-max
10 constant ir-digits-max
: ir-negative ( c-addr u -- c-addr' u' flag )
  dup if over c@ [char] - = if 1 /string true exit then then false ;
: ir-convert ( c-addr u -- ud c-addr' u' ) 0 0 2swap base @ >r decimal >number r> base ! ;
: ir-fits? ( u -- u true | false ) dup ir-literal-max u> if drop false else true then ;
: ir-whole? ( c-addr u -- u true | false )
  dup 1 ir-digits-max 1+ within 0= if 2drop false exit then
  ir-convert nip 0= swap 0= and if ir-fits? else drop false then ;
: ir-signed ( u negative -- n ) if negate then ;
: ir-literal? ( c-addr u -- n true | false )
  ir-negative >r ir-whole? if r> ir-signed true else r> drop false then ;

\ Definitions of this file. The text of a name is already folded.
: ir-known? ( c-addr u -- flag )
  lf-ir-vocabulary ir-look if drop true exit then ir-defs ir-find dup if nip then ;
: ir-name? ( c-addr u -- c-addr u flag )
  dup ir-name-chars > if ir-why-long-name ir-unsupported false exit then
  2dup ir-known? if ir-why-redefined ir-unsupported false exit then true ;
: ir-new ( c-addr u kind -- index true | false )
  ir-defs store-new-slot 0= if drop 2drop ir-full false exit then
  >r tuck ir-entry-class ! ir-text! r> true ;
: ir-define ( c-addr u kind -- index true | false )
  >r ir-name? if r> ir-new else 2drop r> drop false then ;
: ir-constant? ( index -- flag ) ir-def ir-entry-class @ ir-constant = ;

\ Open IF and BEGIN structures; a frame is the class of its latest word.
: ir-top ( -- addr ) ir-depth @ 1- cells ir-control + ;
: ir-top? ( frame -- flag ) ir-depth @ 0> if ir-top @ = else drop false then ;
: ir-push ( frame -- )
  ir-depth @ ir-control-capacity < if 1 ir-depth +! ir-top ! else drop ir-full then ;
: ir-unbalanced ( -- ) ir-why-unbalanced ir-invalid ;
: ir-open ( c-addr u frame -- ) >r ir-keyword-line r> ir-push ;
\ ELSE and WHILE turn the frame of their IF or BEGIN into their own and
\ are written one level out, beside it.
: ir-turn? ( from to -- flag ) swap ir-top? if ir-top ! true else drop false then ;
: ir-middle ( c-addr u flag -- )
  if ir-depth @ 1- ir-keyword else 2drop ir-unbalanced then ;
: ir-close ( c-addr u flag -- )
  if -1 ir-depth +! ir-keyword-line else 2drop ir-unbalanced then ;
: ir-if-open? ( -- flag ) ir-if ir-top? ir-else ir-top? or ;
\ Forth-2012 allows more WHILEs in one BEGIN, each closed by a THEN after
\ REPEAT; IR 0.1 has one.
: ir-second-while? ( -- flag ) ir-while ir-top? ;

\ Actions for a vocabulary word inside a definition ( index -- ).
: ir-to-top ( -- ) ir-mode-top ir-mode ! ;
: ir-body-prim ( index -- ) s" prim " ir-start-line ir-word-text ir-append ir-done ;
: ir-body-nested ( index -- ) drop ir-why-nested ir-invalid ;
: ir-body-inside ( index -- ) drop ir-why-inside ir-unsupported ;
: ir-body-end ( index -- )
  drop ir-depth @ if ir-unbalanced exit then ir-end -1 ir-current ! ir-to-top ;
: ir-body-if ( index -- ) drop s" if" ir-if ir-open ;
: ir-body-else ( index -- ) drop s" else" ir-if ir-else ir-turn? ir-middle ;
: ir-body-then ( index -- ) drop s" then" ir-if-open? ir-close ;
: ir-body-begin ( index -- ) drop s" begin" ir-begin ir-open ;
: ir-body-while ( index -- )
  drop ir-second-while? if ir-why-two-whiles ir-unsupported exit then
  s" while" ir-begin ir-while ir-turn? ir-middle ;
: ir-body-repeat ( index -- ) drop s" repeat" ir-while ir-top? ir-close ;
: ir-body-exit ( index -- ) drop s" exit" ir-keyword-line ;
\ Comments: ( skips past the next ) on its line, \ to the end of the line.
: ir-skip-paren ( index -- )
  drop ir-rest ['] ir-unclosed? ir-skip
  dup if 1 /string ir-rest! else 2drop ir-why-comment ir-unsupported then ;
: ir-skip-line ( index -- ) drop ir-rest chars + 0 ir-rest! ;
: ir-not-ir ( index -- ) drop ir-why-not-ir ir-unsupported ;

\ A table of execution tokens must have one for each class or mode.
: ir-sized? ( table entries -- flag ) cells + here = ;

create ir-body-actions  \ indexed by class
  ' ir-body-prim , ' ir-body-prim , ' ir-body-nested , ' ir-body-end ,
  ' ir-body-if , ' ir-body-else , ' ir-body-then , ' ir-body-begin ,
  ' ir-body-while , ' ir-body-repeat , ' ir-body-exit , ' ir-body-inside ,
  ' ir-skip-paren , ' ir-skip-line , ' ir-body-inside , ' ir-not-ir ,
ir-body-actions ir-classes ir-sized? 0= [if] .( lf-ir: body actions ) abort [then]

\ Actions for a vocabulary word outside a definition ( index -- ). Tokens
\ before CONSTANT are kept, and the cells they would leave on Gforth's data
\ stack are counted; a token taking more cells than are there would take
\ values the caller left, which the IR does not model.
: ir-take ( taken given -- )
  over ir-values @ > if 2drop ir-why-borrowed ir-unsupported exit then
  swap - ir-values +! ;
: ir-token-at! ( token -- ) ir-here rot tuck ir-token-column ! ir-token-line ! ;
: ir-keep! ( value kind token -- )
  tuck ir-token-kind ! tuck ir-token-value ! ir-token-at! ;
: ir-keep ( value kind -- )
  ir-kept# @ dup ir-pending-capacity < if ir-kept ir-keep! 1 ir-kept# +! exit then
  drop 2drop ir-full ;
: ir-top-prim ( index -- ) dup ir-effect ir-take ir-kept-prim ir-keep ;
: ir-top-colon ( index -- )
  drop ir-kept# @ if ir-why-left-over ir-unsupported exit then
  ir-here ir-mark! ir-mode-word ir-mode ! ;
: ir-top-control ( index -- ) drop ir-why-outside ir-unsupported ;
: ir-one-value ( -- )
  ir-values @ 1 <> if ir-why-one-value ir-unsupported exit then
  ir-mode-constant ir-mode ! ;
: ir-top-constant ( index -- )
  drop ir-kept# @ if ir-one-value else ir-why-no-value ir-invalid then ;

create ir-top-actions  \ indexed by class; >r r> r@ are not kept
  ' ir-top-prim , ' ir-top-control , ' ir-top-colon , ' ir-top-control ,
  ' ir-top-control , ' ir-top-control , ' ir-top-control , ' ir-top-control ,
  ' ir-top-control , ' ir-top-control , ' ir-top-control , ' ir-top-constant ,
  ' ir-skip-paren , ' ir-skip-line , ' drop , ' ir-not-ir ,
ir-top-actions ir-classes ir-sized? 0= [if] .( lf-ir: top actions ) abort [then]

: ir-act ( index table -- ) over ir-class cells + @ execute ;

\ A token that is not in the vocabulary: a definition, else a literal.
: ir-body-call ( index -- )
  dup ir-current @ = if drop ir-why-recursive ir-unsupported exit then
  s" call " ir-start-line ir-def-text ir-append ir-done ;
: ir-body-lit ( n -- ) s" lit " ir-start-line ir-number ir-done ;
: ir-top-call ( index -- )
  dup ir-constant? 0= if drop ir-why-outside ir-unsupported exit then
  0 1 ir-take ir-kept-call ir-keep ;
: ir-keep-lit ( n -- ) 0 1 ir-take ir-kept-lit ir-keep ;
: ir-literal ( c-addr u xt -- )
  >r ir-literal? if r> execute else r> drop ir-why-unknown ir-unsupported then ;
: ir-body-token ( c-addr u -- )
  lf-ir-vocabulary ir-look if ir-body-actions ir-act exit then
  ir-defs ir-look if ir-body-call exit then ['] ir-body-lit ir-literal ;
: ir-top-token ( c-addr u -- )
  lf-ir-vocabulary ir-look if ir-top-actions ir-act exit then
  ir-defs ir-look if ir-top-call exit then ['] ir-keep-lit ir-literal ;

\ The name after : starts a word; the name after CONSTANT ends a constant,
\ whose kept tokens are then written with their own locations.
: ir-word-name ( c-addr u -- )
  ir-colon ir-define 0= if exit then
  dup ir-current ! s" word " ir-append ir-def-text ir-append ir-mark ir-location ir-flush
  ir-mode-body ir-mode ! ;
: ir-kept-text ( value kind -- )
  case ir-kept-prim of s" prim " ir-append ir-word-text ir-append endof
    ir-kept-lit of s" lit " ir-append ir-number endof
    ir-kept-call of s" call " ir-append ir-def-text ir-append endof
    nip endcase ;
: ir-token-where ( token -- line column ) dup ir-token-line @ swap ir-token-column @ ;
: ir-replay ( token -- )
  0 ir-indent dup ir-token-value @ over ir-token-kind @ ir-kept-text
  ir-token-where ir-location ir-flush ;
: ir-replay-all ( -- )
  ir-kept# @ 0 ?do i ir-kept ir-replay loop 0 ir-kept# ! 0 ir-values ! ;
: ir-constant-name ( c-addr u -- )
  ir-constant ir-define 0= if exit then
  s" constant " ir-append ir-def-text ir-append ir-done ir-replay-all ir-end ir-to-top ;

\ One token, in the current mode, looked up in lower case; the first
\ failure is reported with the token as the source spells it.
create ir-mode-actions  \ indexed by mode, which only the reader sets
  ' ir-top-token , ' ir-word-name , ' ir-body-token , ' ir-constant-name ,
ir-mode-actions ir-modes ir-sized? 0= [if] .( lf-ir: mode actions ) abort [then]
: ir-dispatch ( c-addr u -- ) ir-mode @ cells ir-mode-actions + @ execute ;
: ir-column! ( c-addr -- ) ir-start @ - 1 chars / 1+ ir-column ! ;
: ir-token ( c-addr u -- )
  over ir-column! 2dup 2>r ir-fold ir-dispatch 2r> ir-ok? if 2drop else ir-report then ;

\ The tokens of a line, until one fails: each is the characters up to the
\ next space or tab.
: ir-next-token ( -- c-addr u )
  ir-rest ['] ir-blank? ir-skip 2dup ['] ir-inside? ir-skip 2dup ir-rest! nip - ;
: ir-tokens ( -- ) begin ir-ok? while ir-next-token dup while ir-token repeat 2drop then ;

\ A line: refused when a character is outside printable ASCII; otherwise
\ its tokens, after which : or CONSTANT must have found its name.
: ir-odd ( c-addr -- ) ir-column! ir-why-character ir-unsupported ir-diagnose ;
: ir-plain-line? ( -- flag )
  ir-rest ['] ir-plain? ir-skip if ir-odd false else drop true then ;
: ir-naming? ( -- flag ) ir-mode @ dup ir-mode-word = swap ir-mode-constant = or ;
: ir-end-of-line ( -- )
  ir-ok? ir-naming? and if ir-why-no-name ir-invalid ir-diagnose then ;
: ir-scan-line ( c-addr u -- )
  over ir-start ! ir-rest! ir-plain-line? if ir-tokens ir-end-of-line then ;
: ir-unreadable ( -- ) 0 ir-column ! ir-why-unreadable ir-invalid ir-diagnose ;
\ Count a line and read it, unless the reader has stopped or the line is
\ too long.
: ir-scan ( c-addr u -- )
  ir-ok? 0= if 2drop exit then
  1 ir-line# +! dup ir-line-chars < if ir-scan-line else 2drop ir-unreadable then ;

\ Reading. lf-ir-start resets the record and writes the header; lines then
\ come from a file (lf-ir-read-file) or one at a time (lf-ir-feed), and
\ lf-ir-finish checks the end of the input and gives the outcome.
: ir-reset ( xt -- )
  lf-ir-reader /lf-ir-reader erase lf-ir-reader irr-emit !
  outcome-ok ir-outcome ! ir-why-none ir-why ! -1 ir-current ! ir-to-top ;
: ir-source-header ( c-addr u -- ) s" source " ir-append ir-append ir-flush ;
\ A path too long for its header line stops the reader with a diagnostic.
: ir-header ( c-addr u -- )
  s" lf-ir 0.1" ir-append ir-flush 2dup ir-source-header
  ir-ok? if 2drop else ir-report then ;
: lf-ir-start ( xt c-addr u -- )
  rot ir-reset ir-def-capacity /ir-slot 0 ir-defs store-init 0= abort" lf-ir: store"
  ir-header ;
\ A fed line is copied first, so it may live in a transient buffer such as
\ the pictured-numeric one, which the reader itself uses. A line too long
\ to copy is cut to the buffer's size, which ir-scan then refuses.
: lf-ir-feed ( c-addr u -- )
  ir-line-chars min tuck ir-text swap chars move ir-text swap ir-scan ;
: ir-at-end ( -- )
  ir-mode @ ir-mode-top <> if ir-why-unclosed ir-invalid exit then
  ir-kept# @ if ir-why-left-over ir-unsupported then ;
: ir-end-of-input ( -- ) 0 ir-column ! ir-at-end ir-ok? 0= if ir-diagnose then ;
: lf-ir-finish ( -- outcome ) ir-ok? if ir-end-of-input then ir-outcome @ ;

\ A file, read line by line into the line buffer. A line that fills the
\ buffer is too long; a read error stops the reader. The file is closed
\ even when the output word throws, and the exception is passed on.
: ir-fetch ( fileid -- u true | false )
  >r ir-text ir-line-chars r> read-line
  if 2drop ir-unreadable false else 0= if drop false else true then then ;
: ir-more? ( fileid -- flag ) ir-fetch if ir-text swap ir-scan ir-ok? else false then ;
: ir-read-lines ( fileid -- ) begin dup ir-more? 0= until drop ;
: ir-read-open ( fileid -- )
  dup ['] ir-read-lines catch ?dup if nip swap close-file drop throw then
  close-file drop ;
: ir-read-path ( c-addr u -- )
  r/o open-file if drop ir-unreadable else ir-read-open then ;
: lf-ir-read-file ( xt c-addr u -- outcome )
  2dup 2>r lf-ir-start 2r> ir-ok? if ir-read-path else 2drop then lf-ir-finish ;

\ For tests and callers: why the reader stopped, and where.
: lf-ir-reason ( -- reason ) ir-why @ ;
: lf-ir-where ( -- line column ) ir-here ;

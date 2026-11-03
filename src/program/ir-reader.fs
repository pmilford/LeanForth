\ Reader from restricted Forth source to the program IR, version 0.1
\ (docs/programming/PROGRAM_IR.md). Untrusted: it translates text and
\ proves nothing; a program receipt names it as a trusted assumption.
\
\ It reads colon definitions and constants built only from the primitives,
\ control words and decimal literals of IR 0.1 and writes the IR's text
\ form one line at a time through an output word ( c-addr u -- ), with the
\ line and column of every source token. Anything else stops it with one
\ diagnostic line and an outcome: unsupported for Forth outside IR 0.1,
\ invalid for malformed Forth or an unreadable file, exhausted when one of
\ the fixed capacities below is reached. Lines written before a diagnostic
\ are incomplete and must not be used.
\
\ Tokens are split by the host's own PARSE-NAME: each source line is
\ EVALUATEd behind the word lf-ir-tokens, which parses the rest of the line
\ itself, so no source token is ever executed. Names are compared exactly
\ (case-sensitive) and literals must be plain decimal within 32 bits, so
\ the reader accepts less than Gforth does, never more.
\
\ Requires ../lib/lib.fs. State: lf-ir-vocabulary and lf-ir-reasons, two
\ tables filled while this file loads and never changed afterwards, and
\ lf-ir-reader, the one reader record, reached only through the accessors
\ below. One read at a time; not re-entrant.

decimal
require ../lib/lib.fs

\ Classes of the words the reader knows.
0 constant ir-prim        \ an IR primitive: dup, +, max, ...
1 constant ir-colon
2 constant ir-semicolon
3 constant ir-if
4 constant ir-else
5 constant ir-then
6 constant ir-begin
7 constant ir-while
8 constant ir-repeat
9 constant ir-exit
10 constant ir-constant
11 constant ir-paren       \ a ( comment )
12 constant ir-backslash   \ a \ comment
13 constant ir-decimal
14 constant ir-other       \ standard Forth that IR 0.1 does not model

\ Named text. The vocabulary, the diagnostic messages and the definitions
\ read so far are stores of these records.
40 constant ir-text-chars
begin-structure /ir-entry
  field: ir-entry-class     \ a class above; for a definition ir-colon or ir-constant
  field: ir-entry-length    \ characters used in ir-entry-name
  ir-text-chars chars +field ir-entry-name
end-structure
/ir-entry aligned constant /ir-slot

: ir-entry-text ( entry -- c-addr u ) dup ir-entry-name swap ir-entry-length @ ;
: ir-entry= ( c-addr u entry -- flag ) ir-entry-text compare 0= ;
: ir-text! ( c-addr u entry -- )
  over ir-text-chars > abort" lf-ir: text too long"
  2dup ir-entry-length ! ir-entry-name swap chars move ;

\ The index of the first record of a store whose text is c-addr u.
: ir-same? ( c-addr u store entry -- store flag ) swap >r ir-entry= r> swap ;
: ir-at? ( c-addr u store index -- c-addr u store flag )
  over store-slot 2>r 2dup 2r> ir-same? ;
: ir-find ( c-addr u store -- index true | false )
  dup store-count @ 0 ?do i ir-at? if drop 2drop i true unloop exit then loop
  drop 2drop false ;

\ The vocabulary.
80 /ir-slot 0 store: lf-ir-vocabulary
: ir-slot ( store -- entry ) store-new-slot 0= abort" lf-ir: table full" drop ;
: ir-word ( class c-addr u -- )
  lf-ir-vocabulary ir-slot dup >r ir-text! r> ir-entry-class ! ;
: ir-entry ( index -- entry ) lf-ir-vocabulary store-slot ;
: ir-class ( index -- class ) ir-entry ir-entry-class @ ;
: ir-word-text ( index -- c-addr u ) ir-entry ir-entry-text ;

ir-colon s" :" ir-word        ir-semicolon s" ;" ir-word    ir-if s" if" ir-word
ir-else s" else" ir-word      ir-then s" then" ir-word      ir-begin s" begin" ir-word
ir-while s" while" ir-word    ir-repeat s" repeat" ir-word  ir-exit s" exit" ir-word
ir-constant s" constant" ir-word  ir-paren s" (" ir-word    ir-backslash s" \" ir-word
ir-decimal s" decimal" ir-word
\ The 38 primitives of IR 0.1, in the order of Prim in program-ir.lean.
ir-prim s" dup" ir-word    ir-prim s" drop" ir-word   ir-prim s" swap" ir-word
ir-prim s" over" ir-word   ir-prim s" nip" ir-word    ir-prim s" tuck" ir-word
ir-prim s" rot" ir-word    ir-prim s" 2dup" ir-word   ir-prim s" 2drop" ir-word
ir-prim s" >r" ir-word     ir-prim s" r>" ir-word     ir-prim s" r@" ir-word
ir-prim s" +" ir-word      ir-prim s" -" ir-word      ir-prim s" *" ir-word
ir-prim s" /" ir-word      ir-prim s" mod" ir-word    ir-prim s" negate" ir-word
ir-prim s" abs" ir-word    ir-prim s" 1+" ir-word     ir-prim s" 1-" ir-word
ir-prim s" =" ir-word      ir-prim s" <>" ir-word     ir-prim s" <" ir-word
ir-prim s" >" ir-word      ir-prim s" 0=" ir-word     ir-prim s" 0<>" ir-word
ir-prim s" 0<" ir-word     ir-prim s" 0>" ir-word     ir-prim s" and" ir-word
ir-prim s" or" ir-word     ir-prim s" xor" ir-word    ir-prim s" invert" ir-word
ir-prim s" rshift" ir-word ir-prim s" max" ir-word    ir-prim s" min" ir-word
ir-prim s" true" ir-word   ir-prim s" false" ir-word
\ Common standard words outside IR 0.1, named so the diagnostic says so.
ir-other s" until" ir-word  ir-other s" again" ir-word  ir-other s" do" ir-word
ir-other s" ?do" ir-word    ir-other s" loop" ir-word   ir-other s" +loop" ir-word
ir-other s" leave" ir-word  ir-other s" unloop" ir-word ir-other s" i" ir-word
ir-other s" j" ir-word      ir-other s" case" ir-word   ir-other s" of" ir-word
ir-other s" endof" ir-word  ir-other s" endcase" ir-word ir-other s" recurse" ir-word
ir-other s" variable" ir-word ir-other s" create" ir-word ir-other s" value" ir-word
ir-other s" @" ir-word      ir-other s" !" ir-word      ir-other s" lshift" ir-word

\ Diagnostic reasons; each message is stored at its reason's index.
16 /ir-slot 0 store: lf-ir-reasons
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
lf-ir-reasons store-count @ 16 <> [if] .( lf-ir: reason table ) abort [then]
: ir-reason-text ( reason -- c-addr u ) lf-ir-reasons store-slot ir-entry-text ;

\ Capacities.
31 constant ir-name-chars       \ longest definition name
32 constant ir-def-capacity     \ definitions per file
8 constant ir-control-capacity  \ open IF and BEGIN structures
8 constant ir-pending-capacity  \ tokens before CONSTANT
96 constant ir-out-chars        \ longest output line
128 constant ir-line-chars      \ source lines must be shorter than this
ir-def-capacity /ir-slot store-size constant /ir-defs

\ Every line is EVALUATEd behind this prefix (lf-ir-tokens is defined last).
: ir-prefix ( -- c-addr u ) s" lf-ir-tokens " ;
13 constant ir-prefix-chars
ir-prefix nip ir-prefix-chars <> [if] .( lf-ir: prefix length ) abort [then]

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

begin-structure /lf-ir-reader
  field: reader-emit          \ output word ( c-addr u -- ), one line per call
  field: reader-outcome       \ outcome-ok until the first diagnostic
  field: reader-reason        \ why it stopped, or ir-why-none
  field: reader-line          \ line of the current token, from 1
  field: reader-column        \ column of the current token, from 1; 0 at end of file
  field: reader-mode
  field: reader-current       \ definition being compiled, or -1
  field: reader-mark-line     \ where it started
  field: reader-mark-column
  field: reader-depth         \ open control structures
  ir-control-capacity cells +field reader-control
  field: reader-kept#
  ir-pending-capacity /ir-token * +field reader-kept
  field: reader-out#
  ir-out-chars chars +field reader-out
  /ir-defs +field reader-defs         \ a store of /ir-slot records
  \ The prefix, then the line, then the two characters READ-LINE may add.
  ir-prefix-chars ir-line-chars + 2 + chars +field reader-text
end-structure
create lf-ir-reader /lf-ir-reader allot

\ Accessors: the only words that name lf-ir-reader.
: ir-outcome ( -- addr ) lf-ir-reader reader-outcome ;
: ir-why ( -- addr ) lf-ir-reader reader-reason ;
: ir-line# ( -- addr ) lf-ir-reader reader-line ;
: ir-column ( -- addr ) lf-ir-reader reader-column ;
: ir-mode ( -- addr ) lf-ir-reader reader-mode ;
: ir-current ( -- addr ) lf-ir-reader reader-current ;
: ir-mark ( -- line column )
  lf-ir-reader dup reader-mark-line @ swap reader-mark-column @ ;
: ir-depth ( -- addr ) lf-ir-reader reader-depth ;
: ir-control ( -- addr ) lf-ir-reader reader-control ;
: ir-kept# ( -- addr ) lf-ir-reader reader-kept# ;
: ir-kept ( i -- token ) /ir-token * lf-ir-reader reader-kept + ;
: ir-out# ( -- addr ) lf-ir-reader reader-out# ;
: ir-out ( -- c-addr ) lf-ir-reader reader-out ;
: ir-defs ( -- store ) lf-ir-reader reader-defs ;
: ir-text ( -- c-addr ) lf-ir-reader reader-text ;
: ir-emit ( c-addr u -- ) lf-ir-reader reader-emit @ execute ;
: ir-here ( -- line column ) ir-line# @ ir-column @ ;
: ir-mark! ( line column -- )
  lf-ir-reader tuck reader-mark-column ! reader-mark-line ! ;

\ Stopping. Only the first diagnostic counts; later tokens are skipped.
: ir-ok? ( -- flag ) ir-outcome @ ok? ;
: ir-stop ( outcome reason -- ) ir-ok? if ir-why ! ir-outcome ! else 2drop then ;
: ir-unsupported ( reason -- ) outcome-unsupported swap ir-stop ;
: ir-invalid ( reason -- ) outcome-invalid swap ir-stop ;
: ir-exhausted ( -- ) outcome-exhausted ir-why-capacity ir-stop ;

\ The output line under construction. Text that would not fit stops the
\ reader instead of overrunning the buffer.
: ir-room ( -- u ) ir-out-chars ir-out# @ - ;
: ir-copy ( c-addr u -- ) ir-out ir-out# @ chars + swap dup ir-out# +! chars move ;
: ir-append ( c-addr u -- ) dup ir-room > if 2drop ir-exhausted else ir-copy then ;
: ir-send ( -- ) ir-out ir-out# @ ir-emit 0 ir-out# ! ;
: ir-flush ( -- ) ir-ok? if ir-send else 0 ir-out# ! then ;

\ Pieces of a line.
: ir-number ( n -- ) dup abs 0 <# #s rot sign #> ir-append ;
: ir-indent ( depth -- ) 1+ 2* s"                     " drop swap ir-append ;
: ir-at ( line column -- ) s"  @" ir-append swap ir-number s" :" ir-append ir-number ;
: ir-done ( -- ) ir-here ir-at ir-flush ;
: ir-keyword ( c-addr u depth -- ) ir-indent ir-append ir-done ;
: ir-line ( c-addr u -- ) ir-depth @ ir-keyword ;
: ir-start-line ( c-addr u -- ) ir-depth @ ir-indent ir-append ;
: ir-def-text ( index -- c-addr u ) ir-defs store-slot ir-entry-text ;

\ The diagnostic line: "unsupported @line:column: message: token".
: ir-outcome-text ( outcome -- c-addr u )
  case outcome-unsupported of s" unsupported" endof
    outcome-invalid of s" invalid" endof
    outcome-exhausted of s" exhausted" endof
    s" failed" rot endcase ;
: ir-clipped ( c-addr u -- ) ir-room min ir-copy ;
: ir-report ( c-addr u -- )
  0 ir-out# ! ir-outcome @ ir-outcome-text ir-clipped ir-here ir-at
  s" : " ir-clipped ir-why @ ir-reason-text ir-clipped
  dup if s" : " ir-clipped ir-clipped else 2drop then ir-send ;

\ Literals: plain decimal digits with an optional minus sign, at most
\ 2147483647 in size so that the same source suits 32-bit cells.
2147483647 constant ir-literal-max
: ir-minus? ( c-addr u -- flag ) dup if drop 1 s" -" compare 0= else 2drop false then ;
: ir-convert ( c-addr u -- ud c-addr' u' ) 0 0 2swap base @ >r decimal >number r> base ! ;
: ir-fits? ( u -- u true | false ) dup ir-literal-max u> if drop false else true then ;
: ir-unsigned ( c-addr u -- u true | false )
  dup 0= if 2drop false exit then
  ir-convert nip 0= swap 0= and if ir-fits? else drop false then ;
: ir-literal? ( c-addr u -- n true | false )
  2dup ir-minus? if 1 /string ir-unsigned if negate true else false then exit then
  ir-unsigned ;

\ Definitions of this file.
: ir-known? ( c-addr u -- flag )
  2dup lf-ir-vocabulary ir-find if drop 2drop true exit then
  ir-defs ir-find dup if nip then ;
: ir-name? ( c-addr u -- c-addr u flag )
  dup ir-name-chars > if ir-why-long-name ir-unsupported false exit then
  2dup ir-known? if ir-why-redefined ir-unsupported false exit then true ;
: ir-new ( c-addr u kind -- index true | false )
  ir-defs store-new-slot 0= if drop 2drop ir-exhausted false exit then
  >r tuck ir-entry-class ! ir-text! r> true ;
: ir-define ( c-addr u kind -- index true | false )
  >r ir-name? if r> ir-new else 2drop r> drop false then ;
: ir-constant? ( index -- flag ) ir-defs store-slot ir-entry-class @ ir-constant = ;

\ Open IF and BEGIN structures; a frame is the class of its latest word.
: ir-top ( -- addr ) ir-depth @ 1- cells ir-control + ;
: ir-top? ( frame -- flag ) ir-depth @ 0> if ir-top @ = else drop false then ;
: ir-push ( frame -- )
  ir-depth @ ir-control-capacity < if 1 ir-depth +! ir-top ! else drop ir-exhausted then ;
: ir-unbalanced ( -- ) ir-why-unbalanced ir-invalid ;
: ir-open ( c-addr u frame -- ) >r ir-line r> ir-push ;
\ ELSE and WHILE replace the frame below them and print one level out.
: ir-middle ( c-addr u from to -- )
  swap ir-top? if ir-top ! ir-depth @ 1- ir-keyword else drop 2drop ir-unbalanced then ;
: ir-close ( c-addr u flag -- ) if -1 ir-depth +! ir-line else 2drop ir-unbalanced then ;

\ Actions for a vocabulary word inside a definition ( index -- ).
: ir-body-prim ( index -- ) s" prim " ir-start-line ir-word-text ir-append ir-done ;
: ir-body-nested ( index -- ) drop ir-why-nested ir-invalid ;
: ir-body-inside ( index -- ) drop ir-why-inside ir-unsupported ;
: ir-body-end ( index -- )
  drop ir-depth @ if ir-unbalanced exit then
  s" end" ir-append ir-done -1 ir-current ! ir-mode-top ir-mode ! ;
: ir-body-if ( index -- ) drop s" if" ir-if ir-open ;
: ir-body-else ( index -- ) drop s" else" ir-if ir-else ir-middle ;
: ir-body-then ( index -- ) drop s" then" ir-if ir-top? ir-else ir-top? or ir-close ;
: ir-body-begin ( index -- ) drop s" begin" ir-begin ir-open ;
: ir-body-while ( index -- ) drop s" while" ir-begin ir-while ir-middle ;
: ir-body-repeat ( index -- ) drop s" repeat" ir-while ir-top? ir-close ;
: ir-body-exit ( index -- ) drop s" exit" ir-line ;
: ir-skip-paren ( index -- )
  drop [char] ) parse chars + source chars + u< 0= if ir-why-comment ir-unsupported then ;
: ir-skip-line ( index -- ) drop source nip >in ! ;
: ir-not-ir ( index -- ) drop ir-why-not-ir ir-unsupported ;

create ir-body-actions  \ indexed by class
  ' ir-body-prim , ' ir-body-nested , ' ir-body-end , ' ir-body-if , ' ir-body-else ,
  ' ir-body-then , ' ir-body-begin , ' ir-body-while , ' ir-body-repeat ,
  ' ir-body-exit , ' ir-body-inside , ' ir-skip-paren , ' ir-skip-line ,
  ' ir-body-inside , ' ir-not-ir ,

\ Actions for a vocabulary word outside a definition ( index -- ).
: ir-keep! ( value kind token -- )
  tuck ir-token-kind ! tuck ir-token-value !
  ir-here rot tuck ir-token-column ! ir-token-line ! ;
: ir-keep ( value kind -- )
  ir-kept# @ dup ir-pending-capacity < if ir-kept ir-keep! 1 ir-kept# +! exit then
  drop 2drop ir-exhausted ;
: ir-top-prim ( index -- ) ir-kept-prim ir-keep ;
: ir-top-colon ( index -- )
  drop ir-kept# @ if ir-why-left-over ir-unsupported exit then
  ir-here ir-mark! ir-mode-word ir-mode ! ;
: ir-top-control ( index -- ) drop ir-why-outside ir-unsupported ;
: ir-top-constant ( index -- )
  drop ir-kept# @ if ir-mode-constant ir-mode ! else ir-why-no-value ir-invalid then ;

create ir-top-actions  \ indexed by class
  ' ir-top-prim , ' ir-top-colon , ' ir-top-control , ' ir-top-control ,
  ' ir-top-control , ' ir-top-control , ' ir-top-control , ' ir-top-control ,
  ' ir-top-control , ' ir-top-control , ' ir-top-constant , ' ir-skip-paren ,
  ' ir-skip-line , ' drop , ' ir-not-ir ,

: ir-act ( index table -- ) over ir-class cells + @ execute ;

\ A token that is not in the vocabulary.
: ir-body-call ( index -- )
  dup ir-current @ = if drop ir-why-recursive ir-unsupported exit then
  s" call " ir-start-line ir-def-text ir-append ir-done ;
: ir-body-lit ( n -- ) s" lit " ir-start-line ir-number ir-done ;
: ir-top-call ( index -- )
  dup ir-constant? if ir-kept-call ir-keep else drop ir-why-outside ir-unsupported then ;
: ir-literal ( c-addr u xt -- )
  >r ir-literal? if r> execute else r> drop ir-why-unknown ir-unsupported then ;
: ir-body-token ( c-addr u -- )
  2dup lf-ir-vocabulary ir-find if nip nip ir-body-actions ir-act exit then
  2dup ir-defs ir-find if nip nip ir-body-call exit then ['] ir-body-lit ir-literal ;
: ir-keep-lit ( n -- ) ir-kept-lit ir-keep ;
: ir-top-token ( c-addr u -- )
  2dup lf-ir-vocabulary ir-find if nip nip ir-top-actions ir-act exit then
  2dup ir-defs ir-find if nip nip ir-top-call exit then ['] ir-keep-lit ir-literal ;

\ The name after : starts a word; the name after CONSTANT ends a constant,
\ whose kept tokens are then written with their own locations.
: ir-word-name ( c-addr u -- )
  ir-colon ir-define 0= if exit then
  dup ir-current ! s" word " ir-append ir-def-text ir-append ir-mark ir-at ir-flush
  ir-mode-body ir-mode ! ;
: ir-kept-text ( value kind -- )
  case ir-kept-prim of s" prim " ir-append ir-word-text ir-append endof
    ir-kept-lit of s" lit " ir-append ir-number endof
    ir-kept-call of s" call " ir-append ir-def-text ir-append endof
    nip endcase ;
: ir-replay ( token -- )
  0 ir-indent dup ir-token-value @ over ir-token-kind @ ir-kept-text
  dup ir-token-line @ swap ir-token-column @ ir-at ir-flush ;
: ir-replay-all ( -- ) ir-kept# @ 0 ?do i ir-kept ir-replay loop 0 ir-kept# ! ;
: ir-constant-name ( c-addr u -- )
  ir-constant ir-define 0= if exit then
  s" constant " ir-append ir-def-text ir-append ir-done ir-replay-all
  s" end" ir-append ir-done ir-mode-top ir-mode ! ;

\ One token, in the current mode; the first failure is reported with it.
\ After that, tokens are skipped and the location stays put.
create ir-mode-actions  \ indexed by mode, which only the reader sets
  ' ir-top-token , ' ir-word-name , ' ir-body-token , ' ir-constant-name ,
: ir-dispatch ( c-addr u -- ) ir-mode @ cells ir-mode-actions + @ execute ;
: ir-line-buffer ( -- c-addr ) ir-text ir-prefix-chars chars + ;
: ir-column! ( c-addr -- ) ir-line-buffer - 1 chars / 1+ ir-column ! ;
: ir-token ( c-addr u -- )
  ir-ok? 0= if 2drop exit then over ir-column!
  2dup 2>r ir-dispatch 2r> ir-ok? if 2drop else ir-report then ;

\ The word every evaluated line starts with: it parses the rest of the line
\ itself, so no token of the line reaches the host's interpreter.
: lf-ir-tokens ( -- ) begin parse-name dup while ir-token repeat 2drop ;

\ Reading. lf-ir-start resets the record and writes the header; lines then
\ come from a file (lf-ir-read-file) or one at a time (lf-ir-feed), and
\ lf-ir-finish checks the end of the input and gives the outcome.
: ir-unreadable ( -- ) ir-why-unreadable ir-invalid s" " ir-report ;
: ir-too-long ( -- ) 0 ir-column ! ir-unreadable ;
\ Count a line and evaluate its u characters, behind the prefix.
: ir-scan ( u -- )
  1 ir-line# +! dup ir-line-chars < if ir-text swap ir-prefix-chars + evaluate
  else drop ir-too-long then ;
: ir-reset ( xt -- )
  lf-ir-reader /lf-ir-reader erase lf-ir-reader reader-emit !
  outcome-ok ir-outcome ! ir-why-none ir-why ! -1 ir-current ! ir-mode-top ir-mode !
  ir-prefix ir-text swap chars move ;
: ir-header ( c-addr u -- )
  s" lf-ir 0.1" ir-append ir-flush s" source " ir-append ir-append ir-flush ;
: lf-ir-start ( xt c-addr u -- )
  rot ir-reset ir-def-capacity /ir-slot 0 ir-defs store-init 0= abort" lf-ir: store"
  ir-header ;
\ A line longer than the buffer is cut to the buffer's size, which
\ ir-scan then refuses as too long.
: lf-ir-feed ( c-addr u -- )
  ir-ok? 0= if 2drop exit then
  ir-line-chars min tuck ir-line-buffer swap chars move ir-scan ;
: ir-end-of-input ( -- )
  ir-mode @ ir-mode-top <> if ir-why-unclosed ir-invalid exit then
  ir-kept# @ if ir-why-left-over ir-unsupported then ;
: lf-ir-finish ( -- outcome )
  ir-ok? if 0 ir-column ! ir-end-of-input ir-ok? 0= if s" " ir-report then then
  ir-outcome @ ;

\ A file, read line by line straight into the line buffer. A line that
\ fills the buffer is too long; a read error stops the reader.
: ir-fetch ( fileid -- u true | false )
  >r ir-line-buffer ir-line-chars r> read-line
  if 2drop ir-unreadable false else 0= if drop false else true then then ;
: ir-more? ( fileid -- flag ) ir-fetch if ir-scan ir-ok? else false then ;
: ir-read-lines ( fileid -- ) begin dup ir-more? 0= until drop ;
: lf-ir-read-file ( xt c-addr u -- outcome )
  2dup 2>r lf-ir-start 2r> r/o open-file
  if drop ir-unreadable else dup ir-read-lines close-file drop then lf-ir-finish ;

\ For tests and callers: why the reader stopped, and where.
: lf-ir-reason ( -- reason ) ir-why @ ;
: lf-ir-where ( -- line column ) ir-here ;

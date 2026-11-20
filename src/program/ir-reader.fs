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
\ or an exception are incomplete and must not be used. lf-ir-finish ends
\ a read; a line fed after it stops the reader.
\
\ Threat model. The reader defends against hostile source files: whatever
\ a file holds, the reader refuses it or gives IR that means what Gforth
\ does with it (the rule below). Its caller and the output word are
\ trusted harness code (the receipt generator, the tests), relied on to
\ use the reader as documented here. Even so, it enforces this, and only
\ this, on them (ir-enter and ir-emit below):
\ - The four reader words, lf-ir-start, lf-ir-feed, lf-ir-finish and
\   lf-ir-read-file, keep the reader of their context busy while they
\   run, and so while the output word runs. A reader word called while
\   it is busy refuses (THROW -2), changing nothing but a count of calls.
\ - The read fails as invalid if its output word throws, calls a reader
\   word in its context, or returns with the data stack at another depth
\   (which also aborts). One that returns in another context aborts at
\   once, touching no record: the reader it left stays busy for good.
\ - An exception inside a reader word fails the read as invalid, or
\   leaves the reader busy for good (just before the word's handler is
\   set up, or just after its work threw), or, during the entry check or
\   once the work has made the reader idle again, acts as if it came
\   before or after the call: a read never ends ok if an exception cut
\   its work short or came before its reader went idle again. Every
\   exception passes on; one that stops the reading of a file's lines
\   closes the file first.
\ - A line fed before lf-ir-start or after lf-ir-finish fails the read; a
\   fed line's length is unsigned, so a negative one is too long, and the
\   line is refused unread.
\ Other misuse is not detected (docs/programming/PROGRAM_IR.md lists it),
\ such as an output word that writes into the reader's record or
\ unbalances the return stack, or a caller or output word that calls an
\ internal word (any but the four reader words, lf-ir-reason and
\ lf-ir-where), such as ir-feed, which does lf-ir-feed's work without the
\ entry check.
\
\ It must accept less than Gforth (1.0 and 0.7.3) does, never more, and
\ give what it accepts Gforth's meaning:
\ - It splits a file into lines itself, at LF only, dropping one CR just
\   before an LF, and each line into tokens at spaces and tabs, as both
\   hosts do. A line holding any other character outside printable ASCII
\   (NUL, any other CR, DEL, any byte of 128 or more) is refused, even in
\   a comment, so no character whose treatment differs between hosts
\   reaches a token. Nothing reaches the host's interpreter, so no source
\   token is ever executed, whatever the caller's STATE, BASE or search
\   order.
\ - Names are looked up with ASCII case folded (A-Z equals a-z), as
\   Gforth looks them up, and written in lower case. A definition whose
\   folded name the reader knows (its vocabulary below or an earlier
\   definition) is refused, so the file cannot change those words under
\   another spelling. It may define another name the host has, such as .
\   or DEPTH: its IR is unaffected, but Gforth then uses that definition
\   in anything compiled after the file, so the file must be loaded last.
\ - Literals are plain decimal: at most ten digits, at most 2147483647 in
\   size. The tokens before CONSTANT must leave exactly one value and must
\   not divide: Gforth runs them while it loads the file, and a division
\   by zero, or of the smallest cell by -1, stops the load there, whereas
\   the IR runs a constant's body only when the constant is called.
\ Gforth must load the source with BASE ten, its default search order and
\ its own standard words, as it does when it starts; nothing here can
\ check that.
\
\ Requires ../lib/lib.fs. State: lf-ir-reader, one context record (in a
\ new context the reader is stopped until lf-ir-start; its entry state,
\ busy and the count of calls, outlives each read), reached only
\ through the accessors below; and lf-ir-vocabulary, lf-ir-reasons and
\ three dispatch tables, filled while this file loads and never changed
\ afterwards. One read at a time in each context.

decimal
require ../lib/lib.fs
require ../lib/decimal.fs

\ Classes of the words the reader knows.
0 constant ir-prim        \ an IR primitive on the data stack: dup, +, max, ...
1 constant ir-divide      \ / and mod: IR primitives that can throw on the host
2 constant ir-rstack      \ an IR primitive on the return stack: >r r> r@
3 constant ir-colon
4 constant ir-semicolon
5 constant ir-if
6 constant ir-else
7 constant ir-then
8 constant ir-begin
9 constant ir-while
10 constant ir-repeat
11 constant ir-exit
12 constant ir-constant
13 constant ir-paren       \ a ( comment )
14 constant ir-backslash   \ a \ comment
15 constant ir-decimal
16 constant ir-other       \ standard Forth that IR 0.1 does not model
17 constant ir-classes

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
  2dup-under ir-find dup if 2swap 2drop then ;

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
: ir-division ( effect c-addr u -- ) ir-divide -rot ir-add ir-effect! ;
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
21 s" /" ir-division   21 s" mod" ir-division 11 s" negate" ir-data
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
32 /ir-slot 0 store: lf-ir-reasons
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
21 constant ir-why-dividing  s" a division outside a definition" ir-reason
22 constant ir-why-stopped   s" reader not started" ir-reason
23 constant ir-why-output    s" output word failed" ir-reason
24 constant ir-why-finished  s" reader already finished" ir-reason
25 constant ir-why-busy      s" reader busy" ir-reason
26 constant ir-why-interrupted s" read stopped by an exception" ir-reason
27 constant ir-reasons
lf-ir-reasons store-count @ ir-reasons <> [if] .( lf-ir: reason table ) abort [then]
: ir-reason-text ( reason -- c-addr u ) lf-ir-reasons store-slot ir-entry-text ;

\ Capacities.
31 constant ir-name-chars       \ longest definition name
32 constant ir-def-capacity     \ definitions per file
8 constant ir-control-capacity  \ open IF and BEGIN structures
8 constant ir-pending-capacity  \ tokens before CONSTANT
96 constant ir-out-chars        \ longest output line
128 constant ir-line-chars      \ source lines must be shorter than this
128 constant ir-block-chars     \ characters read from a file at a time
ir-def-capacity /ir-slot store-size constant /ir-defs

\ A token kept until CONSTANT: a primitive (value: vocabulary index), a
\ literal (value: the number) or a call (value: definition index).
0 constant ir-kept-prim
1 constant ir-kept-lit
2 constant ir-kept-call
begin-structure /ir-token
  field: ir-token-kind
  field: ir-token-value
  2 cells +field ir-token-place  \ where it was read: line column, with 2@ 2!
end-structure

\ What the next token is.
0 constant ir-mode-top        \ between definitions
1 constant ir-mode-word       \ the name after :
2 constant ir-mode-body       \ inside a colon definition
3 constant ir-mode-constant   \ the name after CONSTANT
4 constant ir-modes

begin-structure /lf-ir-reader
  \ The entry state (ir-enter), which a new read keeps.
  field: irr-busy          \ true while a reader word runs in this context
  field: irr-calls         \ reader words called in this context, refused ones too
  \ The read, which lf-ir-start erases.
  field: irr-emit          \ output word ( c-addr u -- ), one line per call
  field: irr-outcome       \ outcome-ok until the first diagnostic
  field: irr-reason        \ why it stopped, or ir-why-none
  field: irr-finished      \ true once lf-ir-finish has ended the read
  field: irr-line          \ number of the current line, from 1
  field: irr-column        \ column of the current token, from 1; 0 at end of file
  field: irr-start         \ the current line's first character
  2 cells +field irr-rest  \ the part of the line not read yet: c-addr u, with 2@ 2!
  field: irr-mode
  field: irr-current       \ definition being compiled, or -1
  2 cells +field irr-mark  \ where it started: line column, with 2@ 2!
  field: irr-depth        \ open control structures
  ir-control-capacity cells +field irr-control
  field: irr-kept#
  field: irr-values        \ cells the kept tokens leave on the data stack
  ir-pending-capacity /ir-token * +field irr-kept
  field: irr-out#
  \ Character buffers are padded to whole cells, so later fields stay aligned.
  ir-out-chars chars aligned +field irr-out
  ir-line-chars chars aligned +field irr-folded   \ the current token in lower case
  /ir-defs +field irr-defs         \ a store of /ir-slot records
  field: irr-held          \ characters of a file's current line so far
  ir-line-chars chars aligned +field irr-text     \ the current line
  ir-block-chars chars aligned +field irr-block   \ the last block read from a file
end-structure
/lf-ir-reader context-record: lf-ir-reader

\ Accessors: the only words that name lf-ir-reader.
: ir-busy ( -- addr ) lf-ir-reader irr-busy ;
: ir-calls ( -- addr ) lf-ir-reader irr-calls ;
: ir-outcome ( -- addr ) lf-ir-reader irr-outcome ;
: ir-why ( -- addr ) lf-ir-reader irr-reason ;
: ir-finished ( -- addr ) lf-ir-reader irr-finished ;
: ir-line# ( -- addr ) lf-ir-reader irr-line ;
: ir-column ( -- addr ) lf-ir-reader irr-column ;
: ir-start ( -- addr ) lf-ir-reader irr-start ;
: ir-rest ( -- c-addr u ) lf-ir-reader irr-rest 2@ ;
: ir-rest! ( c-addr u -- ) lf-ir-reader irr-rest 2! ;
: ir-mode ( -- addr ) lf-ir-reader irr-mode ;
: ir-current ( -- addr ) lf-ir-reader irr-current ;
: ir-mark ( -- line column ) lf-ir-reader irr-mark 2@ ;
: ir-mark! ( line column -- ) lf-ir-reader irr-mark 2! ;
: ir-depth ( -- addr ) lf-ir-reader irr-depth ;
: ir-control ( -- addr ) lf-ir-reader irr-control ;
: ir-kept# ( -- addr ) lf-ir-reader irr-kept# ;
: ir-values ( -- addr ) lf-ir-reader irr-values ;
: ir-kept ( i -- token ) /ir-token * lf-ir-reader irr-kept + ;
: ir-out# ( -- addr ) lf-ir-reader irr-out# ;
: ir-out ( -- c-addr ) lf-ir-reader irr-out ;
: ir-folded ( -- c-addr ) lf-ir-reader irr-folded ;
: ir-defs ( -- store ) lf-ir-reader irr-defs ;
: ir-held ( -- addr ) lf-ir-reader irr-held ;
: ir-text ( -- c-addr ) lf-ir-reader irr-text ;
: ir-block ( -- c-addr ) lf-ir-reader irr-block ;
: ir-emit! ( xt -- ) lf-ir-reader irr-emit ! ;
: ir-emit@ ( -- xt ) lf-ir-reader irr-emit @ ;
\ The read: the record after its entry state.
: ir-the-read ( -- addr u ) lf-ir-reader irr-emit /lf-ir-reader 0 irr-emit - ;
: ir-here ( -- line column ) ir-line# @ ir-column @ ;

\ Until lf-ir-start, the reader of every context is stopped: lf-ir-feed
\ reads nothing, lf-ir-finish gives invalid, and no line is written.
: ir-stopped ( -- )
  ['] 2drop ir-emit! outcome-invalid ir-outcome ! ir-why-stopped ir-why ! ;
' ir-stopped context-setup

\ Stopping. Only the first diagnostic counts; later tokens are skipped.
: ir-ok? ( -- flag ) ir-outcome @ ok? ;
: ir-state! ( outcome reason -- ) ir-why ! ir-outcome ! ;
: ir-stop ( outcome reason -- ) ir-ok? if ir-state! else 2drop then ;
: ir-unsupported ( reason -- ) outcome-unsupported swap ir-stop ;
: ir-invalid ( reason -- ) outcome-invalid swap ir-stop ;
: ir-full ( -- ) outcome-full ir-why-capacity ir-stop ;

\ Entry. Each reader word (lf-ir-start, lf-ir-feed, lf-ir-finish and
\ lf-ir-read-file) does its work through ir-enter, the one entry check.
\ It counts the call, and refuses it (THROW -2), changing nothing else,
\ while the reader of this context is busy: while a reader word runs in
\ it, and so while the output word runs. Otherwise it makes the reader
\ busy, and the work makes it idle when it returns. If the work throws,
\ the read stops as invalid ("read stopped by an exception"), the reader
\ is made idle and the exception passes on; but if the context has
\ changed, which only an output word does (ir-emit has then aborted), no
\ record is touched. An exception that comes after the reader is made
\ busy but before the handler is set up, or after the work threw but
\ before the handler made the reader idle, leaves it busy for good:
\ every reader word then refuses, so that read never ends.
: ir-home? ( context -- flag ) lf-context @ = ;
: ir-claim ( -- ) 1 ir-calls +! ir-busy @ abort" lf-ir: reader busy" true ir-busy ! ;
: ir-idle ( -- ) false ir-busy ! ;
: ir-work ( i*x xt -- j*x ) execute ir-idle ;
: ir-thrown ( code context -- code )
  ir-home? over 0<> and if ir-why-interrupted ir-invalid ir-idle then ;
: ir-enter ( i*x xt -- j*x )
  ir-claim lf-context @ >r ['] ir-work catch r> ir-thrown throw ;

\ The output word. It runs while the reader is busy, so a reader word it
\ calls in this context is refused, and counted. The read goes on only if
\ the output word returned normally, in the context it was called in,
\ having called no reader word there, with the data stack as deep as
\ before less its two arguments. Otherwise the read stops as invalid
\ ("output word failed"), and any exception passes on; a change of depth
\ also aborts. A change of context aborts at once and touches no record,
\ nor switches back, since the output word may have freed the context it
\ left; the reader there stays busy.
: ir-failed ( -- ) outcome-invalid ir-why-output ir-state! ;
: ir-call ( c-addr u -- code ) ir-emit@ catch dup if nip nip then ;
: ir-same-context ( context -- ) ir-home? 0= abort" lf-ir: output word changed context" ;
\ depth was taken with the output word's two arguments on the stack; its
\ code and depth itself now take their place, so DEPTH must equal it.
: ir-same-depth ( code depth -- code )
  depth <> dup if ir-failed then abort" lf-ir: output word changed stack depth" ;
\ Stop the read unless the output word gave code 0 and no reader word was
\ called since the count of calls was calls.
: ir-clean ( code calls -- code ) ir-calls @ <> over or if ir-failed then ;
: ir-emit ( c-addr u -- )
  ir-calls @ >r depth lf-context @ 2>r ir-call 2r> ir-same-context ir-same-depth
  r> ir-clean throw ;

\ The output line under construction. Text that would not fit stops the
\ reader instead of overrunning the buffer.
: ir-room ( -- u ) ir-out-chars ir-out# @ - ;
: ir-copy ( c-addr u -- ) ir-out ir-out# @ chars + swap dup ir-out# +! chars move ;
: ir-append ( c-addr u -- ) dup ir-room > if 2drop ir-full else ir-copy then ;
: ir-send ( -- ) ir-out ir-out# @ ir-emit 0 ir-out# ! ;
: ir-flush ( -- ) ir-ok? if ir-send else 0 ir-out# ! then ;

\ Pieces of a line. Numbers are written in decimal whatever BASE is.
: ir-number ( n -- ) n>decimal ir-append ;
: ir-indent ( depth -- ) 1+ 2* s"                     " drop swap ir-append ;
: ir-location ( line column -- )
  s"  @" ir-append swap ir-number s" :" ir-append ir-number ;
: ir-done ( -- ) ir-here ir-location ir-flush ;
: ir-keyword ( c-addr u depth -- ) ir-indent ir-append ir-done ;
: ir-keyword-line ( c-addr u -- ) ir-depth @ ir-keyword ;
: ir-start-line ( c-addr u -- ) ir-depth @ ir-indent ir-append ;
: ir-end ( -- ) s" end" ir-append ir-done ;
: ir-def ( index -- entry ) ir-defs store-slot ;
: ir-def-append ( index -- ) ir-def ir-entry-text ir-append ;

\ The diagnostic line: "unsupported @line:column: reason: token", or
\ without ": token" (ir-diagnose) for a failure that has no token. Its
\ pieces are clipped to the line, and nothing in it can stop the reader.
: ir-clipped ( c-addr u -- ) ir-room min ir-copy ;
: ir-outcome-text ( -- )
  0 ir-out# ! ir-outcome @ outcome-text ir-clipped ir-here ir-location ;
: ir-why-text ( -- ) s" : " ir-clipped ir-why @ ir-reason-text ir-clipped ;
: ir-token-text ( c-addr u -- ) dup if s" : " ir-clipped ir-clipped else 2drop then ;
: ir-report ( c-addr u -- ) ir-outcome-text ir-why-text ir-token-text ir-send ;
: ir-diagnose ( -- ) s" " ir-report ;
\ Report the token c-addr u if the reader has stopped.
: ir-blame ( c-addr u -- ) ir-ok? if 2drop else ir-report then ;

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
\ 2147483647 in size so that the same source suits 32-bit cells. On cells
\ of 32 bits or more, ten digits fit in a double cell, so the conversion
\ cannot wrap.
2147483647 constant ir-literal-max
10 constant ir-digits-max
: ir-negative ( c-addr u -- c-addr' u' flag )
  dup if over c@ [char] - = if 1 /string true exit then then false ;
: ir-fits? ( u -- u true | false ) dup ir-literal-max u> if drop false else true then ;
: ir-whole? ( c-addr u -- u true | false )
  dup 1 ir-digits-max 1+ within 0= if 2drop false exit then
  decimal>number nip 0= swap 0= and if ir-fits? else drop false then ;
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

\ The cell at index of a table of cells.
: ir-cell ( index table -- addr ) swap cells + ;

\ Open IF and BEGIN structures; a frame is the class of its latest word.
: ir-top ( -- addr ) ir-depth @ 1- ir-control ir-cell ;
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

\ Dispatch tables: one execution token for each class or mode, stored
\ under the name of its index, so that the order of the constants above
\ does not matter; loading stops if a slot is left empty.
: ir-table ( n "name" -- ) create 0 ?do 0 , loop ;
: ir-act! ( xt index table -- ) ir-cell ! ;
: ir-filled? ( table n -- flag ) 0 -rot cells-has? 0= ;
\ Refuse the word of vocabulary index as unsupported, for reason.
: ir-refuse ( index reason -- ) nip ir-unsupported ;

\ Actions for a vocabulary word inside a definition ( index -- ).
: ir-to-top ( -- ) ir-mode-top ir-mode ! ;
: ir-body-prim ( index -- ) s" prim " ir-start-line ir-word-text ir-append ir-done ;
: ir-body-nested ( index -- ) drop ir-why-nested ir-invalid ;
: ir-body-inside ( index -- ) ir-why-inside ir-refuse ;
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
: ir-not-ir ( index -- ) ir-why-not-ir ir-refuse ;

ir-classes ir-table ir-body-actions
: ir-body! ( xt class -- ) ir-body-actions ir-act! ;
' ir-body-prim ir-prim ir-body!          ' ir-body-prim ir-divide ir-body!
' ir-body-prim ir-rstack ir-body!        ' ir-body-nested ir-colon ir-body!
' ir-body-end ir-semicolon ir-body!      ' ir-body-if ir-if ir-body!
' ir-body-else ir-else ir-body!          ' ir-body-then ir-then ir-body!
' ir-body-begin ir-begin ir-body!        ' ir-body-while ir-while ir-body!
' ir-body-repeat ir-repeat ir-body!      ' ir-body-exit ir-exit ir-body!
' ir-body-inside ir-constant ir-body!    ' ir-skip-paren ir-paren ir-body!
' ir-skip-line ir-backslash ir-body!     ' ir-body-inside ir-decimal ir-body!
' ir-not-ir ir-other ir-body!
ir-body-actions ir-classes ir-filled? 0= [if] .( lf-ir: body actions ) abort [then]

\ Actions for a vocabulary word outside a definition ( index -- ). Tokens
\ before CONSTANT are kept, and the cells they would leave on Gforth's data
\ stack are counted; a token taking more cells than are there would take
\ values the caller left, which the IR does not model.
: ir-take ( taken given -- )
  over ir-values @ > if 2drop ir-why-borrowed ir-unsupported exit then
  swap - ir-values +! ;
: ir-token-at! ( token -- ) ir-here rot ir-token-place 2! ;
: ir-keep! ( value kind token -- )
  tuck ir-token-kind ! tuck ir-token-value ! ir-token-at! ;
: ir-keep ( value kind -- )
  ir-kept# @ dup ir-pending-capacity < if ir-kept ir-keep! 1 ir-kept# +! exit then
  drop 2drop ir-full ;
: ir-top-prim ( index -- ) dup ir-effect ir-take ir-kept-prim ir-keep ;
\ Gforth divides while it loads the file, and a division by zero, or of
\ the smallest cell by -1, stops the load there (THROW -10 or -11); the
\ IR divides only when the constant is called. So no division is kept.
: ir-top-divide ( index -- ) ir-why-dividing ir-refuse ;
: ir-top-colon ( index -- )
  drop ir-kept# @ if ir-why-left-over ir-unsupported exit then
  ir-here ir-mark! ir-mode-word ir-mode ! ;
: ir-top-control ( index -- ) ir-why-outside ir-refuse ;
: ir-one-value ( -- )
  ir-values @ 1 <> if ir-why-one-value ir-unsupported exit then
  ir-mode-constant ir-mode ! ;
\ CONSTANT with nothing before it would take a value from outside the
\ file, as + would: unsupported, like that.
: ir-top-constant ( index -- )
  drop ir-kept# @ if ir-one-value else ir-why-no-value ir-unsupported then ;
: ir-top-decimal ( index -- ) drop ;  \ BASE is already ten, as assumed above

\ >r r> r@, / and mod are not kept.
ir-classes ir-table ir-top-actions
: ir-top! ( xt class -- ) ir-top-actions ir-act! ;
' ir-top-prim ir-prim ir-top!            ' ir-top-divide ir-divide ir-top!
' ir-top-control ir-rstack ir-top!       ' ir-top-colon ir-colon ir-top!
' ir-top-control ir-semicolon ir-top!    ' ir-top-control ir-if ir-top!
' ir-top-control ir-else ir-top!         ' ir-top-control ir-then ir-top!
' ir-top-control ir-begin ir-top!        ' ir-top-control ir-while ir-top!
' ir-top-control ir-repeat ir-top!       ' ir-top-control ir-exit ir-top!
' ir-top-constant ir-constant ir-top!    ' ir-skip-paren ir-paren ir-top!
' ir-skip-line ir-backslash ir-top!      ' ir-top-decimal ir-decimal ir-top!
' ir-not-ir ir-other ir-top!
ir-top-actions ir-classes ir-filled? 0= [if] .( lf-ir: top actions ) abort [then]

: ir-act ( index table -- ) over ir-class swap ir-cell @ execute ;

\ A token that is not in the vocabulary: a definition, else a literal.
: ir-body-call ( index -- )
  dup ir-current @ = if drop ir-why-recursive ir-unsupported exit then
  s" call " ir-start-line ir-def-append ir-done ;
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
: ir-word-line ( index -- )
  dup ir-current ! s" word " ir-append ir-def-append ir-mark ir-location ir-flush ;
: ir-word-name ( c-addr u -- )
  ir-colon ir-define if ir-word-line ir-mode-body ir-mode ! then ;
\ A kept token's instruction; there are only three kinds.
: ir-kept-text ( value kind -- )
  case ir-kept-prim of s" prim " ir-append ir-word-text ir-append endof
    ir-kept-lit of s" lit " ir-append ir-number endof
    ir-kept-call of s" call " ir-append ir-def-append endof
    true abort" lf-ir: kept kind" endcase ;
: ir-token-where ( token -- line column ) ir-token-place 2@ ;
: ir-replay ( token -- )
  0 ir-indent dup ir-token-value @ over ir-token-kind @ ir-kept-text
  ir-token-where ir-location ir-flush ;
: ir-replay-all ( -- )
  ir-kept# @ 0 ?do i ir-kept ir-replay loop 0 ir-kept# ! 0 ir-values ! ;
: ir-constant-line ( index -- ) s" constant " ir-append ir-def-append ir-done ;
: ir-constant-name ( c-addr u -- )
  ir-constant ir-define if ir-constant-line ir-replay-all ir-end ir-to-top then ;

\ One token, in the current mode, looked up in lower case; the first
\ failure is reported with the token as the source spells it.
ir-modes ir-table ir-mode-actions  \ indexed by mode, which only the reader sets
\ Named so, not ir-mode!, which would read as storing into ir-mode.
: ir-mode-action! ( xt mode -- ) ir-mode-actions ir-act! ;
' ir-top-token ir-mode-top ir-mode-action!
' ir-word-name ir-mode-word ir-mode-action!
' ir-body-token ir-mode-body ir-mode-action!
' ir-constant-name ir-mode-constant ir-mode-action!
ir-mode-actions ir-modes ir-filled? 0= [if] .( lf-ir: mode actions ) abort [then]
: ir-dispatch ( c-addr u -- ) ir-mode @ ir-mode-actions ir-cell @ execute ;
: ir-column! ( c-addr -- ) ir-start @ - 1 chars / 1+ ir-column ! ;
: ir-token ( c-addr u -- ) over ir-column! 2dup 2>r ir-fold ir-dispatch 2r> ir-blame ;

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
\ too long. The length u, unsigned, may exceed the line buffer; the line
\ is then refused before any of it is read.
: ir-scan ( c-addr u -- )
  ir-ok? 0= if 2drop exit then
  1 ir-line# +! dup ir-line-chars u< if ir-scan-line else 2drop ir-unreadable then ;

\ Reading. lf-ir-start erases the read and writes the header; lines then
\ come from a file (lf-ir-read-file) or one at a time (lf-ir-feed), and
\ lf-ir-finish checks the end of the input and gives the outcome. Each
\ reader word does its work through ir-enter.
: ir-reset ( xt -- )
  ir-the-read erase ir-emit!
  outcome-ok ir-outcome ! ir-why-none ir-why ! -1 ir-current ! ir-to-top ;
\ Text copied into the line buffer, of at most ir-line-chars characters,
\ so that the caller may give it in a transient buffer, such as the
\ pictured-numeric one, which the reader and its output word may reuse.
: ir-own ( c-addr u -- c-addr' u ) tuck ir-text swap chars move ir-text swap ;
\ The path is copied before the output word first runs, so that the
\ header and OPEN-FILE use the path given; the line buffer holds no line
\ until the file is open. A path longer than the buffer, its length u
\ taken as unsigned, is cut to the buffer's size: it does not fit its
\ header line either, so the read stops as full, quoting the copy.
: ir-cut ( u -- u' ) dup ir-line-chars u> if drop ir-line-chars then ;
: ir-path ( c-addr u -- c-addr' u' ) ir-cut ir-own ;
: ir-source-header ( c-addr u -- ) s" source " ir-append ir-append ir-flush ;
\ A path too long for its header line stops the reader with a diagnostic.
: ir-header ( c-addr u -- )
  s" lf-ir 0.1" ir-append ir-flush 2dup ir-source-header ir-blame ;
\ Start a read and write its header; give the copy of its path.
: ir-new-read ( xt c-addr u -- c-addr' u' )
  rot ir-reset ir-def-capacity /ir-slot 0 ir-defs store-init 0= abort" lf-ir: store"
  ir-path 2dup ir-header ;
: ir-start-read ( xt c-addr u -- ) ir-new-read 2drop ;
: lf-ir-start ( xt c-addr u -- ) ['] ir-start-read ir-enter ;
\ A fed line is copied first, so it may live in a transient buffer too. A
\ line too long to copy, its length u taken as unsigned, is neither copied
\ nor read: ir-scan refuses it unread. A fed line has no line end: any CR
\ in it is refused. Nothing is copied into a stopped reader.
: ir-feed-line ( c-addr u -- ) dup ir-line-chars u< if ir-own then ir-scan ;
\ A line fed after lf-ir-finish stops the reader, and is not written about.
: ir-unfinished ( -- ) ir-finished @ if ir-why-finished ir-invalid then ;
: ir-feed ( c-addr u -- ) ir-unfinished ir-ok? if ir-feed-line else 2drop then ;
: lf-ir-feed ( c-addr u -- ) ['] ir-feed ir-enter ;
: ir-at-end ( -- )
  ir-mode @ ir-mode-top <> if ir-why-unclosed ir-invalid exit then
  ir-kept# @ if ir-why-left-over ir-unsupported then ;
: ir-end-of-input ( -- ) 0 ir-column ! ir-at-end ir-ok? 0= if ir-diagnose then ;
\ Finishing ends the read; finishing again gives the same outcome.
: ir-finish ( -- outcome )
  ir-ok? if ir-end-of-input then true ir-finished ! ir-outcome @ ;
: lf-ir-finish ( -- outcome ) ['] ir-finish ir-enter ;

\ A file, read a block at a time and split into lines at LF only, so that
\ the reader, not the host's READ-LINE, decides where a line ends. The
\ current line is held in the line buffer; characters beyond the buffer
\ are counted, not kept, and ir-scan refuses the line as too long, at the
\ end of the first block after which it is too long even without a CR, so
\ a file without LF is not read to its end. One CR just before an LF is
\ dropped, as both Gforths drop it; any other CR stays in its line and is
\ refused as a character outside printable ASCII. A last line without LF
\ is read too. A read error stops the reader. The file is closed when an
\ exception stops the reading of its lines; the exception passes on, and
\ ir-enter stops the read, as for any exception, OPEN-FILE's included.
10 constant ir-lf
13 constant ir-cr
: ir-hold ( char -- )
  ir-held @ dup ir-line-chars < if chars ir-text + c! else 2drop then 1 ir-held +! ;
: ir-line ( u -- ) ir-text swap 0 ir-held ! ir-scan ;
\ Whether the line held, of u characters, all of them kept, ends in CR.
: ir-cr-last? ( u -- flag )
  dup 1 ir-line-chars 1+ within if 1- chars ir-text + c@ ir-cr = else drop false then ;
: ir-line-feed ( -- ) ir-held @ dup ir-cr-last? if 1- then ir-line ;
: ir-last-line ( -- ) ir-held @ ?dup if ir-line then ;
: ir-char ( char -- ) dup ir-lf = if drop ir-line-feed else ir-hold then ;
: ir-chars ( c-addr u -- ) chars over + swap ?do i c@ ir-char 1 chars +loop ;
\ The next block: its length, 0 at the end of the file, and true; or
\ false after a read error.
: ir-fetch ( fileid -- u true | false )
  >r ir-block ir-block-chars r> read-file if drop ir-unreadable false else true then ;
\ Refuse the line held if it is too long even without a CR at its end.
: ir-too-long ( -- ) ir-held @ dup ir-line-chars > if ir-line else drop then ;
\ The lines of a block of u characters, or at the end of the file the
\ last line; false once the file has ended or the reader has stopped.
: ir-block-lines ( u -- flag )
  ?dup if ir-block swap ir-chars ir-too-long ir-ok? else ir-last-line false then ;
: ir-more? ( fileid -- flag ) ir-fetch if ir-block-lines else false then ;
: ir-read-lines ( fileid -- ) begin dup ir-more? 0= until drop ;
: ir-close-file ( fileid -- ) close-file drop ;
: ir-read-open ( fileid -- )
  dup >r ['] ir-read-lines catch dup if nip then r> ir-close-file throw ;
\ Opened as a binary file, so that no host translates its line ends.
: ir-read-path ( c-addr u -- )
  r/o bin open-file if drop ir-unreadable else ir-read-open then ;
: ir-read-file ( xt c-addr u -- outcome )
  ir-new-read ir-ok? if ir-read-path else 2drop then ir-finish ;
: lf-ir-read-file ( xt c-addr u -- outcome ) ['] ir-read-file ir-enter ;

\ For tests and callers: why the reader stopped, or that it is busy (as
\ the output word sees it), and where.
: lf-ir-reason ( -- reason ) ir-busy @ if ir-why-busy else ir-why @ then ;
: lf-ir-where ( -- line column ) ir-here ;

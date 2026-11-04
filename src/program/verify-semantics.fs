\ Verification semantics of IR 0.1 (ADR 0019 §1-§3): what each Forth word
\ does in correctness mode, shared by both designs. `DUP` writes
\ `prim dup`; `:` reads its name, as Forth's `:` does, defines it in the
\ file's own word list and writes `word NAME`, leaving Forth interpreting;
\ `IF` writes `if` and opens a frame; a word of the file writes `call
\ NAME`; a plain decimal writes `lit n`. Inside a definition each
\ instruction is written at once, one level deeper per open frame; outside
\ one, the tokens before CONSTANT are kept and written as its body. The
\ structure frames live here, never on the data stack, so no number can
\ stand for one. A word refuses what IR 0.1 does not model, with the
\ reasons of verify-report.fs.
\
\ The words with verification semantics are a table, pv-names, keyed by
\ name (A-Z read as a-z, as Gforth finds names): the 38 primitives of IR
\ 0.1 (in the order of Prim in tests/reference/program-ir.lean, each with
\ its data-stack effect: taken, then given, as two digits), the 13 words
\ with an action of their own, and every other name of Forth-2012's Core
\ and Core Ext word sets, reserved: such a word refuses ("a Forth word
\ outside IR 0.1") and no file may redefine it. Each entry also keeps the
\ execution token that FORTH-WORDLIST gave for its name when this file
\ loaded: its identity, by which the mode shift (verify.fs) knows the
\ host's own word.
\
\ Calls are bound early: Forth's own lookup finds a word of the file, the
\ one visible at that point, and a name is defined once (a redefinition,
\ in any case of letters, is refused), so writing the call by name is
\ exact. Names that read as numbers are refused (owner's answer 4).
\
\ Untrusted, like verify-report.fs. State: one context record, pv-state,
\ reset for each run, and the table, read-only once this file has loaded.
\ Every run grows the dictionary: a word list, and a word for each
\ definition.

require ../lib/lib.fs
require ../lib/text-run.fs
require ../author/source.fs
require ./verify-report.fs

\ Kinds of table entries.
0 constant pv-kind-data          \ an IR primitive on the data stack: dup, +, max ...
1 constant pv-kind-rstack        \ an IR primitive on the return stack: >r r> r@
2 constant pv-kind-divide        \ / and mod, which can throw on the host
3 constant pv-kind-action        \ a word with an action of its own: : ; if ...
4 constant pv-kind-reserved      \ a standard word outside IR 0.1

16 constant pv-entry-chars       \ longest name in the table
begin-structure /pv-entry
  field: pv-entry-kind
  field: pv-entry-datum          \ a primitive's effect, or an action's xt
  field: pv-entry-host           \ the xt FORTH-WORDLIST gave for the name, or 0
  field: pv-entry-length
  pv-entry-chars chars aligned +field pv-entry-name
end-structure
200 /pv-entry aligned 0 store: pv-names

: pv-entry-text ( entry -- c-addr u ) dup pv-entry-name swap pv-entry-length @ ;
: pv-entry ( i -- entry ) pv-names store-slot ;

\ Names compare with A-Z read as a-z; the table and definitions keep them
\ in lower case.
: pv-lower ( char -- char' ) dup [char] A [char] Z 1+ within if bl or then ;
: pv-fold ( c-addr u -- ) chars over + swap ?do i c@ pv-lower i c! 1 chars +loop ;
: pv-same-char? ( c-addr1 c-addr2 -- flag ) c@ swap c@ pv-lower = ;
\ Whether c-addr1 u, folded, is the lower-case text at c-addr2.
: pv-folded-as? ( c-addr1 c-addr2 u -- flag )
  0 ?do 2dup pv-same-char? 0= if 2drop false unloop exit then char+ swap char+ swap loop
  2drop true ;
: pv-names? ( c-addr u entry -- flag )
  pv-entry-text rot over = if pv-folded-as? else 2drop drop false then ;
\ The entry of a name, any case of letters.
: pv-entry-of ( c-addr u -- entry true | false )
  pv-names store-count @ 0 ?do 2dup i pv-entry pv-names? if 2drop i pv-entry true unloop
    exit then loop 2drop false ;

\ Making the table, while this file loads; a name twice, or too long, aborts.
: pv-host ( c-addr u -- xt|0 ) forth-wordlist search-wordlist 0= if 0 then ;
: pv-name-room ( c-addr u -- c-addr u )
  dup pv-entry-chars > abort" pv: name too long" 2dup pv-entry-of abort" pv: name twice" ;
: pv-entry-text! ( c-addr u entry -- )
  2dup pv-entry-length ! pv-entry-name swap chars move ;
: pv-name, ( c-addr u -- entry )
  pv-name-room pv-names store-new-slot 0= abort" pv: table full" drop >r
  2dup pv-host r@ pv-entry-host ! r@ pv-entry-text! r> ;
\ A word with verification semantics must be a word of this Forth, whose
\ identity the mode shift compares; a reserved one need not.
: pv-host-word ( entry kind -- entry kind )
  dup pv-kind-reserved <> if over pv-entry-host @ 0= abort" pv: not a word of this Forth"
  then ;
: pv-typed ( datum entry kind -- ) pv-host-word over pv-entry-kind ! pv-entry-datum ! ;
: pv-data ( effect c-addr u -- ) pv-name, pv-kind-data pv-typed ;
: pv-division ( effect c-addr u -- ) pv-name, pv-kind-divide pv-typed ;
: pv-return ( effect c-addr u -- ) pv-name, pv-kind-rstack pv-typed ;
: pv-act ( xt c-addr u -- ) pv-name, pv-kind-action pv-typed ;
: pv-reserve ( c-addr u -- ) 0 -rot pv-name, pv-kind-reserved pv-typed ;
: pv-reserve-all ( c-addr u -- )
  begin lfa-next-token dup while pv-reserve repeat 2drop 2drop ;

\ Literals: a minus sign or none, then one to ten decimal digits, at most
\ 2147483647 in size, so that the same source suits 32-bit cells; the
\ value is read here, never by the host.
2147483647 constant pv-literal-max
10 constant pv-digits-max
: pv-negative ( c-addr u -- c-addr' u' flag )
  dup if over c@ [char] - = if 1 /string true exit then then false ;
: pv-convert ( c-addr u -- ud c-addr' u' ) 0 0 2swap base @ >r decimal >number r> base ! ;
: pv-fits? ( u -- u true | false ) dup pv-literal-max u> if drop false else true then ;
: pv-whole? ( c-addr u -- u true | false )
  dup 1 pv-digits-max 1+ within 0= if 2drop false exit then
  pv-convert nip 0= swap 0= and if pv-fits? else drop false then ;
: pv-literal? ( c-addr u -- n true | false )
  pv-negative >r pv-whole? if r> if negate then true else r> drop false then ;

\ Names that read as numbers, refused for every definition: anything that
\ Forth-2012 or Gforth (1.0 or 0.7.3) could read as a number with BASE
\ ten, and more. After any leading signs and base prefixes (+ - # $ % &):
\ a digit; Gforth 1.0's digit separator _; a quote and one more character
\ ('c', Gforth's 'c and -'c); after a prefix, a hexadecimal letter; or a
\ point before any of these (Gforth 1.0 reads .5 as a float, ._ and $.a
\ as numbers). So 5, -0, 1e, $10, 'a', -'a', .5, _1, -_1 and #_1 are
\ refused, and ->x, "x", x:dup and -rot are names. tests/program/verify.fs
\ checks the rule against the running Gforth: every short token it reads
\ with an empty search order must be refused here.
: pv-digit? ( char -- flag ) [char] 0 [char] 9 1+ within ;
: pv-hex-letter? ( char -- flag ) pv-lower [char] a [char] f 1+ within ;
: pv-sign? ( char -- flag ) dup [char] + = swap [char] - = or ;
: pv-prefix? ( char -- flag ) dup [char] # [char] & 1+ within swap pv-sign? or ;
: pv-unprefixed? ( char -- flag ) pv-prefix? 0= ;
\ Whether c-addr u starts with char and has more after it.
: pv-first? ( c-addr u char -- flag )
  over 1 > if nip swap c@ = else 2drop drop false then ;
: pv-quote? ( c-addr u -- flag ) [char] ' pv-first? ;
: pv-point? ( c-addr u -- flag ) [char] . pv-first? ;
\ The first character of a number after the signs and prefixes.
: pv-numeral? ( char prefixed? -- flag )
  over pv-hex-letter? and over [char] _ = or swap pv-digit? or ;
\ The rest after the signs and prefixes, and whether there were any.
: pv-prefixes ( c-addr u -- c-addr' u' prefixed? )
  2dup ['] pv-unprefixed? text-scan dup >r /string r> 0<> ;
: pv-numeric-rest? ( c-addr u prefixed? -- flag )
  over 0= if drop 2drop false exit then >r 2dup pv-quote? if 2drop r> drop true exit then
  2dup pv-point? if 1 /string then drop c@ r> pv-numeral? ;
: pv-number-like? ( c-addr u -- flag ) pv-prefixes pv-numeric-rest? ;

\ The run's state.
31 constant pv-name-max          \ longest definition name
32 constant pv-defs-max          \ definitions per file
8 constant pv-frames-max         \ open IF and BEGIN structures
8 constant pv-kept-max           \ tokens before CONSTANT
\ The deepest line is written at level pv-frames-max + 1 (verify-report.fs).
pv-frames-max 1+ 2* pv-indent-chars > [if] .( pv: indentation too short ) abort [then]
0 constant pv-kind-word
1 constant pv-kind-constant
begin-structure /pv-def
  field: pv-def-kind             \ pv-kind-word or pv-kind-constant
  field: pv-def-length
  pv-name-max chars aligned +field pv-def-name   \ folded to lower case
end-structure
pv-defs-max /pv-def aligned store-size constant /pv-defs
\ A token kept until CONSTANT: a primitive (value: its entry), a literal
\ (value: the number) or a call (value: the definition's index), and
\ where it stood.
0 constant pv-kept-prim
1 constant pv-kept-lit
2 constant pv-kept-call
begin-structure /pv-kept
  field: pv-kept-kind
  field: pv-kept-value
  field: pv-kept-pos             \ as lfa-pos
end-structure
1 constant pv-frame-if
2 constant pv-frame-else
3 constant pv-frame-begin
4 constant pv-frame-while
begin-structure /pv-state
  field: pv-state-words          \ the file's word list, new for each run
  field: pv-state-current        \ the definition being compiled, or -1
  field: pv-state-mark           \ where its : stood, as lfa-pos
  field: pv-state-depth          \ open frames
  pv-frames-max cells +field pv-state-frames
  field: pv-state-kept#
  field: pv-state-values         \ cells the kept tokens leave on the data stack
  pv-kept-max /pv-kept * +field pv-state-kept
  /pv-defs +field pv-state-defs
end-structure
/pv-state context-record: pv-state

: pv-words ( -- addr ) pv-state pv-state-words ;
: pv-current ( -- addr ) pv-state pv-state-current ;
: pv-mark ( -- addr ) pv-state pv-state-mark ;
: pv-depth ( -- addr ) pv-state pv-state-depth ;
: pv-frame ( i -- addr ) cells pv-state pv-state-frames + ;
: pv-kept# ( -- addr ) pv-state pv-state-kept# ;
: pv-values ( -- addr ) pv-state pv-state-values ;
: pv-kept ( i -- kept ) /pv-kept * pv-state pv-state-kept + ;
: pv-defs ( -- store ) pv-state pv-state-defs ;
: pv-state-reset ( -- )
  pv-state /pv-state erase wordlist pv-words ! -1 pv-current !
  pv-defs-max /pv-def aligned 0 pv-defs store-init 0= abort" pv: definitions" ;

\ Definitions of the file.
: pv-def ( index -- def ) pv-defs store-slot ;
: pv-def-text ( index -- c-addr u ) pv-def dup pv-def-name swap pv-def-length @ ;
: pv-in-def? ( -- flag ) pv-current @ 0< 0= ;
: pv-constant? ( index -- flag ) pv-def pv-def-kind @ pv-kind-constant = ;
\ The index of a word the file defined, found as Forth finds it.
: pv-file-word ( c-addr u -- index true | false )
  pv-words @ search-wordlist if >body @ true else false then ;
: pv-known? ( c-addr u -- flag ) 2dup pv-entry-of if drop 2drop true exit then
  pv-file-word dup if nip then ;

\ Define the name at offset in the line in the file's word list, as
\ Forth's CREATE reads it from the input source. When Forth's interpreter
\ runs such a word, the design says what it does (pv-word-runs): the
\ separate vocabulary writes the call; the mode shift never lets one run.
: pv-create ( index offset -- )
  pv-prefix# @ + >in ! get-current >r pv-words @ set-current create r> set-current ,
  does> @ pv-word-runs ;

\ The name after a defining word, on the same line, becomes the current
\ token; it must be short, new in any case of letters, and no number.
: pv-name ( -- ) parse-name dup 0= if 2drop pv-why-no-name pv-fail-here then pv-token! ;
: pv-name-check ( -- )
  pv-token-text nip pv-name-max >  pv-why-long-name pv-?fail
  pv-token-text pv-known?          pv-why-redefined pv-?fail
  pv-token-text pv-number-like?    pv-why-number-name pv-?fail ;
\ A definition's name, folded to lower case.
: pv-def-name! ( c-addr u def -- )
  2dup pv-def-length ! pv-def-name swap 2dup 2>r chars move 2r> pv-fold ;
: pv-def! ( kind def -- ) tuck pv-def-kind ! pv-token-text rot pv-def-name! ;
: pv-new-def ( kind -- index )
  pv-defs store-new-slot 0= if drop pv-why-capacity pv-fail then >r pv-def! r> ;
: pv-define ( kind -- index ) pv-name pv-name-check pv-new-def dup pv-token @ pv-create ;

\ Writing instructions: at the current level inside a definition.
: pv-line-start ( c-addr u -- ) pv-depth @ 1+ pv-indent pv-append ;
: pv-keyword ( c-addr u level -- ) pv-indent pv-append pv-done ;
: pv-call-text ( index -- ) pv-def-text pv-append ;

\ Outside a definition: the cells the kept tokens leave, counted with each
\ primitive's effect; taking more than the file gave would take values
\ the caller left, which the IR does not model.
: pv-take ( taken given -- )
  over pv-values @ > pv-why-borrowed pv-?fail swap - pv-values +! ;
: pv-kept! ( value kind kept -- )
  tuck pv-kept-kind ! tuck pv-kept-value ! pv-here lfa-pos swap pv-kept-pos ! ;
: pv-keep ( value kind -- )
  pv-kept# @ pv-kept-max < 0= pv-why-capacity pv-?fail
  pv-kept# @ pv-kept pv-kept! 1 pv-kept# +! ;

\ Literals, calls and primitives. Outside a definition each is kept, a
\ literal and a constant's call giving one cell.
: pv-keep-one ( value kind -- ) 0 1 pv-take pv-keep ;
: pv-lit-inside ( n -- ) s" lit " pv-line-start pv-number pv-done ;
: pv-lit ( n -- ) pv-in-def? if pv-lit-inside else pv-kept-lit pv-keep-one then ;
\ A word is visible inside its own definition, but Gforth hides it until
\ ; so a call there would be of an earlier word of that name.
: pv-call-inside ( index -- )
  dup pv-current @ = pv-why-recursive pv-?fail
  s" call " pv-line-start pv-call-text pv-done ;
: pv-call-top ( index -- )
  dup pv-constant? 0= pv-why-outside pv-?fail pv-kept-call pv-keep-one ;
: pv-call ( index -- ) pv-in-def? if pv-call-inside else pv-call-top then ;
: pv-effect ( entry -- taken given ) pv-entry-datum @ 10 /mod swap ;
\ Gforth runs the tokens before CONSTANT while it loads the file: a
\ division can stop the load (THROW -10, -11) where the IR divides only
\ when the constant is called; >R R> R@ are modelled only in definitions.
: pv-top-refused ( kind -- )
  case pv-kind-rstack of pv-why-outside pv-fail endof
    pv-kind-divide of pv-why-dividing pv-fail endof endcase ;
: pv-prim-top ( entry -- )
  dup pv-entry-kind @ pv-top-refused dup pv-effect pv-take pv-kept-prim pv-keep ;
: pv-prim-inside ( entry -- ) s" prim " pv-line-start pv-entry-text pv-append pv-done ;
: pv-prim ( entry -- ) pv-in-def? if pv-prim-inside else pv-prim-top then ;
\ A table entry's verification semantics.
: pv-perform ( entry -- )
  dup pv-entry-kind @ case
    pv-kind-action of pv-entry-datum @ execute endof
    pv-kind-reserved of drop pv-why-not-ir pv-fail endof
    swap pv-prim endcase ;

\ Structure: each word writes its line and keeps the frames.
: pv-inside ( -- ) pv-in-def? 0= pv-why-outside pv-?fail ;
: pv-top-only ( -- ) pv-in-def? pv-why-inside pv-?fail ;
: pv-unbalanced? ( flag -- ) pv-why-unbalanced pv-?fail ;
: pv-top ( -- addr ) pv-depth @ 1- pv-frame ;
: pv-top? ( frame -- flag ) pv-depth @ if pv-top @ = else drop false then ;
: pv-push ( frame -- )
  pv-depth @ pv-frames-max < 0= pv-why-capacity pv-?fail 1 pv-depth +! pv-top ! ;
: pv-open ( c-addr u frame -- ) >r pv-depth @ 1+ pv-keyword r> pv-push ;
\ ELSE and WHILE turn their IF's or BEGIN's frame into their own, and are
\ written one level out, beside it.
: pv-retag ( from to -- ) swap pv-top? 0= pv-unbalanced? pv-top ! ;
: pv-beside ( c-addr u -- ) pv-depth @ pv-keyword ;
: pv-close ( c-addr u -- ) -1 pv-depth +! pv-depth @ 1+ pv-keyword ;
: pv-if ( -- ) pv-inside s" if" pv-frame-if pv-open ;
: pv-else ( -- ) pv-inside pv-frame-if pv-frame-else pv-retag s" else" pv-beside ;
: pv-if-open? ( -- flag ) pv-frame-if pv-top? pv-frame-else pv-top? or ;
: pv-then ( -- ) pv-inside pv-if-open? 0= pv-unbalanced? s" then" pv-close ;
: pv-begin ( -- ) pv-inside s" begin" pv-frame-begin pv-open ;
\ Forth-2012 allows more WHILEs in one BEGIN, each closed by a THEN after
\ REPEAT; IR 0.1 has one.
: pv-while ( -- )
  pv-inside pv-frame-while pv-top? pv-why-two-whiles pv-?fail
  pv-frame-begin pv-frame-while pv-retag s" while" pv-beside ;
: pv-repeat ( -- )
  pv-inside pv-frame-while pv-top? 0= pv-unbalanced? s" repeat" pv-close ;
: pv-exit ( -- ) pv-inside s" exit" pv-line-start pv-done ;

\ Definitions. The location of `word` is the colon's; of `constant` and
\ its `end`, the constant's name; of a word's `end`, the semicolon.
: pv-no-values-left ( -- ) pv-kept# @ 0<> pv-why-left-over pv-?fail ;
: pv-word-line ( index -- ) s" word " pv-append pv-call-text pv-mark @ pv-done-at ;
: pv-colon ( -- )
  pv-in-def? pv-why-nested pv-?fail pv-no-values-left
  pv-here lfa-pos pv-mark ! pv-kind-word pv-define dup pv-current ! pv-word-line ;
: pv-end ( -- ) s" end" pv-append pv-done ;
: pv-semicolon ( -- ) pv-inside pv-depth @ 0<> pv-unbalanced? pv-end -1 pv-current ! ;
\ A kept token's instruction: there are only three kinds.
: pv-kept-text ( value kind -- )
  case pv-kept-prim of s" prim " pv-append pv-entry-text pv-append endof
    pv-kept-lit of s" lit " pv-append pv-number endof
    pv-kept-call of s" call " pv-append pv-call-text endof
    true abort" pv: kept kind" endcase ;
: pv-replay ( kept -- )
  1 pv-indent dup pv-kept-value @ over pv-kept-kind @ pv-kept-text
  pv-kept-pos @ pv-done-at ;
: pv-replay-all ( -- )
  pv-kept# @ 0 ?do i pv-kept pv-replay loop 0 pv-kept# ! 0 pv-values ! ;
: pv-constant-lines ( index -- )
  s" constant " pv-append pv-call-text pv-done pv-replay-all pv-end ;
\ CONSTANT with nothing before it would take a value from outside the
\ file, as + would.
: pv-constant ( -- )
  pv-top-only pv-kept# @ 0= pv-why-no-value pv-?fail
  pv-values @ 1 <> pv-why-one-value pv-?fail
  pv-kind-constant pv-define pv-constant-lines ;
\ BASE is ten for the whole run, so DECIMAL changes nothing.
: pv-base-ten ( -- ) pv-top-only ;
\ Comments: ( must close on its line; \ ends the line.
: pv-line-end ( -- c-addr ) pv-text chars + ;
: pv-paren ( -- ) [char] ) parse chars + pv-line-end < 0= pv-why-comment pv-?fail ;
: pv-backslash ( -- ) source nip >in ! ;

\ At the end of the text: no definition open, no value left.
: pv-end-of-text ( -- )
  pv-no-token pv-in-def? pv-why-unclosed pv-?fail-here
  pv-kept# @ 0<> pv-why-left-over pv-?fail-here ;

\ The table: the 13 words with an action of their own, the 38 primitives
\ of IR 0.1 in the order of Prim in program-ir.lean, and the reserved
\ names of Forth-2012 Core and Core Ext (\q is a double quote).
' pv-colon s" :" pv-act           ' pv-semicolon s" ;" pv-act
' pv-constant s" constant" pv-act ' pv-base-ten s" decimal" pv-act
' pv-paren s" (" pv-act           ' pv-backslash s" \" pv-act
' pv-if s" if" pv-act             ' pv-else s" else" pv-act
' pv-then s" then" pv-act         ' pv-begin s" begin" pv-act
' pv-while s" while" pv-act       ' pv-repeat s" repeat" pv-act
' pv-exit s" exit" pv-act
12 s" dup" pv-data     10 s" drop" pv-data    22 s" swap" pv-data
23 s" over" pv-data    21 s" nip" pv-data     23 s" tuck" pv-data
33 s" rot" pv-data     24 s" 2dup" pv-data    20 s" 2drop" pv-data
10 s" >r" pv-return    01 s" r>" pv-return    01 s" r@" pv-return
21 s" +" pv-data       21 s" -" pv-data       21 s" *" pv-data
21 s" /" pv-division   21 s" mod" pv-division 11 s" negate" pv-data
11 s" abs" pv-data     11 s" 1+" pv-data      11 s" 1-" pv-data
21 s" =" pv-data       21 s" <>" pv-data      21 s" <" pv-data
21 s" >" pv-data       11 s" 0=" pv-data      11 s" 0<>" pv-data
11 s" 0<" pv-data      11 s" 0>" pv-data      21 s" and" pv-data
21 s" or" pv-data      21 s" xor" pv-data     11 s" invert" pv-data
21 s" rshift" pv-data  21 s" max" pv-data     21 s" min" pv-data
01 s" true" pv-data    01 s" false" pv-data
s\" ! # #> #s ' */ */mod +! +loop , . .\q /mod 2! 2* 2/ 2@ 2over 2swap <# >body >in"
pv-reserve-all
s\" >number ?dup @ abort abort\q accept align aligned allot base bl c! c, c@ cell+"
pv-reserve-all
s\" cells char char+ chars count cr create depth do does> emit environment? evaluate"
pv-reserve-all
s\" execute fill find fm/mod here hold i immediate j key leave literal loop lshift m*"
pv-reserve-all
s\" move postpone quit recurse s\q s>d sign sm/rem source space spaces state type u."
pv-reserve-all
s\" u< um* um/mod unloop until variable word [ ['] [char] ]" pv-reserve-all
s\" .( .r 2>r 2r> 2r@ :noname ?do action-of again buffer: c\q case compile, defer"
pv-reserve-all
s\" defer! defer@ endcase endof erase hex holds is marker of pad parse parse-name pick"
pv-reserve-all
s\" refill restore-input roll s\\\q save-input source-id to u.r u> unused value within"
pv-reserve-all
s\" [compile]" pv-reserve-all

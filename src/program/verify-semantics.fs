\ Verification semantics of IR 0.2 (ADR 0019 §1-§3 and Amendment 1): what
\ each Forth word does in correctness mode, for the mode shift. `DUP`
\ writes `prim dup`; `:` reads its name, as Forth's `:` does, defines it in
\ the file's own word list and writes `word NAME`, leaving Forth
\ interpreting; `IF` writes `if` and opens a frame; `.` writes `out .`; a
\ word of the file writes `call NAME`; a number writes `lit n`. Inside a
\ definition each instruction is written at once, one level deeper per
\ open frame; outside one, the tokens before CONSTANT are kept and written
\ as its body. The structure frames live here, never on the data stack, so
\ no number can stand for one. A word refuses what IR 0.2 does not model,
\ with the reasons of verify-report.fs.
\
\ The words with verification semantics are a table, pv-names, keyed by
\ name (A-Z read as a-z, as Gforth finds names): the 40 primitives of IR
\ 0.2 (in the order of Prim in tests/reference/program-ir.lean, each with
\ its data-stack effect: taken, then given, as two digits), the 7 output
\ words (each with the cells it takes), the 16 words with an action of
\ their own, and every other name of Forth-2012's Core and Core Ext word
\ sets, reserved: such a word refuses ("a Forth word outside IR 0.2") and
\ no file may redefine it. Each entry also keeps the execution token that
\ FORTH-WORDLIST gave for its name when this file loaded: its identity, by
\ which the mode shift (verify.fs) knows the host's own word; and whether
\ it is new in IR 0.2 (lshift, -rot and the output words), whose lines make
\ the run's IR 0.2. `-rot` and `.S` are no Core words, but both Gforths
\ have them; src/lib/portability.fs defines `-rot` as `rot rot` on a Forth
\ without it, which run mode must load first there.
\
\ Calls are bound early, as Forth binds them (Amendment 1, A1): Forth's own
\ lookup finds the version of a word of the file visible at that point. A
\ file may define its own words again, in any case of letters; each
\ version gets its own IR name, the name folded to lower case, then 'k for
\ its k-th redefinition (x, x'1, x'2), and a call names the version it
\ reaches. A definition is hidden until its ; as in Forth, so its own name
\ inside it means the version before it (none: "recursive call"). A name
\ the IR already gives another version (x'1 after x twice) is refused, so
\ IR names are unique; standard words may not be redefined; names that
\ read as numbers are refused (owner's answer 4).
\
\ Untrusted, like verify-report.fs. State: one context record, pv-state,
\ reset for each run, and the table, read-only once this file has loaded.
\ Every run grows the dictionary: a word list, and a word for each
\ definition.

require ../lib/lib.fs
require ../lib/decimal.fs
require ../lib/text-run.fs
require ../author/source.fs
require ./verify-report.fs

\ Kinds of table entries.
0 constant pv-kind-data          \ an IR primitive on the data stack: dup, +, max ...
1 constant pv-kind-rstack        \ an IR primitive on the return stack: >r r> r@
2 constant pv-kind-divide        \ / and mod, which can throw on the host
3 constant pv-kind-action        \ a word with an action of its own: : ; if ...
4 constant pv-kind-reserved      \ a standard word outside IR 0.2
5 constant pv-kind-output        \ an output word: . u. cr emit space spaces .s

16 constant pv-entry-chars       \ longest name in the table
begin-structure /pv-entry
  field: pv-entry-kind
  field: pv-entry-datum          \ a primitive's effect, output cells, an action's xt
  field: pv-entry-host           \ the xt FORTH-WORDLIST gave for the name, or 0
  field: pv-entry-new            \ true for a word new in IR 0.2
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
: pv-table-name? ( c-addr u -- flag ) pv-entry-of dup if nip then ;

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
\ The entry made last is new in IR 0.2.
: pv-ir-0.2 ( -- ) true pv-names store-count @ 1- pv-entry pv-entry-new ! ;
: pv-output ( cells c-addr u -- ) pv-name, pv-kind-output pv-typed pv-ir-0.2 ;

\ Literals (Amendment 1, A3): Forth-2012's numbers, read here with BASE
\ ten, never by the host: [-]decimal digits, #[-]decimal digits,
\ $[-]hexadecimal digits (either case), %[-]binary digits, or 'c' for one
\ printable character, from -2^31 to 2^32 - 1, so that every 32-bit word,
\ signed or unsigned, can be written. At most 10 decimal, 8 hexadecimal or
\ 32 binary digits, so that leading zeros stay limited as before. The value
\ is a double, exact on 32-bit hosts too. Refused: a sign before a prefix
\ (-$10, which Forth-2012 does not define, and which Gforth 1.0 reads or
\ not depending on the number it read before) or before 'c', Gforth's
\ digit separator (1_000), 0x10, double numbers (1.) and every other form.
\ tests/program/verify_ir02.py compares this reading with both Gforths'
\ own on many tokens.
: pv-letter? ( char -- flag ) pv-lower [char] a [char] z 1+ within ;
\ The value of a digit or letter, 99 for any other character.
: pv-digit-value ( char -- n )
  dup decimal-digit? if [char] 0 - exit then
  dup pv-letter? if pv-lower [char] a - 10 + else drop 99 then ;
: pv-in-base? ( char base -- n true | false )
  swap pv-digit-value tuck > if true else drop false then ;
\ d times base plus n.
: pv-d*+ ( d base n -- d' ) >r tuck * >r um* r> + r> 0 d+ ;
: pv-digit+ ( d char base -- d' true | false )
  tuck pv-in-base? if pv-d*+ true else drop 2drop false then ;
\ The value of the digits c-addr u in base, or false at a character that
\ is no digit of it.
: pv-digits ( c-addr u base -- d true | false )
  -rot 0 0 2swap chars over + swap ?do
    2 pick i c@ swap pv-digit+ 0= if drop unloop false exit then
  1 chars +loop rot drop true ;
\ A radix: the base of a prefix's digits and how many there may be.
begin-structure /pv-radix
  field: pv-radix-base
  field: pv-radix-digits
end-structure
: pv-radix, ( base digits "name" -- ) create swap , , ;
10 10 pv-radix, pv-radix-10      16 8 pv-radix, pv-radix-16
2 32 pv-radix, pv-radix-2
\ The radix a prefix character names, or 0.
: pv-radix ( char -- radix|0 )
  case [char] # of pv-radix-10 endof [char] $ of pv-radix-16 endof
    [char] % of pv-radix-2 endof >r 0 r> endcase ;
\ One digit to the radix's most.
: pv-few? ( u radix -- flag ) pv-radix-digits @ 1+ 1 swap within ;
: pv-numeral ( c-addr u radix -- d true | false )
  2dup pv-few? if pv-radix-base @ pv-digits else 2drop drop false then ;
: pv-negative ( c-addr u -- c-addr' u' flag )
  dup if over c@ [char] - = if 1 /string true exit then then false ;
\ The largest magnitude: 2^31 below zero, 2^32 - 1 above.
: pv-limit ( negative? -- d ) if 32768 65536 um* else 65536 65536 um* 1 0 d- then ;
: pv-in-range? ( d negative? -- d' true | false )
  dup >r pv-limit 2over du< if 2drop r> drop false exit then r> if dnegate then true ;
: pv-signed ( c-addr u radix -- d true | false )
  >r pv-negative r> swap >r pv-numeral if r> pv-in-range? else r> drop false then ;
\ After a prefix, or without one.
: pv-prefixed ( c-addr u -- d true | false )
  dup 0= if 2drop false exit then
  over c@ pv-radix ?dup if >r 1 /string r> else pv-radix-10 then pv-signed ;
: pv-quote-char? ( c-addr -- flag ) c@ [char] ' = ;
: pv-char-literal? ( c-addr u -- d true | false )
  3 <> if drop false exit then
  dup pv-quote-char? over 2 chars + pv-quote-char? and 0= if drop false exit then
  char+ c@ dup bl 1+ 127 within if 0 true else drop false then ;
: pv-literal? ( c-addr u -- d true | false )
  2dup pv-char-literal? if 2swap 2drop true exit then pv-prefixed ;

\ Names that read as numbers, refused for every definition: anything that
\ Forth-2012 or Gforth (1.0 or 0.7.3) could read as a number with BASE
\ ten, and more. After any leading signs and base prefixes (+ - # $ % &):
\ a digit; Gforth 1.0's digit separator _; a quote and one more character
\ ('c', Gforth's 'c and -'c); after a prefix, a hexadecimal letter, or any
\ letter before a digit or a point (Gforth 1.0 reads -k1 and +M5 as floats,
\ an SI prefix standing for the point); or a point before a digit, _ or a
\ prefixed hexadecimal letter (Gforth 1.0 reads .5 as a float, ._ and $.a
\ as numbers). So 5, -0, 1e, $10, 'a', -'a', .5, _1, -_1, #_1 and -k1 are
\ refused, and ->x, "x" and x:dup are names. tests/program/verify.fs
\ checks the rule against the running Gforth: every token of one to three
\ printable characters that it reads with an empty search order must be
\ refused here.
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
  over pv-hex-letter? and over [char] _ = or swap decimal-digit? or ;
\ A letter before a digit or a point: Gforth 1.0's float with an SI prefix.
: pv-si-float? ( c-addr u -- flag )
  1 > if dup c@ pv-letter? swap char+ c@ dup decimal-digit? swap [char] . = or and
  else drop false then ;
\ A rest that is a number by its first two characters: a quote and one
\ more, or, after a prefix, an SI float.
: pv-two-char-number? ( c-addr u prefixed? -- flag )
  >r 2dup pv-quote? r> if >r pv-si-float? r> or else nip nip then ;
\ The rest after the signs and prefixes, and whether there were any.
: pv-prefixes ( c-addr u -- c-addr' u' prefixed? )
  2dup ['] pv-unprefixed? text-scan dup >r /string r> 0<> ;
: pv-numeric-rest? ( c-addr u prefixed? -- flag )
  over 0= if drop 2drop false exit then
  >r 2dup r@ pv-two-char-number? if 2drop r> drop true exit then
  2dup pv-point? if 1 /string then drop c@ r> pv-numeral? ;
: pv-number-like? ( c-addr u -- flag ) pv-prefixes pv-numeric-rest? ;

\ The run's state.
31 constant pv-name-max          \ longest definition name in the source
32 constant pv-defs-max          \ definitions per file, each version counted
36 constant pv-ir-name-max       \ longest IR name: a source name, ' and a version
8 constant pv-frames-max         \ open IF and BEGIN structures
8 constant pv-kept-max           \ tokens before CONSTANT
\ The deepest line is written at level pv-frames-max + 1 (verify-report.fs).
pv-frames-max 1+ 2* pv-indent-chars > [if] .( pv: indentation too short ) abort [then]
pv-defs-max 100 < 0= [if] .( pv: version numbers too long ) abort [then]
0 constant pv-kind-word
1 constant pv-kind-constant
begin-structure /pv-def
  field: pv-def-kind             \ pv-kind-word or pv-kind-constant
  field: pv-def-prev             \ the version of the name this one replaces, or -1
  field: pv-def-version          \ 0 for a name's first definition, k for its k-th
  field: pv-def-length
  pv-ir-name-max chars aligned +field pv-def-name   \ the IR name
end-structure
pv-defs-max /pv-def aligned store-size constant /pv-defs
\ A token kept until CONSTANT: a primitive (value: its entry), a literal
\ (value and high: the number, a double) or a call (value: the
\ definition's index), and where it stood.
0 constant pv-kept-prim
1 constant pv-kept-lit
2 constant pv-kept-call
begin-structure /pv-kept
  field: pv-kept-kind
  field: pv-kept-value
  field: pv-kept-high
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
: pv-def-chars ( def -- c-addr u ) dup pv-def-name swap pv-def-length @ ;
: pv-def-text ( index -- c-addr u ) pv-def pv-def-chars ;
: pv-in-def? ( -- flag ) pv-current @ 0< 0= ;
: pv-constant? ( index -- flag ) pv-def pv-def-kind @ pv-kind-constant = ;
\ The index of the version of a word of the file visible now, found as
\ Forth finds it: its newest header.
: pv-file-word ( c-addr u -- index true | false )
  pv-words @ search-wordlist if >body @ true else false then ;

\ Define the name at offset in the line in the file's word list, as
\ Forth's CREATE reads it from the input source. When Forth's interpreter
\ runs such a word, the design says what it does (pv-word-runs): the
\ mode shift never lets one run.
: pv-create ( index offset -- )
  pv-prefix# @ + >in ! get-current >r pv-words @ set-current create r> set-current ,
  does> @ pv-word-runs ;

\ The name after a defining word, on the same line, becomes the current
\ token; it must be short, no standard word in any case of letters, and no
\ number. A name of the file's own may be defined again.
: pv-name ( -- ) parse-name dup 0= if 2drop pv-why-no-name pv-fail-here then pv-token! ;
: pv-name-check ( -- )
  pv-token-text nip pv-name-max >  pv-why-long-name pv-?fail
  pv-token-text pv-table-name?     pv-why-redefined pv-?fail
  pv-token-text pv-number-like?    pv-why-number-name pv-?fail ;
\ The definition's IR name: the token folded to lower case, then 'k for
\ the k-th redefinition of that name.
: pv-def+ ( c-addr u def -- def )
  >r r@ pv-def-chars chars + swap dup >r chars move r> r@ pv-def-length +! r> ;
: pv-suffix+ ( def k -- ) >r s" '" rot pv-def+ r> n>decimal rot pv-def+ drop ;
: pv-version-suffix ( def -- ) dup pv-def-version @ ?dup if pv-suffix+ else drop then ;
: pv-name-folded ( def -- def ) dup pv-def-chars pv-fold ;
: pv-ir-name! ( def -- )
  0 over pv-def-length ! >r pv-token-text r> pv-def+ pv-name-folded pv-version-suffix ;
\ The version the token's new definition replaces, if any, and its number.
: pv-replaced ( -- index|-1 ) pv-token-text pv-file-word 0= if -1 then ;
: pv-version-of ( prev -- k ) dup 0< if drop 0 else pv-def pv-def-version @ 1+ then ;
: pv-def! ( kind def -- )
  tuck pv-def-kind ! pv-replaced 2dup swap pv-def-prev ! pv-version-of
  over pv-def-version ! pv-ir-name! ;
\ Whether an earlier definition has the IR name of def, the newest.
: pv-same-name? ( def index -- flag ) pv-def-text rot pv-def-chars compare 0= ;
: pv-same-name-at? ( def index -- def flag ) over swap pv-same-name? ;
: pv-name-taken? ( def -- flag )
  pv-defs store-count @ 1- ['] pv-same-name-at? any? nip ;
: pv-new-def ( kind -- index )
  pv-defs store-new-slot 0= if drop pv-why-capacity pv-fail then
  >r tuck pv-def! pv-name-taken? pv-why-version-name pv-?fail r> ;
: pv-define ( kind -- index ) pv-name pv-name-check pv-new-def dup pv-token @ pv-create ;

\ Writing instructions: at the current level inside a definition.
: pv-line-start ( c-addr u -- ) pv-depth @ 1+ pv-indent pv-append ;
: pv-keyword ( c-addr u level -- ) pv-indent pv-append pv-done ;
: pv-call-text ( index -- ) pv-def-text pv-append ;
\ A primitive: its line marks the IR as 0.2 when the primitive is new.
: pv-prim-text ( entry -- )
  s" prim " pv-append dup pv-entry-new @ if pv-new-ir then pv-entry-text pv-append ;

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
: pv-lit-inside ( d -- ) s" lit " pv-line-start pv-number-d pv-done ;
: pv-lit-top ( d -- ) >r pv-kept-lit pv-keep-one r> pv-kept# @ 1- pv-kept pv-kept-high ! ;
: pv-lit ( d -- ) pv-in-def? if pv-lit-inside else pv-lit-top then ;
\ A word is hidden inside its own definition until its ; (Forth's
\ hiding): its name there means the version before it, if any.
: pv-visible ( index -- index' )
  dup pv-current @ = if pv-def pv-def-prev @ dup 0< pv-why-recursive pv-?fail then ;
: pv-call-inside ( index -- ) pv-visible s" call " pv-line-start pv-call-text pv-done ;
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
: pv-prim-inside ( entry -- ) pv-depth @ 1+ pv-indent pv-prim-text pv-done ;
: pv-prim ( entry -- ) pv-in-def? if pv-prim-inside else pv-prim-top then ;

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
\ REPEAT; IR 0.2 has one.
: pv-while ( -- )
  pv-inside pv-frame-while pv-top? pv-why-two-whiles pv-?fail
  pv-frame-begin pv-frame-while pv-retag s" while" pv-beside ;
: pv-repeat ( -- )
  pv-inside pv-frame-while pv-top? 0= pv-unbalanced? s" repeat" pv-close ;
: pv-exit ( -- ) pv-inside s" exit" pv-line-start pv-done ;

\ Output words (Amendment 1, A2), only inside definitions: `.` writes
\ `out .`, its stack effect only taking one cell; what it prints is an
\ event, which no stack proof reads. Every out line makes the IR 0.2.
: pv-out-line ( -- ) s" out " pv-line-start pv-new-ir ;
: pv-out-word ( entry -- ) pv-inside pv-out-line pv-entry-text pv-append pv-done ;
\ ." text" and S" text" TYPE write out ." text": the text after the one
\ blank that ends the word, up to the next quote, which must close it on
\ the same line; a tab in it is refused, since IR text holds none. S"
\ must be followed at once by TYPE, the host's own as the design knows
\ words; S" anywhere else, TYPE alone, S\" and .( stay refused: a string's
\ address is memory, and .( prints while Forth compiles.
: pv-line-end ( -- c-addr ) pv-text chars + ;
: pv-tab? ( char -- flag ) 9 = ;
: pv-has-tab? ( c-addr u -- flag ) tuck ['] pv-tab? text-scan > ;
: pv-quoted ( -- c-addr u )
  [char] " parse 2dup chars + pv-line-end < 0= pv-why-open-text pv-?fail
  2dup pv-has-tab? pv-why-character pv-?fail ;
: pv-out-text ( c-addr u -- )
  pv-out-line s\" .\q " pv-append pv-append s\" \q" pv-append pv-done ;
: pv-dot-quote ( -- ) pv-inside pv-quoted pv-out-text ;
: pv-type? ( c-addr u -- flag )
  pv-entry-of if pv-entry-text s" type" compare 0= else false then ;
\ The token after S" must be TYPE, refused at S" otherwise; it is then the
\ current token while the design checks it, S" before and after.
: pv-token@ ( -- offset u ) pv-token @ pv-token# @ ;
: pv-token-back ( offset u -- ) pv-token# ! pv-token ! ;
: pv-check-type ( c-addr u -- )
  2dup pv-type? 0= pv-why-not-ir pv-?fail
  2dup pv-token! 2dup pv-entry-of drop pv-design@ pv-design-host @ execute ;
: pv-then-type ( -- ) pv-token@ parse-name pv-check-type pv-token-back ;
: pv-s-quote ( -- ) pv-inside pv-quoted pv-then-type pv-out-text ;
: pv-type-alone ( -- ) pv-why-not-ir pv-fail ;

\ A table entry's verification semantics; a reserved entry's is a
\ refusal (the mode shift refuses those before, in pv-shift-entry of
\ verify.fs, so this arm is defence in depth: no reserved entry is ever
\ written as IR).
: pv-perform ( entry -- )
  dup pv-entry-kind @ case
    pv-kind-action of pv-entry-datum @ execute endof
    pv-kind-reserved of drop pv-why-not-ir pv-fail endof
    pv-kind-output of pv-out-word endof swap pv-prim endcase ;

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
: pv-kept-lit-text ( kept -- )
  s" lit " pv-append dup pv-kept-value @ swap pv-kept-high @ pv-number-d ;
: pv-kept-call-text ( kept -- ) s" call " pv-append pv-kept-value @ pv-call-text ;
: pv-kept-text ( kept -- )
  dup pv-kept-kind @ case pv-kept-prim of pv-kept-value @ pv-prim-text endof
    pv-kept-lit of pv-kept-lit-text endof pv-kept-call of pv-kept-call-text endof
    true abort" pv: kept kind" endcase ;
: pv-replay ( kept -- ) 1 pv-indent dup pv-kept-text pv-kept-pos @ pv-done-at ;
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
: pv-paren ( -- ) [char] ) parse chars + pv-line-end < 0= pv-why-comment pv-?fail ;
: pv-backslash ( -- ) source nip >in ! ;

\ At the end of the text: no definition open, no value left.
: pv-end-of-text ( -- )
  pv-no-token pv-in-def? pv-why-unclosed pv-?fail-here
  pv-kept# @ 0<> pv-why-left-over pv-?fail-here ;

\ The table: the 16 words with an action of their own, the 40 primitives
\ of IR 0.2 in the order of Prim in program-ir.lean (the last two new in
\ IR 0.2), the 7 output words with the cells each takes, and the reserved
\ names of Forth-2012 Core and Core Ext (\q is a double quote).
' pv-colon s" :" pv-act           ' pv-semicolon s" ;" pv-act
' pv-constant s" constant" pv-act ' pv-base-ten s" decimal" pv-act
' pv-paren s" (" pv-act           ' pv-backslash s" \" pv-act
' pv-if s" if" pv-act             ' pv-else s" else" pv-act
' pv-then s" then" pv-act         ' pv-begin s" begin" pv-act
' pv-while s" while" pv-act       ' pv-repeat s" repeat" pv-act
' pv-exit s" exit" pv-act
' pv-dot-quote s\" .\q" pv-act    ' pv-s-quote s\" s\q" pv-act
' pv-type-alone s" type" pv-act
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
21 s" lshift" pv-data pv-ir-0.2               33 s" -rot" pv-data pv-ir-0.2
1 s" ." pv-output      1 s" u." pv-output     0 s" cr" pv-output
1 s" emit" pv-output   0 s" space" pv-output  1 s" spaces" pv-output
0 s" .s" pv-output
s\" ! # #> #s ' */ */mod +! +loop , /mod 2! 2* 2/ 2@ 2over 2swap <# >body >in"
pv-reserve-all
s\" >number ?dup @ abort abort\q accept align aligned allot base bl c! c, c@ cell+"
pv-reserve-all
s\" cells char char+ chars count create depth do does> environment? evaluate"
pv-reserve-all
s\" execute fill find fm/mod here hold i immediate j key leave literal loop m*"
pv-reserve-all
s\" move postpone quit recurse s>d sign sm/rem source state"
pv-reserve-all
s\" u< um* um/mod unloop until variable word [ ['] [char] ]" pv-reserve-all
s\" .( .r 2>r 2r> 2r@ :noname ?do action-of again buffer: c\q case compile, defer"
pv-reserve-all
s\" defer! defer@ endcase endof erase hex holds is marker of pad parse parse-name pick"
pv-reserve-all
s\" refill restore-input roll s\\\q save-input source-id to u.r u> unused value within"
pv-reserve-all
s\" [compile]" pv-reserve-all

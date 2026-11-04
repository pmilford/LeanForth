\ Throwaway prototype for ADR 0019 (program words in two modes): the
\ correctness vocabulary of IR 0.1. The same source file that ordinary
\ Forth runs is handed, line by line, to Forth's own text interpreter
\ (EVALUATE) with only two word lists in the search order: this
\ vocabulary, whose words have the names of the Forth words they stand for
\ and emit IR 0.1 when they run, and a fresh word list for the words the
\ file defines, which emit a call. Nothing else is visible. Numbers are
\ read by the interpreter itself; each vocabulary word first checks the
\ text between the previous word and itself (the "gap"): it must be only
\ plain decimal literals, as many as the data stack grew, with the values
\ the text says. Those become lit instructions.
\
\ Standard Forth-2012 words only; runs on Gforth 1.0 and 0.7.3. Not
\ reviewed, not part of src/, global variables for brevity.

decimal

\ ---------------------------------------------------------------- outcomes
0 constant cv-ok  1 constant cv-invalid  2 constant cv-unsupported  3 constant cv-full
-4130 constant cv-throw    \ a diagnostic was recorded; unwind to the runner

\ Reasons, numbered and worded as in src/program/ir-reader.fs, plus two.
create cv-reasons 32 cells allot
: cv-reason! ( c-addr u n -- )
  >r here r> cells cv-reasons + ! dup c, here swap dup allot move align ;
: cv-reason ( n -- c-addr u ) cells cv-reasons + @ count ;
s" no diagnostic" 0 cv-reason!
s" not a known word or 32-bit decimal" 1 cv-reason!
s" a Forth word outside IR 0.1" 2 cv-reason!
s" not allowed outside a definition" 3 cv-reason!
s" not allowed inside a definition" 4 cv-reason!
s" unbalanced control structure" 5 cv-reason!
s" a definition inside a definition" 6 cv-reason!
s" definition not closed" 7 cv-reason!
s" comment not closed on its line" 8 cv-reason!
s" recursive call" 9 cv-reason!
s" name already defined" 10 cv-reason!
s" name longer than 31 characters" 11 cv-reason!
s" constant without a value" 12 cv-reason!
s" values left outside a definition" 13 cv-reason!
s" reader capacity exceeded" 14 cv-reason!
s" file not readable or line too long" 15 cv-reason!
s" a character outside printable ASCII" 16 cv-reason!
s" a name must follow on the same line" 17 cv-reason!
s" a second WHILE in one loop" 18 cv-reason!
s" not exactly one value before CONSTANT" 19 cv-reason!
s" takes values from outside the file" 20 cv-reason!
s" a division outside a definition" 21 cv-reason!
s" read stopped by an exception" 26 cv-reason!
s" the host read a literal differently from its text" 27 cv-reason!
s" run while Forth is compiling" 28 cv-reason!
s" a standard word redefined before the run" 29 cv-reason!
29 constant why-replaced
1 constant why-unknown     2 constant why-not-ir      3 constant why-outside
4 constant why-inside      5 constant why-unbalanced  6 constant why-nested
7 constant why-unclosed    8 constant why-comment     9 constant why-recursive
10 constant why-redefined  11 constant why-long-name  12 constant why-no-value
13 constant why-left-over  14 constant why-capacity   15 constant why-unreadable
16 constant why-character  17 constant why-no-name    18 constant why-two-whiles
19 constant why-one-value  20 constant why-borrowed   21 constant why-dividing
26 constant why-interrupted 27 constant why-host-literal 28 constant why-compiling

\ ---------------------------------------------------------------- the line
variable cv-line#          \ number of the line being run, from 1
variable cv-line-addr      \ the line being run
variable cv-line-len
variable cv-synced         \ characters of the line read so far
variable cv-tok            \ offset of the current token
variable cv-tok#           \ and its length
variable cv-base           \ data-stack depth while the run started
variable cv-fbase          \ floating-point depth when the line started
: cv-text ( -- c-addr u ) cv-line-addr @ cv-line-len @ ;
: cv-char ( n -- char ) cv-line-addr @ + c@ ;
: cv-blank? ( char -- flag ) bl 1+ < ;
: cv-col ( -- col ) cv-tok @ 1+ ;
: cv-token ( -- c-addr u ) cv-line-addr @ cv-tok @ + cv-tok# @ ;
[defined] fdepth [if]
: cv-fdepth ( -- n ) fdepth ;
: cv-fclear ( -- ) begin fdepth cv-fbase @ > while fdrop repeat ;
[else]
: cv-fdepth ( -- n ) 0 ;
: cv-fclear ( -- ) ;
[then]

\ ---------------------------------------------------------------- output
create cv-out 160 chars allot
variable cv-out#
variable cv-quiet          \ true: write diagnostics only (for tests)
variable cv-outcome  variable cv-why  variable cv-err-line  variable cv-err-col
: cv+ ( c-addr u -- ) tuck cv-out cv-out# @ + swap move cv-out# +! ;
: cv-n+ ( n -- ) dup abs 0 <# #s rot sign #> cv+ ;
: cv-at+ ( line col -- ) s"  @" cv+ swap cv-n+ s" :" cv+ cv-n+ ;
: cv-indent+ ( level -- ) 0 ?do s"   " cv+ loop ;
variable cv-lines#         \ lines written so far
: cv-line ( -- )
  cv-quiet @ 0= if cv-out cv-out# @ type cr then 0 cv-out# ! 1 cv-lines# +! ;
: cv-outcome. ( outcome -- )
  case cv-invalid of ." invalid" endof cv-unsupported of ." unsupported" endof
    cv-full of ." full" endof endcase ;
\ Record and print the first diagnostic: token c-addr u (empty for none).
: cv-report ( c-addr u col why outcome -- )
  cv-outcome @ cv-ok <> if 2drop 2drop drop exit then
  cv-outcome ! cv-why ! cv-err-col ! cv-line# @ cv-err-line !
  cv-outcome @ cv-outcome. ."  @" cv-err-line @ 0 .r ." :" cv-err-col @ 0 .r ." : "
  cv-why @ cv-reason type dup if ." : " type else 2drop then cr ;
: cv-fail ( c-addr u col why outcome -- ) cv-report cv-throw throw ;
\ The same at the current token.
: cv-refuse ( why outcome -- ) >r >r cv-token cv-col r> r> cv-fail ;
: cv-unsupported! ( why -- ) cv-unsupported cv-refuse ;
: cv-invalid! ( why -- ) cv-invalid cv-refuse ;

\ ---------------------------------------------------------------- definitions
variable cv-in-def         \ true inside a colon definition
variable cv-def            \ body of the word being defined
variable cv-mark           \ column of its :
variable cv-prog           \ the file's own word list, new for each run
variable cv-defs#          \ definitions so far: each one's identity
create cv-ctl 8 cells allot  variable cv-ctl#     \ open IF and BEGIN frames
1 constant f-if  2 constant f-else  3 constant f-begin  4 constant f-while

\ Instructions inside a definition are written at once, one level deeper
\ per open frame; outside, they are kept for CONSTANT, with the number of
\ cells they would leave counted.
8 constant cv-keep-max
create cv-kept cv-keep-max 64 * chars allot
create cv-kept-len cv-keep-max cells allot
variable cv-kept#  variable cv-values
: cv-start ( -- ) cv-in-def @ if cv-ctl# @ 1+ cv-indent+ then ;
: cv-keep ( -- )
  cv-kept# @ cv-keep-max = if why-capacity cv-full cv-refuse then
  cv-out cv-kept cv-kept# @ 64 * chars + cv-out# @ move
  cv-out# @ cv-kept-len cv-kept# @ cells + ! 1 cv-kept# +! 0 cv-out# ! ;
: cv-done ( line col -- ) cv-at+ cv-in-def @ if cv-line else cv-keep then ;
: cv-here ( -- line col ) cv-line# @ cv-col ;
\ Cells taken and given outside a definition; taking more than the file
\ gave would take the caller's values.
: cv-take ( taken given -- )
  over cv-values @ > if why-borrowed cv-unsupported! then swap - cv-values +! ;

\ ---------------------------------------------------------------- literals
\ The only literal syntax: an optional minus sign and 1 to 10 decimal
\ digits, at most 2147483647 in size (src/program/ir-reader.fs's rule).
2147483647 constant cv-lit-max
: cv-digits ( c-addr u -- u true | false )
  dup 1 11 within 0= if 2drop false exit then
  0 0 2swap >number nip if 2drop false exit then
  if drop false exit then dup cv-lit-max u> if drop false else true then ;
: cv-literal? ( c-addr u -- n true | false )
  dup if over c@ [char] - = if 1 /string cv-digits if negate true else false then exit
  then then cv-digits ;

\ Tokens of the gap: the text from offset from to offset to.
variable cv-pos  variable cv-end
: cv-more? ( -- flag ) cv-pos @ cv-end @ < ;
: cv-skip ( -- ) begin cv-more? while cv-pos @ cv-char cv-blank? while 1 cv-pos +! repeat
  then ;
: cv-next ( -- start len )
  cv-skip cv-pos @ begin cv-more? while cv-pos @ cv-char cv-blank? 0= while 1 cv-pos +!
  repeat then cv-pos @ over - ;
create cv-gap-vals 64 cells allot  create cv-gap-at 64 2 * cells allot  variable cv-gap#
: cv-gap! ( n start len -- )
  cv-gap# @ 2* cells cv-gap-at + 2! cv-gap# @ cells cv-gap-vals + ! 1 cv-gap# +! ;
\ Every token of the gap must be a literal; the first that is not stops
\ the run at that token.
: cv-gap-token ( start len -- )
  2dup swap cv-line-addr @ + swap cv-literal? if -rot cv-gap! exit then
  cv-tok# ! cv-tok ! why-unknown cv-unsupported! ;
: cv-gap-scan ( from to -- )
  cv-end ! cv-pos ! 0 cv-gap# ! begin cv-next dup while cv-gap-token repeat 2drop ;
\ The interpreter pushed one cell per literal, with the value its text
\ gives (BASE is ten). Pop and compare them, last first; no floats.
: cv-taken ( -- )
  depth cv-base @ - cv-gap# @ <> if why-host-literal cv-invalid! then
  cv-gap# @ 0 ?do cv-gap# @ 1- i - cells cv-gap-vals + @ <>
    if why-host-literal cv-invalid! then loop
  cv-fdepth cv-fbase @ <> if why-host-literal cv-invalid! then ;
\ Each literal is the current token while its instruction is made.
: cv-lit ( n -- )
  cv-in-def @ 0= if 0 1 cv-take then cv-start s" lit " cv+ cv-n+ cv-here cv-done ;
\ Hooks, so that another vocabulary (sym.fs) can reuse the runner: what a
\ literal does, what a word of the file does, and the vocabulary itself.
variable cv-lit-xt   ' cv-lit cv-lit-xt !
variable cv-call-xt
variable cv-vocab
: cv-lits ( -- )
  cv-gap# @ 0 ?do i 2* cells cv-gap-at + 2@ cv-tok# ! cv-tok !
    i cells cv-gap-vals + @ cv-lit-xt @ execute loop ;
: cv-gap ( from to -- ) cv-gap-scan cv-taken cv-lits ;

\ ---------------------------------------------------------------- sync
\ The token that invoked the running word: back from >IN over at most one
\ delimiter, then over the token (the interpreter leaves >IN there).
: cv-in ( -- n ) >in @ cv-line-len @ min ;
: cv-token-end ( -- n ) cv-in dup if dup 1- cv-char cv-blank? if 1- then then ;
: cv-token-start ( end -- start )
  begin dup while dup 1- cv-char cv-blank? 0= while 1- repeat then ;
: cv-ours? ( -- flag ) source cv-text rot = >r = r> and ;
\ Run first by every word of the vocabulary and of the file: the gap
\ before the word becomes lit instructions, the word becomes the current
\ token, and the line counts as read up to >IN.
variable cv-word-at  variable cv-word#
: cv-sync ( -- )
  cv-ours? 0= if why-interrupted cv-invalid! then
  cv-token-end dup cv-token-start dup cv-word-at ! - cv-word# !
  cv-synced @ cv-word-at @ cv-gap
  cv-word-at @ cv-tok ! cv-word# @ cv-tok# ! cv-in cv-synced ! ;
: cv-read ( -- ) cv-in cv-synced ! ;     \ after a word that parsed text

\ ---------------------------------------------------------------- the file's words
\ Body of a word the file defines: kind, done flag, identity, name.
0 constant k-word  1 constant k-constant
: pw-kind ( body -- addr ) ;
: pw-done ( body -- addr ) cell+ ;
: pw-id ( body -- addr ) 2 cells + ;
: pw-name ( body -- c-addr u ) 3 cells + dup cell+ swap @ ;
: cv-fold ( c-addr u -- )
  bounds ?do i c@ dup [char] A [char] Z 1+ within if bl or i c! else drop then loop ;
: cv-name, ( c-addr u -- ) dup , here over 2>r here swap dup allot move 2r> cv-fold align ;
: cv-call ( body -- )
  cv-in-def @ if
    dup pw-done @ 0= if drop why-recursive cv-unsupported! then
    cv-start s" call " cv+ pw-name cv+ cv-here cv-done exit then
  dup pw-kind @ k-constant <> if drop why-outside cv-unsupported! then
  0 1 cv-take s" call " cv+ pw-name cv+ cv-here cv-done ;
\ Define the name at offset start of the line in the file's word list, as
\ Forth's CREATE reads it; each such word, when it runs, emits a call of
\ exactly this definition (early binding: Forth's own lookup found it).
variable cv-in-offset      \ where the line starts in Forth's input source
: cv-define ( kind start -- body )
  cv-in-offset @ + >in ! get-current >r cv-prog @ set-current create r> set-current
  here >r , false , 1 cv-defs# +! cv-defs# @ , cv-token cv-name, r>
  does> >r cv-sync r> cv-call-xt @ execute ;
' cv-call cv-call-xt !

\ ---------------------------------------------------------------- vocabulary
wordlist constant cv-words
\ A vocabulary word whose action is xt, run after the gap.
: cv-entry ( xt "name" -- )
  get-current >r cv-words set-current create r> set-current ,
  does> >r cv-sync r> @ execute ;
\ A primitive: its class, its data-stack effect as two digits (taken,
\ given: 2dup is 24) and its name.
0 constant c-data  1 constant c-rstack  2 constant c-divide
: p-class ( body -- addr ) ;  : p-effect ( body -- addr ) cell+ ;
: p-name ( body -- c-addr u ) 2 cells + dup cell+ swap @ ;
: cv-prim ( body -- )
  cv-in-def @ if cv-start s" prim " cv+ p-name cv+ cv-here cv-done exit then
  dup p-class @ c-rstack = if drop why-outside cv-unsupported! then
  dup p-class @ c-divide = if drop why-dividing cv-unsupported! then
  dup p-effect @ 10 /mod swap cv-take s" prim " cv+ p-name cv+ cv-here cv-done ;
: prim: ( effect class "name" -- )
  >in @ parse-name rot >in ! 2>r
  get-current >r cv-words set-current create r> set-current , , 2r> dup , here swap
  dup allot move align
  does> >r cv-sync r> cv-prim ;

\ Names: at most 31 characters, and not known yet in any case of letters.
: cv-known? ( c-addr u -- flag )
  2dup cv-words search-wordlist if drop 2drop true exit then
  cv-prog @ search-wordlist if drop true else false then ;
: cv-name ( -- start ) \ the name after a defining word, made the current token
  parse-name dup 0= if 2drop s" " cv-col why-no-name cv-invalid cv-fail then
  cv-tok# ! cv-line-addr @ - cv-tok !
  cv-tok# @ 31 > if why-long-name cv-unsupported! then
  cv-token cv-known? if why-redefined cv-unsupported! then cv-tok @ ;

: cv-colon ( -- )
  cv-in-def @ if why-nested cv-invalid! then
  cv-kept# @ if why-left-over cv-unsupported! then
  cv-col cv-mark ! cv-name k-word swap cv-define cv-def ! cv-read
  s" word " cv+ cv-def @ pw-name cv+ cv-line# @ cv-mark @ cv-at+ cv-line true cv-in-def ! ;
' cv-colon cv-entry :
: cv-semicolon ( -- )
  cv-in-def @ 0= if why-outside cv-unsupported! then
  cv-ctl# @ if why-unbalanced cv-invalid! then
  s" end" cv+ cv-here cv-at+ cv-line true cv-def @ pw-done ! false cv-in-def ! ;
' cv-semicolon cv-entry ;
: cv-replay ( -- )
  cv-kept# @ 0 ?do s"   " cv+ i 64 * cv-kept + i cells cv-kept-len + @ cv+ cv-line loop
  0 cv-kept# ! 0 cv-values ! ;
: cv-constant ( -- )
  cv-in-def @ if why-inside cv-unsupported! then
  cv-kept# @ 0= if why-no-value cv-unsupported! then
  cv-values @ 1 <> if why-one-value cv-unsupported! then
  cv-name k-constant swap cv-define >r cv-read
  s" constant " cv+ r@ pw-name cv+ cv-here cv-at+ cv-line cv-replay
  s" end" cv+ cv-here cv-at+ cv-line true r> pw-done ! ;
' cv-constant cv-entry constant
: cv-decimal ( -- ) cv-in-def @ if why-inside cv-unsupported! then ;
' cv-decimal cv-entry decimal

\ Comments: ( must close on its line; \ ends the line.
: cv-paren ( -- )
  [char] ) parse + cv-line-addr @ cv-line-len @ + < 0= if why-comment cv-unsupported! then
  cv-read ;
' cv-paren cv-entry (
: cv-backslash ( -- ) cv-line-len @ >in ! cv-read ;
' cv-backslash cv-entry \

\ Control structure: each word writes its line and keeps the structure
\ on its own stack of frames; the data stack never holds a frame, so no
\ literal can stand for one.
: cv-inside ( -- ) cv-in-def @ 0= if why-outside cv-unsupported! then ;
: cv-top ( -- addr ) cv-ctl# @ 1- cells cv-ctl + ;
: cv-top? ( frame -- flag ) cv-ctl# @ if cv-top @ = else drop false then ;
: cv-keyword ( c-addr u level -- ) cv-indent+ cv+ cv-here cv-at+ cv-line ;
: cv-open ( c-addr u frame -- )
  cv-ctl# @ 8 = if why-capacity cv-full cv-refuse then
  >r cv-ctl# @ 1+ cv-keyword 1 cv-ctl# +! r> cv-top ! ;
: cv-turn ( c-addr u from to -- )
  swap cv-top? 0= if why-unbalanced cv-invalid! then cv-top ! cv-ctl# @ cv-keyword ;
: cv-close ( c-addr u -- ) -1 cv-ctl# +! cv-ctl# @ 1+ cv-keyword ;
: cv-if ( -- ) cv-inside s" if" f-if cv-open ;
: cv-else ( -- ) cv-inside s" else" f-if f-else cv-turn ;
: cv-then ( -- )
  cv-inside f-if cv-top? f-else cv-top? or 0= if why-unbalanced cv-invalid! then
  s" then" cv-close ;
: cv-begin ( -- ) cv-inside s" begin" f-begin cv-open ;
: cv-while ( -- )
  cv-inside f-while cv-top? if why-two-whiles cv-unsupported! then
  s" while" f-begin f-while cv-turn ;
: cv-repeat ( -- )
  cv-inside f-while cv-top? 0= if why-unbalanced cv-invalid! then s" repeat" cv-close ;
: cv-exit ( -- ) cv-inside cv-start s" exit" cv+ cv-here cv-done ;
' cv-if cv-entry if          ' cv-else cv-entry else      ' cv-then cv-entry then
' cv-begin cv-entry begin    ' cv-while cv-entry while    ' cv-repeat cv-entry repeat
' cv-exit cv-entry exit

\ The 38 primitives of IR 0.1, in the order of Prim in program-ir.lean.
12 c-data prim: dup     10 c-data prim: drop    22 c-data prim: swap
23 c-data prim: over    21 c-data prim: nip     23 c-data prim: tuck
33 c-data prim: rot     24 c-data prim: 2dup    20 c-data prim: 2drop
10 c-rstack prim: >r    01 c-rstack prim: r>    01 c-rstack prim: r@
21 c-data prim: +       21 c-data prim: -       21 c-data prim: *
21 c-divide prim: /     21 c-divide prim: mod   11 c-data prim: negate
11 c-data prim: abs     11 c-data prim: 1+      11 c-data prim: 1-
21 c-data prim: =       21 c-data prim: <>      21 c-data prim: <
21 c-data prim: >       11 c-data prim: 0=      11 c-data prim: 0<>
11 c-data prim: 0<      11 c-data prim: 0>      21 c-data prim: and
21 c-data prim: or      21 c-data prim: xor     11 c-data prim: invert
21 c-data prim: rshift  21 c-data prim: max     21 c-data prim: min
01 c-data prim: true    01 c-data prim: false

\ Standard words outside IR 0.1: reserved, so that they cannot be
\ redefined and say why they are refused.
: cv-not-ir ( -- ) why-not-ir cv-unsupported! ;
' cv-not-ir cv-entry until   ' cv-not-ir cv-entry again   ' cv-not-ir cv-entry do
' cv-not-ir cv-entry ?do     ' cv-not-ir cv-entry loop    ' cv-not-ir cv-entry +loop
' cv-not-ir cv-entry leave   ' cv-not-ir cv-entry unloop  ' cv-not-ir cv-entry i
' cv-not-ir cv-entry j       ' cv-not-ir cv-entry case    ' cv-not-ir cv-entry of
' cv-not-ir cv-entry endof   ' cv-not-ir cv-entry endcase ' cv-not-ir cv-entry recurse
' cv-not-ir cv-entry variable ' cv-not-ir cv-entry create ' cv-not-ir cv-entry value
' cv-not-ir cv-entry @       ' cv-not-ir cv-entry !       ' cv-not-ir cv-entry lshift

\ ---------------------------------------------------------------- the runner
\ The caller's search order, compilation word list and BASE, restored
\ after every run however it ends.
create cv-saved-order 17 cells allot
variable cv-saved-base  variable cv-saved-current
: cv-save ( -- )
  base @ cv-saved-base ! get-current cv-saved-current !
  get-order dup cv-saved-order ! 0 ?do cv-saved-order i 1+ cells + ! loop ;
: cv-restore ( -- )
  cv-saved-order @ dup 0 ?do cv-saved-order over i - cells + @ swap loop set-order
  cv-saved-current @ set-current cv-saved-base @ base ! ;
cv-words cv-vocab !
: cv-isolate ( -- ) cv-prog @ cv-vocab @ 2 set-order decimal ;

\ Lines: split at LF, one CR before it dropped; every character must be
\ printable ASCII, a space or a tab; fewer than 128 characters.
2variable cv-rest
: cv-eol ( c-addr u -- n )
  dup >r 0 ?do dup i + c@ 10 = if drop i unloop r> drop exit then loop drop r> ;
: cv-cr ( c-addr u -- c-addr u' ) dup if 2dup + 1- c@ 13 = if 1- then then ;
\ The next line, without its LF, and whether an LF ended it.
: cv-split ( -- c-addr n lf? )
  cv-rest 2@ 2dup cv-eol tuck > >r
  cv-rest 2@ 2 pick 1+ over min /string cv-rest 2! r> ;
: cv-odd? ( char -- flag ) dup 9 = if drop false exit then 32 127 within 0= ;
: cv-check-chars ( -- )
  cv-line-len @ 0 ?do i cv-char cv-odd? if
    s" " i 1+ why-character cv-unsupported cv-fail then loop ;
: cv-run-line ( c-addr u -- )
  1 cv-line# +! 0 cv-synced ! 0 cv-out# !
  dup 128 < 0= if 2drop s" " 0 why-unreadable cv-invalid cv-fail then
  cv-line-len ! cv-line-addr ! cv-check-chars cv-fdepth cv-fbase !
  cv-text evaluate cv-synced @ cv-line-len @ cv-gap
  state @ if s" " 0 why-compiling cv-invalid cv-fail then ;
: cv-end-of-text ( -- )
  0 cv-tok ! 0 cv-tok# !
  cv-in-def @ if s" " 0 why-unclosed cv-invalid cv-fail then
  cv-kept# @ if s" " 0 why-left-over cv-unsupported cv-fail then ;
\ A line ended by LF: the CR just before the LF is dropped; any other CR
\ is refused as a character.
: cv-lines ( -- )
  begin cv-rest 2@ nip while cv-split if cv-cr then cv-run-line repeat cv-end-of-text ;
\ After a THROW that is no diagnostic of ours (Forth's -13 for an
\ unknown token, or any other host exception while it read the gap): the
\ first token after the text read so far that is not a plain literal.
: cv-first-odd ( -- start len true | false )
  cv-synced @ cv-pos ! cv-line-len @ cv-end !
  begin cv-next dup while 2dup swap cv-line-addr @ + swap cv-literal?
    if drop 2drop else true exit then repeat 2drop false ;
: cv-caught ( code -- )
  dup cv-throw = if drop exit then drop cv-fclear
  cv-first-odd if over cv-line-addr @ + swap rot 1+ why-unknown cv-unsupported cv-report
    exit then
  s" " 0 why-interrupted cv-invalid cv-report ;
: cv-reset ( -- )
  cv-ok cv-outcome ! 0 cv-why ! 0 cv-line# ! 0 cv-err-line ! 0 cv-err-col !
  false cv-in-def ! 0 cv-ctl# ! 0 cv-kept# ! 0 cv-values ! 0 cv-defs# ! 0 cv-out# !
  0 cv-line-len ! wordlist cv-prog ! ;
\ Run the text c-addr u (lines of a source file) in correctness mode,
\ writing IR 0.1 for path c-addr2 u2; the outcome.
: cv-run ( c-addr u c-addr2 u2 -- outcome )
  cv-reset cv-quiet @ if 2drop else ." lf-ir 0.1" cr ." source " type cr then cv-rest 2!
  state @ if s" " 0 why-compiling cv-invalid cv-report cv-outcome @ exit then
  cv-save cv-isolate depth cv-base ! cv-fdepth cv-fbase !
  ['] cv-lines catch ?dup if cv-caught then cv-restore cv-outcome @ ;

\ Files are read whole, as bytes.
65536 constant cv-file-max
create cv-file cv-file-max allot
: cv-slurp ( c-addr u -- c-addr' u' true | false )
  r/o bin open-file if drop false exit then >r
  cv-file cv-file-max r@ read-file r> close-file drop
  if drop false exit then dup cv-file-max < if cv-file swap true else drop false then ;
: cv-run-file ( c-addr u -- outcome )
  2dup cv-slurp 0= if cv-reset ." lf-ir 0.1" cr ." source " type cr
    s" " 0 why-unreadable cv-invalid cv-report cv-outcome @ exit then
  2swap cv-run ;

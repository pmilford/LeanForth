\ Tests of the program words in correctness mode (ADR 0019): the mode
\ shift (src/program/verify.fs). The golden IR of the six example words
\ and of every primitive; a diagnostic of every kind, with the lines it
\ writes and its verdict; the caller's search order, compilation word
\ list, BASE, STATE and stack depth given back after every kind of
\ ending; a run started while Forth compiles; output words that throw,
\ leave a cell or start another run; a run in another context; and, last,
\ a Forth in which each word with verification semantics was redefined
\ before the run, which the mode shift refuses at that word.
\ tests/program/verify_check.py compares it with today's reader on every
\ reader test and hostile input. The separate vocabulary
\ (src/program/verify-alias.fs), a second design once tested here beside
\ it, was retired on 2026-11-18 and remains in the repository's history.
\ Run from the repository root, like every test file.
include ../support/tester.fs
\ Counted OPEN-FILE and CLOSE-FILE, and a READ-FILE that throws once asked
\ to, as Ctrl-C would: the program words, compiled after them, call them.
variable opened
variable closed
variable interrupt-read
[defined] warnings [if] warnings @ false warnings ! [then]
: open-file ( c-addr u fam -- fileid ior ) open-file dup 0= if 1 opened +! then ;
: close-file ( fileid -- ior ) 1 closed +! close-file ;
: read-file ( c-addr u fileid -- u2 ior )
  interrupt-read @ if false interrupt-read ! -28 throw then read-file ;
\ A small heap, when heap-cap is set: ALLOCATE and RESIZE of more address
\ units than heap-cap fail, as a full heap makes them.
variable heap-cap
: capped? ( u -- flag ) heap-cap @ dup if u> else nip then ;
: allocate ( u -- a-addr ior ) dup capped? if drop 0 -59 exit then allocate ;
: resize ( a-addr u -- a-addr2 ior ) dup capped? if drop -61 exit then resize ;
[defined] warnings [if] warnings ! [then]
: open-files ( -- n ) opened @ closed @ - ;
require ../../src/program/verify.fs
\ Both Gforths warn about the redefinitions below.
[defined] warnings [if] false warnings ! [then]

\ Every line written, each followed by "|", and after a run its verdict.
2048 constant transcript-chars
create transcript transcript-chars chars allot
variable transcript#
: transcribe-text ( c-addr u -- )
  dup transcript# @ + transcript-chars > abort" transcript full"
  transcript transcript# @ chars + swap dup transcript# +! chars move ;
: transcribe ( c-addr u -- ) transcribe-text s" |" transcribe-text ;
: transcript-text ( -- c-addr u ) transcript transcript# @ ;
: transcribed? ( c-addr u -- flag ) transcript-text compare 0= ;
: contains? ( c-addr u c-addr2 u2 -- flag ) search nip nip ;
' transcribe lf-verify-to

: verdict ( outcome -- outcome reason line column ) lf-verify-reason lf-verify-where ;
: n+ ( u -- ) 0 <# #s #> transcribe-text s"  " transcribe-text ;
: noted ( outcome -- outcome ) dup n+ lf-verify-reason n+ lf-verify-where swap n+ n+ ;
: shift-run ( c-addr u -- outcome ) 0 transcript# ! s" t.fs" lf-verify-text noted ;
\ The text's verdict; its lines are in the transcript.
: checked ( c-addr u -- outcome reason line column ) shift-run verdict ;

\ Golden files: every line written must equal the next line of the file.
variable golden-file
variable golden-misses
create golden-text 256 chars allot
: golden-next ( -- c-addr u flag )
  golden-text 254 golden-file @ read-line throw golden-text -rot ;
: golden-miss ( c-addr u c-addr u -- )
  ." expected: " type cr ." got:      " type cr 1 golden-misses +! ;
: golden-check ( c-addr u -- )
  golden-next 0= if 2drop s" (end of file)" golden-miss exit then
  2over 2over compare if golden-miss else 2drop 2drop then ;
: golden ( c-addr u -- ) r/o open-file throw golden-file ! 0 golden-misses ! ;
: golden-end ( -- misses )
  golden-next nip nip if 1 golden-misses +! then
  golden-file @ close-file throw golden-misses @ ;
\ Source c-addr u against its golden IR c-addr2 u2, read by xt.
: against ( c-addr u c-addr2 u2 xt -- outcome misses )
  >r golden ['] golden-check lf-verify-to r> execute golden-end
  ['] transcribe lf-verify-to ;
: shift-golden ( c-addr u c-addr2 u2 -- outcome misses ) ['] lf-verify-file against ;

T{ s" src/program/clamp.fs" s" tests/program/ir/clamp.ir" shift-golden -> outcome-ok 0 }T
T{ s" src/program/examples.fs" s" tests/program/ir/examples.ir" shift-golden
   -> outcome-ok 0 }T
T{ s" tests/program/ir/all-primitives.fs" s" tests/program/ir/all-primitives.ir"
   shift-golden -> outcome-ok 0 }T
T{ s" tests/program/ir/ir-0.2.fs" s" tests/program/ir/ir-0.2.ir" shift-golden
   -> outcome-ok 0 }T
T{ s" src/program/sha-words.fs" s" tests/program/ir/sha-words.ir" shift-golden
   -> outcome-ok 0 }T

\ Run mode of the SHA-2 helper words (src/program/sha-words.fs), loaded
\ into a word list of their own: FIPS 180-4's values, and the example of
\ tests/reference/sha256-spec.lean (Sigma0(6a09e667) = ce20b47e).
wordlist constant sha-words
get-current sha-words set-current get-order sha-words swap 1+ set-order
s" ../../src/program/sha-words.fs" included
previous set-current
: sha-word ( c-addr u -- xt ) sha-words search-wordlist 0= abort" no such word" ;
: sha ( i*x c-addr u -- j*x ) sha-word execute ;
T{ $6a09e667 s" sha-big-sigma0" sha -> $ce20b47e }T
T{ 1 1 s" sha-rotr" sha $80000000 1 s" sha-rotr" sha -> $80000000 $40000000 }T
T{ $12345678 8 s" sha-rotr" sha $12345678 31 s" sha-rotr" sha -> $78123456 $2468acf0 }T
T{ $ffffffff $12345678 $9abcdef0 s" sha-ch" sha -> $12345678 }T
T{ 0 $12345678 $9abcdef0 s" sha-ch" sha -> $9abcdef0 }T
T{ $ffffffff 0 $12345678 s" sha-maj" sha $f0f0f0f0 $ff00ff00 $ffff0000 s" sha-maj" sha
   -> $12345678 $fff0f000 }T
T{ $ffffffff 7 s" sha-shr" sha 0 s" sha-mask" sha -> $1ffffff 0 $ffffffff }T

\ Accepted text, and every outcome with its reason, line and column.
T{ s" : double ( n -- 2n ) dup + ; \ a comment" checked -> outcome-ok 0 1 0 }T
T{ transcript-text s" lf-ir 0.1|source t.fs|word double @1:1|  prim dup @1:22|" search
   nip nip transcript-text s" |  prim + @1:26|end @1:28|0 0 1 0 " search nip nip
   -> true true }T
T{ s" 3 constant three  : f three ;" checked -> outcome-ok 0 1 0 }T
T{ transcript-text s" |constant three @1:12|  lit 3 @1:1|end @1:12|" contains? -> true }T
\ Text lines end at LF; a CR just before it is dropped, any other refused.
T{ s\" : f 1 ;\r\n: g f ;\r\n" checked -> outcome-ok 0 2 0 }T
T{ s\" : f 1 ;\r\r\n" checked -> outcome-unsupported pv-why-character 1 8 }T
T{ s" : f   foo ;" checked -> outcome-unsupported pv-why-unknown 1 7 }T
T{ transcript-text s" |unsupported @1:7: not a known word or 32-bit decimal: foo|"
   contains? -> true }T
T{ s" : f begin dup until ;" checked -> outcome-unsupported pv-why-not-ir 1 15 }T
T{ s" : f then ;" checked -> outcome-invalid pv-why-unbalanced 1 5 }T
T{ s" : f dup" checked -> outcome-invalid pv-why-unclosed 1 0 }T
T{ s" :" checked -> outcome-invalid pv-why-no-name 1 1 }T
T{ s" 1 2 3 4 5 6 7 8 9 constant x" checked -> outcome-full pv-why-capacity 1 17 }T
\ Names that read as numbers are refused (owner's answer 4); names in
\ Gforth's other syntaxes are names.
T{ s" : 5 7 ;" checked -> outcome-unsupported pv-why-number-name 1 3 }T
T{ s" 9 constant -0" checked -> outcome-unsupported pv-why-number-name 1 12 }T
T{ s" : f 1 ; : 1e f ;" checked -> outcome-unsupported pv-why-number-name 1 11 }T
T{ s" : ->x 4 ;  : forth:dup 5 ; : g ->x forth:dup ;" checked -> outcome-ok 0 1 0 }T
T{ transcript-text s" |  call ->x @1:32|  call forth:dup @1:36|" contains? -> true }T
\ Forth-2012 Core and Core Ext words are reserved: refused where used,
\ and not to be redefined.
T{ s" : f 1 cells ;" checked -> outcome-unsupported pv-why-not-ir 1 7 }T
T{ s" : . drop ;" checked -> outcome-unsupported pv-why-redefined 1 3 }T
T{ s\" : f s\" x\" ;" checked -> outcome-unsupported pv-why-not-ir 1 5 }T
T{ s\" : f s\\\" x\" ;" checked -> outcome-unsupported pv-why-not-ir 1 5 }T
\ Every number syntax but Forth-2012's (decimals, # $ % and 'c', ADR 0019
\ A3) is refused at its token, also those that Gforth 1.0's recognizers
\ read; so are its other forms.
T{ s" : f -$10 ;" checked -> outcome-unsupported pv-why-unknown 1 5 }T
T{ s" : f 1e ;" checked -> outcome-unsupported pv-why-unknown 1 5 }T
T{ s\" : f \"x dup y\" ;" checked -> outcome-unsupported pv-why-unknown 1 5 }T
T{ s" : f ${HOME} ;" checked -> outcome-unsupported pv-why-unknown 1 5 }T
T{ s" : f ->dup ;" checked -> outcome-unsupported pv-why-unknown 1 5 }T
T{ s" : f 1 2 forth:dup ;" checked -> outcome-unsupported pv-why-unknown 1 9 }T
T{ transcript-text s" |  lit 1 @1:5|  lit 2 @1:7|unsupported @1:9" contains? -> true }T

\ IR 0.2 (ADR 0019 Amendment 1). Literals (A3): Forth-2012's # $ % and
\ 'c' forms and 32-bit values, read here and written in decimal; they are
\ not new instructions, so the IR stays 0.1.
T{ s" : f #10 $-10 %101 'a' ''' ;" checked -> outcome-ok 0 1 0 }T
T{ transcript-text s" lf-ir 0.1|source t.fs|word f @1:1|  lit 10 @1:5|  lit -16 @1:9|"
   contains? -> true }T
T{ transcript-text s" |  lit 5 @1:14|  lit 97 @1:19|  lit 39 @1:23|end @1:27|" contains?
   -> true }T
T{ s" : f $FFFFFFFF 4294967295 -2147483648 $-80000000 %-1 $ffffffff ;" checked
   -> outcome-ok 0 1 0 }T
T{ transcript-text s" |  lit 4294967295 @1:5|  lit 4294967295 @1:15|  lit -2147483648 @1:26|"
   contains? -> true }T
T{ transcript-text s" |  lit -2147483648 @1:38|  lit -1 @1:49|  lit 4294967295 @1:53|"
   contains? -> true }T
T{ s" 4294967295 constant m  : f m ;" checked -> outcome-ok 0 1 0 }T
T{ transcript-text s" |constant m @1:21|  lit 4294967295 @1:1|end @1:21|" contains? -> true }T
\ Outside the range, too many digits, and the forms Forth-2012 lacks or
\ on which the hosts differ.
T{ s" : f 4294967296 ;" checked -> outcome-unsupported pv-why-unknown 1 5 }T
T{ s" : f -2147483649 ;" checked -> outcome-unsupported pv-why-unknown 1 5 }T
T{ s" : f $100000000 ;" checked -> outcome-unsupported pv-why-unknown 1 5 }T
T{ s" : f $-80000001 ;" checked -> outcome-unsupported pv-why-unknown 1 5 }T
T{ s" : f %111111111111111111111111111111111 ;" checked
   -> outcome-unsupported pv-why-unknown 1 5 }T
T{ s" : f 00004294967295 ;" checked -> outcome-unsupported pv-why-unknown 1 5 }T
T{ s" : f 1_000 ;" checked -> outcome-unsupported pv-why-unknown 1 5 }T
T{ s" : f 0x10 ;" checked -> outcome-unsupported pv-why-unknown 1 5 }T
T{ s" : f -'a' ;" checked -> outcome-unsupported pv-why-unknown 1 5 }T
T{ s" : f 'ab' ;" checked -> outcome-unsupported pv-why-unknown 1 5 }T
\ A 'c' form must close with its quote (review rvIR3, L3); Gforth reads
\ 'a as 97 too, but Forth-2012 does not define it.
T{ s" : f 'ab ;" checked -> outcome-unsupported pv-why-unknown 1 5 }T
T{ s" : f 'a- ;" checked -> outcome-unsupported pv-why-unknown 1 5 }T
T{ s" : f '>x ;" checked -> outcome-unsupported pv-why-unknown 1 5 }T
T{ s" : f 'a ;" checked -> outcome-unsupported pv-why-unknown 1 5 }T
T{ s" : f '' ;" checked -> outcome-unsupported pv-why-unknown 1 5 }T
T{ s" : f 'a'' ;" checked -> outcome-unsupported pv-why-unknown 1 5 }T
T{ s" : f #-$1 ;" checked -> outcome-unsupported pv-why-unknown 1 5 }T
T{ s" : f $ ;" checked -> outcome-unsupported pv-why-unknown 1 5 }T
T{ s" : f $1g ;" checked -> outcome-unsupported pv-why-unknown 1 5 }T
T{ s" : f %2 ;" checked -> outcome-unsupported pv-why-unknown 1 5 }T
\ LSHIFT and -ROT (A3), new primitives: the IR is 0.2, inside a word and
\ before CONSTANT.
T{ s" : f 1 4 lshift -rot ;" checked -> outcome-ok 0 1 0 }T
T{ s" lf-ir 0.2|source t.fs|word f @1:1|  lit 1 @1:5|  lit 4 @1:7|  prim lshift @1:9|"
   transcript-text drop over compare -> 0 }T
T{ transcript-text s" |  prim -rot @1:16|end @1:21|" contains? -> true }T
T{ s" 1 4 LSHIFT constant k" checked -> outcome-ok 0 1 0 }T
T{ s" lf-ir 0.2|source t.fs|constant k @1:21|  lit 1 @1:1|  lit 4 @1:3|  prim lshift @1:5|"
   transcript-text drop over compare -> 0 }T
T{ s" 1 2 3 -rot 2drop constant k" checked -> outcome-ok 0 1 0 }T
T{ s" 1 2 -rot constant k" checked -> outcome-unsupported pv-why-borrowed 1 5 }T
\ Output words (A2), inside definitions only, each an out line; an IR
\ without one, and a run refused before one is written, stays 0.1.
T{ s\" : f dup . u. cr emit space spaces .s .\" hi\" ;" checked -> outcome-ok 0 1 0 }T
T{ s" lf-ir 0.2|source t.fs|word f @1:1|  prim dup @1:5|  out . @1:9|  out u. @1:11|"
   transcript-text drop over compare -> 0 }T
T{ transcript-text s" |  out cr @1:14|  out emit @1:17|  out space @1:22|" contains? -> true }T
T{ transcript-text s\" |  out spaces @1:28|  out .s @1:35|  out .\" hi\" @1:38|end @1:45|"
   contains? -> true }T
T{ s" : f DUP . U. CR EMIT .S ;" checked -> outcome-ok 0 1 0 }T
T{ transcript-text s" |  out u. @1:11|  out cr @1:14|  out emit @1:17|  out .s @1:22|"
   contains? -> true }T
T{ s\" : f .\"   two\" s\" typed text\" TYPE .\" \" ;" checked -> outcome-ok 0 1 0 }T
T{ transcript-text s\" |  out .\"   two\" @1:5|  out .\" typed text\" @1:15|" contains?
   -> true }T
T{ transcript-text s\" |  out .\" \" @1:35|end @1:40|" contains? -> true }T
T{ s" lf-ir 0.2|" transcript-text drop over compare -> 0 }T
T{ s\" : f .\" a \"b\" ;" checked -> outcome-unsupported pv-why-unknown 1 11 }T
T{ s" 5 ." checked -> outcome-unsupported pv-why-outside 1 3 }T
T{ s" lf-ir 0.1|source t.fs|unsupported @1:3: not allowed outside a definition: .|"
   transcript-text drop over compare -> 0 }T
T{ s\" .\" x\"" checked -> outcome-unsupported pv-why-outside 1 1 }T
T{ s" : f cr ; cr" checked -> outcome-unsupported pv-why-outside 1 10 }T
T{ s\" : f s\" x\" ;" checked -> outcome-unsupported pv-why-not-ir 1 5 }T
T{ transcript-text s\" |unsupported @1:5: a Forth word outside IR 0.2: s\"|" contains?
   -> true }T
T{ s\" : f s\" x\"" checked -> outcome-unsupported pv-why-not-ir 1 5 }T
T{ s\" : f s\" x\" dup type ;" checked -> outcome-unsupported pv-why-not-ir 1 5 }T
T{ s" : f type ;" checked -> outcome-unsupported pv-why-not-ir 1 5 }T
T{ s\" : f .\" x\" type ;" checked -> outcome-unsupported pv-why-not-ir 1 11 }T
T{ s\" : f .\" no close ;" checked -> outcome-unsupported pv-why-open-text 1 5 }T
T{ s\" : f s\" no close ;" checked -> outcome-unsupported pv-why-open-text 1 5 }T
T{ s\" : f .\"" checked -> outcome-unsupported pv-why-open-text 1 5 }T
T{ s\" : f .\" a\tb\" ;" checked -> outcome-unsupported pv-why-character 1 5 }T
T{ s" : f .( x) ;" checked -> outcome-unsupported pv-why-not-ir 1 5 }T
T{ s\" : f ;\n: g .\" open" checked -> outcome-unsupported pv-why-open-text 2 5 }T
T{ s\" lf-ir 0.1|source t.fs|word f @1:1|end @1:5|word g @2:1|unsupported @2:5"
   transcript-text drop over compare -> 0 }T
\ A text too long for its IR line (96 characters) stops the run as full.
create long-text 128 chars allot
variable long#
: long+ ( c-addr u -- ) long-text long# @ chars + swap dup long# +! chars move ;
: long-dot-quote ( n -- c-addr u )
  0 long# ! s\" : f .\" " long+ 0 ?do s" x" long+ loop s\" \" ;" long+ long-text long# @ ;
T{ 81 long-dot-quote checked -> outcome-ok 0 1 0 }T
T{ 82 long-dot-quote checked -> outcome-full pv-why-capacity 1 5 }T

\ Redefinition of the file's own words (A1), Forth's early binding: each
\ use binds to the version visible where it stands; each version has its
\ own IR name (probe 1 of the amendment, whose results both Gforths give).
T{ s" : pf 1 ; : pg pf ; : pf 2 ; : ph pf ;" checked -> outcome-ok 0 1 0 }T
T{ transcript-text s" lf-ir 0.1|source t.fs|word pf @1:1|  lit 1 @1:6|end @1:8|" contains?
   -> true }T
T{ transcript-text s" |word pg @1:10|  call pf @1:15|end @1:18|word pf'1 @1:20|" contains?
   -> true }T
T{ transcript-text s" |word ph @1:29|  call pf'1 @1:34|end @1:37|" contains? -> true }T
\ Hidden until its ; inside its own body the name is the version before.
T{ s" : pk 10 ; : pk pk 1+ ; : pk pk 1+ ;" checked -> outcome-ok 0 1 0 }T
T{ transcript-text s" |word pk'1 @1:11|  call pk @1:16|" contains? -> true }T
T{ transcript-text s" |word pk'2 @1:24|  call pk'1 @1:29|" contains? -> true }T
T{ s" : pq pq ;" checked -> outcome-unsupported pv-why-recursive 1 6 }T
T{ s" : r 1 ; : r dup if r then ;" checked -> outcome-ok 0 1 0 }T
T{ transcript-text s" |    call r @1:20|" contains? -> true }T
\ One name in any case of letters; constants; a word made a constant.
T{ s" : Cw 1 ; : cw 2 ; : CW 3 ; : g cW ;" checked -> outcome-ok 0 1 0 }T
T{ transcript-text s" |word cw'2 @1:19|  lit 3 @1:24|end @1:26|word g @1:28|  call cw'2 @1:32|"
   contains? -> true }T
T{ s" 1 constant kk  kk 1+ constant kk  : g kk ;" checked -> outcome-ok 0 1 0 }T
T{ transcript-text s" |constant kk'1 @1:31|  call kk @1:16|  prim 1+ @1:19|end @1:31|"
   contains? -> true }T
T{ transcript-text s" |  call kk'1 @1:39|" contains? -> true }T
T{ s" : wc 7 ; 8 constant wc" checked -> outcome-ok 0 1 0 }T
T{ transcript-text s" |constant wc'1 @1:21|" contains? -> true }T
\ A name the IR gives another version is refused where it comes second;
\ standard words stay refused.
T{ s" : x ; : x ; : x'1 ;" checked -> outcome-unsupported pv-why-version-name 1 15 }T
T{ transcript-text s" |unsupported @1:15: a name the IR gives another version: x'1|" contains?
   -> true }T
T{ s" : x'1 ; : x ; : X ;" checked -> outcome-unsupported pv-why-version-name 1 17 }T
T{ s" : -rot 3 ;" checked -> outcome-unsupported pv-why-redefined 1 3 }T
T{ s" : .S ;" checked -> outcome-unsupported pv-why-redefined 1 3 }T
T{ s" : lshift ;" checked -> outcome-unsupported pv-why-redefined 1 3 }T
\ Each version counts as a definition: 32 per file.
create many-text 512 chars allot
variable many#
: many+ ( c-addr u -- ) many-text many# @ chars + swap dup many# +! chars move ;
: versions ( n -- c-addr u )
  0 many# ! 0 ?do s\" : v ;\n" many+ loop many-text many# @ ;
T{ 32 versions checked -> outcome-ok 0 32 0 }T
T{ transcript-text s" |word v'31 @32:1|end @32:5|" contains? -> true }T
T{ 33 versions checked -> outcome-full pv-why-capacity 33 3 }T

\ The caller's search order, compilation word list, BASE and STATE, and
\ the depth of the data stack, are as before after every kind of ending.
wordlist constant extra-words
create outer /run-settings allot
create order-before 20 cells allot
variable current-before
: order-keep ( -- ) get-order dup order-before ! 0 ?do order-before i 1+ cells + ! loop ;
: order-same? ( -- flag )
  get-order dup order-before @ <> if 0 ?do drop loop false exit then
  true swap 0 ?do swap order-before i 1+ cells + @ = and loop ;
: odd-settings ( -- )
  0 transcript# ! outer run-settings-save drop forth-wordlist extra-words 2 set-order
  extra-words set-current hex ;
: same-settings? ( -- flag )
  order-same? get-current current-before @ = and base @ 16 = and state @ 0= and ;
\ Run xt ( c-addr u -- outcome ) on the text under unusual settings.
: isolated? ( c-addr u xt -- flag )
  odd-settings order-keep get-current current-before ! depth 3 - >r execute drop
  depth r> = same-settings? and outer run-settings-restore ;
: shift-text ( c-addr u -- outcome ) 0 transcript# ! s" t.fs" lf-verify-text ;
: isolated-run? ( c-addr u -- flag ) ['] shift-text isolated? ;
T{ s" : f 1 2 + ;" isolated-run? -> true }T
T{ s" : f if ;" isolated-run? -> true }T
T{ s" : f bye ;" isolated-run? -> true }T
T{ s" : f 1 2 3 $10 ;" isolated-run? -> true }T
T{ s" : f 1. ;" isolated-run? -> true }T
T{ s" 1 2 3 4 5 6 7 8 9 constant x" isolated-run? -> true }T
T{ s" : f" isolated-run? -> true }T
T{ s" src/program/clamp.fs" ' lf-verify-file isolated? -> true }T
T{ s" tests/program/no-such-file.fs" ' lf-verify-file isolated? -> true }T
T{ s" no-such-file.fs" ' lf-verify-file isolated? lf-verify-reason
   -> true pv-why-unreadable }T
[defined] fdepth [if]
T{ fdepth s" : f 1e 2e ;" isolated-run? fdepth -> 0 true 0 }T
[then]
T{ depth -> 0 }T

\ A run started while Forth compiles (an immediate word calling it) is
\ refused before any line runs: Forth would compile the file's words into
\ the word being defined.
variable outcome-then
: run-while-compiling ( -- ) s" : f dup ;" shift-run outcome-then ! ; immediate
: compiled ( -- ) run-while-compiling ;
T{ outcome-then @ verdict -> outcome-invalid pv-why-compiling 0 0 }T
T{ s" lf-ir 0.1|source t.fs|invalid @0:0: run while Forth is compiling|1 28 0 0 "
   transcribed? -> true }T

\ An output word that throws or leaves a cell fails the run as invalid
\ ("output word failed"); the settings come back, and the next run works.
\ A run that the output word starts in its own context aborts (THROW -2)
\ and changes nothing; the run under way goes on.
: boom ( c-addr u -- ) 2drop 99 throw ;
: leave-cell ( c-addr u -- x ) 2drop 0 ;
variable nested
: nest ( c-addr u -- )
  2drop s" : g ;" s" u.fs" ['] lf-verify-text catch dup nested ! if 2drop 2drop then ;
: with-output ( c-addr u xt -- isolated? reason )
  lf-verify-to ['] shift-text isolated? ['] transcribe lf-verify-to lf-verify-reason ;
T{ s" : f ;" ' boom with-output -> true pv-why-output }T
T{ s" : f ;" ' leave-cell with-output -> true pv-why-output }T
T{ s" : f ;" ' nest with-output nested @ -> true 0 -2 }T
T{ s" : f ;" checked -> outcome-ok 0 1 0 }T

\ The source file is closed however the run ends: accepted, refused, or
\ stopped by an exception while it was read.
: closes? ( c-addr u xt -- outcome closed? )
  0 transcript# ! opened @ >r execute opened @ r> - 1 = open-files 0= and ;
T{ s" src/program/clamp.fs" ' lf-verify-file closes? -> outcome-ok true }T
T{ s" /dev/zero" ' lf-verify-file closes? -> outcome-invalid true }T
: interrupted ( xt -- outcome closed? reason )
  true interrupt-read ! s" src/program/clamp.fs" rot closes? lf-verify-reason ;
T{ ' lf-verify-file interrupted -> outcome-invalid true pv-why-interrupted }T

\ A run whose preparation throws (here the design's entry text, once; in
\ use, the dictionary running out while a word list is made) passes the
\ exception on and leaves the context free for the next run.
variable prefix-throws
: throwing-prefix ( -- c-addr u )
  prefix-throws @ if false prefix-throws ! 77 throw then s" " ;
: prefix-like ( xt design -- ) pv-shift over /pv-design move pv-design-prefix ! ;
pv-design: throwing-design  ' throwing-prefix throwing-design prefix-like
: prepare-throws ( -- code busy? )
  true prefix-throws ! s" : f ;" s" t.fs" throwing-design ['] pv-text-run catch
  dup if >r 2drop 2drop drop r> then pv-busy @ ;
T{ prepare-throws -> 77 false }T
T{ s" : f ;" checked -> outcome-ok 0 1 0 }T

\ The runner's own fallbacks, with designs like the mode shift but for
\ one word: a line word that refuses with no current token, whose
\ diagnostic then quotes none; and a handler of THROWs that throws
\ again, after which the run stops as interrupted.
: line-like ( xt design -- ) pv-shift over /pv-design move pv-design-line ! ;
: caught-like ( xt design -- ) pv-shift over /pv-design move pv-design-caught ! ;
: no-token-fail ( -- ) pv-no-token pv-why-unknown pv-fail ;
pv-design: no-token-design  ' no-token-fail no-token-design line-like
T{ 0 transcript# ! s" x" s" t.fs" no-token-design pv-text-run verdict
   -> outcome-unsupported pv-why-unknown 1 0 }T
T{ s" lf-ir 0.1|source t.fs|unsupported @1:0: not a known word or 32-bit decimal|"
   transcribed? -> true }T
: throw-55 ( -- ) 55 throw ;
: throw-66 ( code -- ) drop 66 throw ;
pv-design: rethrow-design  ' throw-66 rethrow-design caught-like
' throw-55 rethrow-design pv-design-line !
T{ s" x" s" t.fs" rethrow-design pv-text-run verdict
   -> outcome-invalid pv-why-interrupted 1 0 }T

\ A word of the file run by anyone but the verifier (here this test,
\ after the run) refuses: the mode shift never lets one run. It throws
\ the runner's code; a refusal already recorded stands, and after an
\ accepted run the record says interrupted.
: file-word ( c-addr u -- xt ) pv-words @ search-wordlist 0= abort" no file word" ;
: run-file-word ( -- code reason ) s" g" file-word catch lf-verify-reason ;
T{ s" : g ; : f then ;" checked -> outcome-invalid pv-why-unbalanced 1 11 }T
T{ run-file-word -> pv-throw pv-why-unbalanced }T
T{ s" : g ;" checked -> outcome-ok 0 1 0 }T
T{ run-file-word -> pv-throw pv-why-interrupted }T
T{ s" : f ;" checked -> outcome-ok 0 1 0 }T

\ Capacities at the boundary: eight open structures are written, the
\ ninth is full, at its own line, as with today's reader.
create nest-text 256 chars allot
variable nest#
: nest+ ( c-addr u -- ) nest-text nest# @ chars + swap dup nest# +! chars move ;
: nested ( n -- c-addr u )
  0 nest# ! s" : f" nest+ dup 0 ?do s\" \nif" nest+ loop 0 ?do s\" \nthen" nest+ loop
  s\" \n;" nest+ nest-text nest# @ ;
T{ 8 nested checked -> outcome-ok 0 18 0 }T
T{ 9 nested checked -> outcome-full pv-why-capacity 10 1 }T
T{ 9 nested shift-run drop transcript-text
   s" full @10:1: reader capacity exceeded: if|6 14 10 1 " compare -> 0 }T

\ A heap too small for a run's IR (review rvIR3, L1): the IR has no limit
\ of its own, so the run stops as full where the heap refuses more, and
\ sends its diagnostic alone, no IR line that could look whole; with the
\ heap free, the same text gives 324 lines. Its IR has about 5,500
\ characters; the program words first allocate 4,096.
create heavy-text 2048 chars allot
variable heavy#
: heavy+ ( c-addr u -- ) heavy-text heavy# @ chars + swap dup heavy# +! chars move ;
: heavy ( -- c-addr u )
  0 heavy# ! s\" : f\n" heavy+
  40 0 do s\" dup drop dup drop dup drop dup drop\n" heavy+ loop
  s" ;" heavy+ heavy-text heavy# @ ;
variable lines-sent
create last-line 128 chars allot
variable last-line#
: count-line ( c-addr u -- )
  1 lines-sent +! 128 min dup last-line# ! last-line swap chars move ;
: last-text ( -- c-addr u ) last-line last-line# @ ;
: heavy-run ( cap xt -- outcome lines )
  >r heap-cap ! 0 lines-sent ! ['] count-line lf-verify-to heavy s" t.fs" r> execute
  0 heap-cap ! ['] transcribe lf-verify-to lines-sent @ ;
: full-line? ( -- flag ) last-text s" full @" search nip nip ;
T{ 4096 ' lf-verify-text heavy-run lf-verify-reason full-line?
   -> outcome-full 1 pv-why-capacity true }T
T{ 0 ' lf-verify-text heavy-run -> outcome-ok 324 }T

\ A caller whose search order is deeper than the run can keep: the run is
\ refused as full before anything changes, the order is the caller's
\ still, and the context is not left busy.
create deep-before /run-settings allot
: deep ( -- )
  get-order run-settings-order-max 0 ?do forth-wordlist swap 1+ loop set-order ;
: order-depth ( -- n ) get-order dup >r 0 ?do drop loop r> ;
variable deep-order#
: deep-run ( xt -- outcome reason same-depth? )
  >r deep-before run-settings-save drop deep order-depth deep-order# !
  s" : f ;" s" t.fs" r> execute verdict 2drop
  order-depth deep-order# @ = deep-before run-settings-restore ;
: deep-shift ( -- outcome reason same? ) ['] lf-verify-text deep-run ;
T{ deep-shift -> outcome-full pv-why-capacity true }T
T{ s" : f ;" checked -> outcome-ok 0 1 0 }T

\ The rule for names that read as numbers, against the host: every token
\ of one to three printable characters (but " { and }, which Gforth 1.0
\ reads as strings and environment names, not numbers), and some longer
\ ones, that this Gforth reads with an empty search order and BASE ten
\ (as a number, a float or a character) must be refused as a name.
wordlist constant no-words
create oracle-settings /run-settings allot
variable oracle-depth
variable oracle-reads
variable oracle-misses
[defined] fdepth [if]
: oracle-fclear ( -- ) begin fdepth while fdrop repeat ;
[else]
: oracle-fclear ( -- ) ;
[then]
: oracle-clear ( i*x -- ) begin depth oracle-depth @ > while drop repeat oracle-fclear ;
\ Whether the host reads c-addr u, by itself, without a THROW.
: host-reads? ( c-addr u -- flag )
  depth 2 - oracle-depth ! oracle-settings run-settings-save drop no-words 1 set-order
  decimal ['] evaluate catch oracle-settings run-settings-restore 0= >r oracle-clear r> ;
: oracle ( c-addr u -- )
  2dup host-reads? if 1 oracle-reads +! 2dup pv-number-like? 0=
  if ." read but not refused: " 2dup type cr 1 oracle-misses +! then then 2drop ;
create token 4 chars allot
\ Characters of a token: printable ASCII but the three above.
: token-char? ( char -- flag )
  dup [char] " <> over [char] { <> and swap [char] } <> and ;
: token! ( char i -- ) chars token + c! ;
\ Run xt ( char -- ) for each character a token may hold.
: each-char ( xt -- )
  127 33 do i token-char? if i over execute then loop drop ;
: token-3rd ( char -- ) 2 token! token 3 oracle ;
: token-2nd ( char -- ) 1 token! token 2 oracle ['] token-3rd each-char ;
: token-1st ( char -- ) 0 token! token 1 oracle ['] token-2nd each-char ;
: oracle-others ( -- )
  s" 1_000" oracle s" 1.5e3" oracle s" -'a'" oracle s" 0x10" oracle s" 2p" oracle
  s" 1k" oracle s" $FF" oracle s" -$1F" oracle s" #-12" oracle s" 'a" oracle
  s" +k0+" oracle s" -u1." oracle s" +M10" oracle s" -k1.5" oracle s" #-k1" oracle ;
: oracle-all ( -- reads misses )
  0 oracle-reads ! 0 oracle-misses ! ['] token-1st each-char oracle-others
  oracle-reads @ oracle-misses @ ;
T{ oracle-all 0 = swap 100 > -> true true }T

\ Each context has its own run record. Last but one, because making a
\ context ends declarations.
T{ s" : f 7 ;" shift-run verdict -> outcome-ok 0 1 0 }T
context-new throw constant other
other context-use
' transcribe lf-verify-to
T{ s" : g if ;" shift-run verdict -> outcome-invalid pv-why-unbalanced 1 8 }T
context-main context-use
T{ lf-verify-reason lf-verify-where -> 0 1 0 }T
T{ other context-free -> 0 }T

\ The rest of this file changes FORTH-WORDLIST, so that everything it runs
\ is compiled first.
\
\ A host word named like a decimal, which run mode would call: the mode
\ shift refuses it.
: decimal-named ( -- outcome reason ) s" : f 7 ;" shift-text lf-verify-reason ;
\ A compile-only word redefined after the program words loaded, here IF:
\ refused where the host gives the new word a token of its own (Gforth
\ 1.0), not where every compile-only word shares one (Gforth 0.7.3), a
\ known limit (docs/programming/PROGRAM_IR.md). Both cases are checked,
\ on whichever host runs this.
s" if" forth-wordlist search-wordlist drop constant if-before
: if-shares-token? ( -- flag ) s" if" forth-wordlist search-wordlist drop if-before = ;
: if-expected ( shares? -- outcome reason )
  if outcome-ok 0 else outcome-unsupported pv-why-replaced then ;
: if-as-expected? ( -- flag )
  s" : f 1 if then ;" shift-text lf-verify-reason if-shares-token? if-expected
  rot = >r = r> and ;
[defined] compile-only [if]
: if ( -- ) postpone if ; immediate compile-only
[then]
T{ if-as-expected? -> true }T
get-current forth-wordlist set-current
: 7 ( -- n ) 7 ;
set-current
T{ decimal-named -> outcome-unsupported pv-why-unknown }T

\ A standard word redefined before the run: here every word with
\ verification semantics in turn, each with a word of the same name made
\ in FORTH-WORDLIST. The mode shift knows the host's own word by its
\ identity and refuses the new one, at its token. This comes last,
\ since the new words hide the standard ones from the rest of this file.
create shadow-text 40 chars allot
: shadow-name ( c-addr u -- c-addr' u' )
  s" create " shadow-text swap chars move tuck shadow-text 7 chars + swap chars move
  shadow-text swap 7 + ;
: shadow ( c-addr u -- )
  get-current >r forth-wordlist set-current shadow-name evaluate r> set-current ;
variable shadow-misses
: one-shadow ( entry -- )
  pv-entry-text 2dup shadow 2dup shift-text drop lf-verify-reason pv-why-replaced <>
  lf-verify-where 1 1 rot = >r = r> and 0= or
  if ." not refused: " 2dup type cr 1 shadow-misses +! then 2drop ;
: shadow-all ( -- n )
  0 shadow-misses ! pv-names store-count @ 0 ?do i pv-entry dup pv-entry-kind @
  pv-kind-reserved <> if one-shadow else drop then loop shadow-misses @ ;
\ TYPE after S" is the host's own too (review rvIR3, L2): with TYPE alone
\ shadowed, the mode shift refuses it at TYPE.
s" type" shadow
T{ s\" : f s\" xy\" type ;" shift-text lf-verify-reason lf-verify-where
   -> outcome-unsupported pv-why-replaced 1 12 }T
T{ shadow-all -> 0 }T
bye

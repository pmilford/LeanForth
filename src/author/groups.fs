\ LeanForth's wordlists and name words (ADR 0017 §3-§5, §9). While a proof
\ runs, the search order holds only three wordlists, searched first to
\ last: LF-WORDS (the syntax words, lf-words), LF-LOCALS (variables and
\ universe parameters, lf-locals) and LF-CONST (constants, lf-consts).
\ Forth's own words are not in the order, so they are invisible in proof
\ text. A constant has an entry under its full name in LF-CONST; each
\ shorter name it can be written by (the part after a dot of its name)
\ has a word in LF-CONST too, with no entry, so that the interpreter finds
\ a word for it. Which constant a name means is decided when the word
\ runs, as Lean decides it (namespaces.fs, declarations.fs).
\
\ Names are case-sensitive although Forth finds words regardless of case
\ (Forth-2012 3.4.2, Gforth): one Forth word, a name group, stands for all
\ spellings that are equal apart from case in one wordlist, and its
\ entries hold the exact spellings with their meanings. When it runs it
\ re-reads the token that invoked it (source.fs) and acts only on an exact
\ match; otherwise it hands the token to the wordlists searched after its
\ own (GET-ORDER, SEARCH-WORDLIST) and runs what it finds there, or stops
\ with "unknown name". A syntax word holds its own spelling. A word must
\ be run by the text interpreter: the token it re-reads must find it.
\
\ Numbers: the interpreter converts a token no word has as a number, in
\ whatever forms its host reads. Every LeanForth word, before it acts,
\ checks the tokens of its line between the last token a word read and
\ its own: those are the numbers, and each must be a plain decimal
\ (source.fs); the runner checks the rest of each line the same way. So
\ the same tokens are refused on every host, at the token itself. No
\ group word is ever made for a number-like spelling.
\
\ The group words live in the dictionary and are shared; their entries
\ live in the checker context, so another context sees the same words but
\ none of the names. Group words are made while a proof runs (for a name
\ spelt in no earlier run), by EVALUATE of a defining word: the only
\ standard way to define a word whose name is a string. Untrusted
\ authoring code.
\ State: the entry store lfa-entries and one record, lfa-groups (the
\ spellings' bytes, the key an entry search seeks, a copy of the search
\ order, the text that defines a group), both in the checker context.

require ../lib/lib.fs
require ./values.fs
require ./form.fs

wordlist constant lf-words
wordlist constant lf-locals
wordlist constant lf-consts
\ A private wordlist that holds only lfa-group:, the one word the EVALUATE
\ that defines a group runs (ADR 0017 Amendment 1, A5 row 8): no word
\ defined later under that name, by a program around a run, is found.
wordlist constant lfa-definer
\ The search order while a proof runs.
: lfa-order! ( -- ) lf-consts lf-locals lf-words 3 set-order ;

\ Entry kinds.
1 constant lfa-entry-variable    \ value: the binder's slot
2 constant lfa-entry-universe    \ value: the universe parameter's level
3 constant lfa-entry-constant    \ value: the declaration

1024 constant lfa-entry-capacity
65536 constant lfa-spelling-capacity
16 constant lfa-order-capacity
256 constant lfa-define-capacity

begin-structure /lfa-entry
  field: lfa-entry-group     \ body address of the group word
  field: lfa-entry-offset    \ the exact spelling, in the spelling bytes
  field: lfa-entry-length
  field: lfa-entry-kind
  field: lfa-entry-value
end-structure
lfa-entry-capacity /lfa-entry 0 context-store: lfa-entries

\ What an entry search seeks: a spelling, a group and a kind.
begin-structure /lfa-key
  field: lfa-key-addr
  field: lfa-key-length
  field: lfa-key-group
  field: lfa-key-kind
end-structure

begin-structure /lfa-groups
  field: lfa-groups-used       \ spelling bytes in use
  field: lfa-groups-order#     \ wordlists in the copied search order
  lfa-order-capacity cells +field lfa-groups-order
  /lfa-key +field lfa-groups-key
  lfa-spelling-capacity +field lfa-groups-spellings
  lfa-define-capacity +field lfa-groups-define
end-structure
/lfa-groups context-record: lfa-groups

: lfa-groups-reset ( -- ) lfa-entries store-clear 0 lfa-groups lfa-groups-used ! ;

\ Entries, newest last. A scope's entries go when it closes.
: lfa-entry ( i -- entry ) lfa-entries store-slot ;
: lfa-entry# ( -- n ) lfa-entries store-count @ ;
: lfa-spelling ( entry -- c-addr u )
  dup lfa-entry-offset @ lfa-groups lfa-groups-spellings + swap lfa-entry-length @ ;
: lfa-spell-room? ( u -- flag ) lfa-spelling-capacity lfa-groups lfa-groups-used @ -
  upto? ;
: lfa-spell! ( c-addr u entry -- )
  over lfa-spell-room? lfa-e-entries-full lfa-must
  2dup lfa-entry-length ! lfa-groups lfa-groups-used @ swap lfa-entry-offset !
  tuck lfa-groups lfa-groups-spellings lfa-groups lfa-groups-used @ + swap move
  lfa-groups lfa-groups-used +! ;
\ Forget entries i and later.
: lfa-entries-cut ( i -- )
  dup lfa-entry# < 0= if drop exit then
  dup lfa-entry lfa-entry-offset @ lfa-groups lfa-groups-used ! lfa-entries store-count
    ! ;

\ The newest entry with the key's spelling, group and kind.
: lfa-key! ( c-addr u group kind -- key )
  lfa-groups lfa-groups-key >r r@ lfa-key-kind ! r@ lfa-key-group ! r@ lfa-key-length !
  r@ lfa-key-addr ! r> ;
: lfa-key-spelling ( key -- c-addr u ) dup lfa-key-addr @ swap lfa-key-length @ ;
: lfa-entry-is? ( key entry -- flag )
  over lfa-key-group @ over lfa-entry-group @ = >r
  over lfa-key-kind @ over lfa-entry-kind @ = r> and
  if swap lfa-key-spelling rot lfa-spelling compare 0= else 2drop false then ;
: lfa-entry-find ( key -- entry true | false )
  lfa-entry# begin dup while 1- 2dup lfa-entry lfa-entry-is?
    if nip lfa-entry true exit then repeat 2drop false ;
\ The same for the current token.
: lfa-token-find ( group kind -- entry true | false )
  2>r lfa-token 2r> lfa-key! lfa-entry-find ;

\ The search order, copied: wordlist i is searched i-th (0 first).
: lfa-order@ ( -- )
  get-order dup lfa-order-capacity > 0= lfa-e-namespaces lfa-must
  dup lfa-groups lfa-groups-order# ! 0 ?do lfa-groups lfa-groups-order i cells + ! loop ;
: lfa-order-wid ( i -- wid ) cells lfa-groups lfa-groups-order + @ ;
: lfa-order# ( -- n ) lfa-groups lfa-groups-order# @ ;
: lfa-order-index ( wid -- i )
  lfa-order# 0 ?do dup i lfa-order-wid = if drop i unloop exit then loop drop lfa-order# ;
\ Run the word that the wordlists after wid have for the current token,
\ or stop: no LeanForth word has it.
: lfa-pass ( wid -- )
  lfa-order@ lfa-order-index 1+ lfa-order# tuck min ?do lfa-token i lfa-order-wid
    search-wordlist
    if unloop execute exit then loop
  lfa-e-unknown lfa-fail ;

\ The numbers the interpreter read: the tokens of c-addr u. The first that
\ is no plain decimal, or an empty string; it is refused as a number form
\ (number-like) or as an unknown name.
: lfa-stray ( c-addr u -- token-addr token-u )
  begin lfa-next-token dup while 2dup lfa-plain-decimal? 0= if 2swap 2drop exit then
    2drop repeat 2swap 2drop ;
: lfa-stray-code ( c-addr u -- code )
  lfa-number-like? if lfa-e-not-word else lfa-e-unknown then ;
\ Check the line up to offset n: a stray token stops the run at itself;
\ in natural form the numbers' positions are kept (form.fs).
: lfa-stray! ( c-addr u token-addr token-u -- )
  2swap 2drop 2dup lfa-token! lfa-stray-code lfa-fail ;
: lfa-read-to ( n -- )
  lfa-unread-to 2dup lfa-stray dup if lfa-stray! then 2drop lfa-numerals-read ;

\ The token that invoked the word whose body is given, which must be found
\ as that word in wid: the word was run by the text interpreter. The
\ numbers before it are checked, and it becomes the current token.
: lfa-numbers-before ( c-addr -- )
  dup lfa-on-line? if lfa-offset lfa-read-to else drop then ;
: lfa-invoked-by ( body wid -- )
  lfa-invoked over lfa-numbers-before 2dup lfa-token! rot search-wordlist
  if >body = else drop false then lfa-e-interpreter lfa-must ;

\ Syntax words: the word's xt in the kernel form, its xt in natural form
\ (form.fs), then its spelling as a counted string. A word of the kernel
\ form only is not supported yet in natural form (error 70) until a
\ natural meaning is given (lfa-natural!); a pending ' stops any natural
\ syntax word.
: lfa-natural-later ( -- ) lfa-e-natural-later lfa-fail ;
: lfa-syntax-name ( body -- c-addr u ) 2 cells + count ;
: lfa-syntax-xt ( body -- xt ) lfa-kernel-form? if @ else lfa-tick-free cell+ @ then ;
: lfa-syntax-run ( body -- )
  dup >r lf-words lfa-invoked-by lfa-token r@ lfa-syntax-name compare
  if r> drop lf-words lfa-pass else r> lfa-syntax-xt execute then ;
: lfa-syntax-spelling, ( c-addr u -- ) dup c, here swap dup chars allot move align ;
\ Define name ( -- ) in LF-WORDS, which runs xt for its exact spelling.
: lfa-syntax ( xt "name" -- )
  get-current >r lf-words set-current >in @ create >in ! , ['] lfa-natural-later ,
  parse-name lfa-syntax-spelling, r> set-current does> lfa-syntax-run ;
\ Give the syntax word name its meaning in natural form (a load-time word).
: lfa-natural! ( xt "name" -- )
  parse-name lf-words search-wordlist 0= abort" lfa-natural!: no such syntax word"
  >body cell+ ! ;

\ Name groups. The body holds the group's wordlist.
: lfa-group-wid ( body -- wid ) @ ;
\ Locals: the innermost variable and the universe parameter with this
\ spelling make one name value; with neither, the token is passed on.
: lfa-local-value ( entry true | false -- n ) if lfa-entry-value @ else -1 then ;
: lfa-local-run ( body -- )
  dup lfa-entry-variable lfa-token-find lfa-local-value
  swap lfa-entry-universe lfa-token-find lfa-local-value
  over 0< over 0< and if 2drop lf-locals lfa-pass exit then lfa-name-value
  lfa-named-natural ;
\ Constants: which one a name means is Lean's resolution (declarations.fs).
defer lfa-const-run ( body -- )
: lfa-run-group ( body -- )
  dup dup lfa-group-wid lfa-invoked-by
  dup lfa-group-wid lf-locals = if lfa-local-run else lfa-const-run then ;
\ Define a group word, in wid, by EVALUATE of: lfa-group: NAME.
get-current lfa-definer set-current
: lfa-group: ( wid "name" -- ) create , does> lfa-run-group ;
set-current
: lfa-define-prefix ( -- c-addr u ) s" lfa-group: " ;
: lfa-define-text ( c-addr u -- c-addr' u' )
  dup lfa-define-capacity 16 - > 0= lfa-e-names-full lfa-must
  lfa-define-prefix lfa-groups lfa-groups-define swap move
  tuck lfa-groups lfa-groups-define lfa-define-prefix nip + swap move
  lfa-groups lfa-groups-define swap lfa-define-prefix nip + ;
\ The dictionary a run leaves free: no group word is made with less than
\ this many address units unused, so a text never drives the dictionary
\ to its end, where Gforth 1.0 lets HERE pass the end by a few bytes
\ (ADR 0017 Amendment 1, A5 row 11). A margin, not a capacity: the
\ dictionary's size is the host's.
65536 constant lfa-dictionary-reserve
: lfa-dictionary-room ( -- )
  unused lfa-dictionary-reserve < 0= lfa-e-entries-full lfa-must ;
\ Define the group word for c-addr u in wid; a number-like spelling never
\ gets one. The proof's search order is set again afterwards.
: lfa-group-define ( c-addr u wid -- )
  lfa-dictionary-room get-current >r dup set-current -rot lfa-define-text
  lfa-definer 1 set-order evaluate lfa-order! r> set-current ;
\ The group of c-addr u in wid, made when there is none.
: lfa-found ( xt n | 0 -- body ) dup 0<> lfa-e-entries-full lfa-must drop >body ;
: lfa-group ( c-addr u wid -- body )
  >r 2dup r@ search-wordlist if nip nip r> drop >body exit then
  2dup lfa-number-like? 0= lfa-e-bad-name lfa-must
  2dup r@ lfa-group-define r> search-wordlist lfa-found ;
\ A new entry of the given kind and value for the exact spelling c-addr u
\ in wid's group.
: lfa-entry-set ( kind value entry -- ) tuck lfa-entry-value ! lfa-entry-kind ! ;
: lfa-entry-new ( c-addr u wid -- entry )
  >r 2dup r> lfa-group >r lfa-entries store-new-slot lfa-e-entries-full lfa-must drop
  dup /lfa-entry erase r> over lfa-entry-group ! dup >r lfa-spell! r> ;

\ The constant whose full name is c-addr u, if there is one: the text's
\ own, else the library's. library.fs sets lfa-library-named while it
\ loads (words.fs loads it, so every run has it; with no library given,
\ lfa-library-lookup finds none).
defer lfa-library-named ( c-addr u -- decl true | false )
: lfa-file-const ( c-addr u -- decl true | false )
  2dup lf-consts search-wordlist 0= if 2drop false exit then
  >body lfa-entry-constant lfa-key! lfa-entry-find
  if lfa-entry-value @ true else false then ;
: lfa-const-named ( c-addr u -- decl true | false )
  2dup lfa-file-const if nip nip true else lfa-library-named then ;

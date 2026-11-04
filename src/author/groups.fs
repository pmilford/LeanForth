\ LeanForth's wordlists and name words (ADR 0017 §3-§5, §9). While a proof
\ runs, the search order holds only these wordlists, searched first to
\ last: LF-WORDS (the syntax words, lf-words), LF-LOCALS (variables and
\ universe parameters, lf-locals), the namespaces entered and opened,
\ newest first, and LF-CONST (every constant under its full name,
\ lf-consts). Forth's own words are not in the order, so they are
\ invisible in proof text.
\
\ Names are case-sensitive although Forth finds words regardless of case
\ (Forth-2012 3.4.2, Gforth): one Forth word, a name group, stands for all
\ spellings that are equal apart from case in one wordlist, and its
\ entries hold the exact spellings with their meanings. When it runs it
\ re-reads the token that invoked it (source.fs) and acts only on an exact
\ match; otherwise it hands the token to the wordlists searched after its
\ own (GET-ORDER, SEARCH-WORDLIST) and runs what it finds there, or stops
\ with "unknown name". A syntax word holds its own spelling. A word must
\ be run by the text interpreter: the token it re-reads must find it. A
\ constant found through a namespace under a short name must not also be
\ a different constant in another visible namespace or at the root.
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

wordlist constant lf-words
wordlist constant lf-locals
wordlist constant lf-consts
\ The wordlist these modules are compiled into; it finds the defining
\ word of a group.
get-current constant lfa-home

\ Entry kinds.
1 constant lfa-entry-variable    \ value: the binder's slot
2 constant lfa-entry-universe    \ value: the universe parameter's level
3 constant lfa-entry-constant    \ value: the declaration

256 constant lfa-entry-capacity
4096 constant lfa-spelling-capacity
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
  field: lfa-groups-wid        \ the wordlist of the group being defined
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
: lfa-spell-room? ( u -- flag ) lfa-spelling-capacity lfa-groups lfa-groups-used @ - upto? ;
: lfa-spell! ( c-addr u entry -- )
  over lfa-spell-room? lfa-e-entries-full lfa-must
  2dup lfa-entry-length ! lfa-groups lfa-groups-used @ swap lfa-entry-offset !
  tuck lfa-groups lfa-groups-spellings lfa-groups lfa-groups-used @ + swap move
  lfa-groups lfa-groups-used +! ;
\ Forget entries i and later.
: lfa-entries-cut ( i -- )
  dup lfa-entry# < 0= if drop exit then
  dup lfa-entry lfa-entry-offset @ lfa-groups lfa-groups-used ! lfa-entries store-count ! ;

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
  lfa-order@ lfa-order-index 1+ lfa-order# tuck min ?do lfa-token i lfa-order-wid search-wordlist
    if unloop execute exit then loop
  lfa-e-unknown lfa-fail ;

\ The token that invoked the word whose body is given, which must be found
\ as that word in wid: the word was run by the text interpreter. The
\ token becomes the current token.
: lfa-invoked-by ( body wid -- )
  lfa-invoked 2dup lfa-token! rot search-wordlist
  if >body = else drop false then lfa-e-interpreter lfa-must ;

\ Syntax words: the word's xt, then its spelling as a counted string.
: lfa-syntax-name ( body -- c-addr u ) cell+ count ;
: lfa-syntax-run ( body -- )
  dup >r lf-words lfa-invoked-by lfa-token r@ lfa-syntax-name compare
  if r> drop lf-words lfa-pass else r> @ execute then ;
: lfa-syntax-spelling, ( c-addr u -- ) dup c, here swap dup chars allot move align ;
\ Define name ( -- ) in LF-WORDS, which runs xt for its exact spelling.
: lfa-syntax ( xt "name" -- )
  get-current >r lf-words set-current >in @ create >in ! ,
  parse-name lfa-syntax-spelling, r> set-current does> lfa-syntax-run ;

\ Name groups. The body holds the group's wordlist.
defer lfa-group-run ( body -- )
: lfa-group-wid ( body -- wid ) @ ;
: lfa-group: ( "name" -- ) create lfa-groups lfa-groups-wid @ , does> lfa-group-run ;
: lfa-define-prefix ( -- c-addr u ) s" lfa-group: " ;
: lfa-define-text ( c-addr u -- c-addr' u' )
  dup lfa-define-capacity 16 - > 0= lfa-e-names-full lfa-must
  lfa-define-prefix lfa-groups lfa-groups-define swap move
  tuck lfa-groups lfa-groups-define lfa-define-prefix nip + swap move
  lfa-groups lfa-groups-define swap lfa-define-prefix nip + ;
\ Define the group word for c-addr u in wid.
: lfa-group-define ( c-addr u wid -- )
  dup lfa-groups lfa-groups-wid ! get-current >r set-current lfa-define-text 2>r
  get-order lfa-home 1 set-order 2r> evaluate set-order r> set-current ;
\ The group of c-addr u in wid, made when there is none.
: lfa-found ( xt n | 0 -- body ) dup 0<> lfa-e-entries-full lfa-must drop >body ;
: lfa-group ( c-addr u wid -- body )
  >r 2dup r@ search-wordlist if nip nip r> drop >body exit then
  2dup r@ lfa-group-define r> search-wordlist lfa-found ;
\ A new entry of the given kind and value for the exact spelling c-addr u
\ in wid's group.
: lfa-entry-set ( kind value entry -- ) tuck lfa-entry-value ! lfa-entry-kind ! ;
: lfa-entry-new ( c-addr u wid -- entry )
  >r 2dup r> lfa-group >r lfa-entries store-new-slot lfa-e-entries-full lfa-must drop
  dup /lfa-entry erase r> over lfa-entry-group ! dup >r lfa-spell! r> ;

\ Locals: the innermost variable and the universe parameter with this
\ spelling make one name value; with neither, the token is passed on.
: lfa-local-value ( entry true | false -- n ) if lfa-entry-value @ else -1 then ;
: lfa-local-run ( body -- )
  dup lfa-entry-variable lfa-token-find lfa-local-value
  swap lfa-entry-universe lfa-token-find lfa-local-value
  over 0< over 0< and if 2drop lf-locals lfa-pass exit then lfa-name-value ;

\ Constants. A short name found in a namespace must not name a different
\ constant in another searched wordlist (another namespace, or LF-CONST).
: lfa-const-in ( wid -- decl true | false )
  >r lfa-token r> search-wordlist 0= if false exit then
  >body lfa-entry-constant lfa-token-find if lfa-entry-value @ true else false then ;
: lfa-differs? ( decl wid -- flag ) lfa-const-in if <> else drop false then ;
: lfa-searched? ( wid -- flag ) dup lf-words <> swap lf-locals <> and ;
: lfa-clash? ( decl wid i -- flag )
  lfa-order-wid tuck <> over lfa-searched? and if lfa-differs? else 2drop false then ;
: lfa-ambiguous? ( decl wid -- flag )
  lfa-order@ lfa-order# 0 ?do 2dup i lfa-clash? if 2drop true unloop exit then loop
  2drop false ;
: lfa-unambiguous ( decl wid -- )
  dup lf-consts = if 2drop exit then lfa-ambiguous? 0= lfa-e-ambiguous lfa-must ;
: lfa-const-run ( body -- )
  dup lfa-entry-constant lfa-token-find 0= if lfa-group-wid lfa-pass exit then
  lfa-entry-value @ tuck swap lfa-group-wid lfa-unambiguous lfa-const-value ;

: lfa-run-group ( body -- )
  dup dup lfa-group-wid lfa-invoked-by
  dup lfa-group-wid lf-locals = if lfa-local-run else lfa-const-run then ;
' lfa-run-group is lfa-group-run

\ Tactic proofs, read (plan FE1g-2; design docs/design/FE1G_TACTICS.md
\ section 3, the owner's syntax of 2026-11-12): the natural meanings of
\ the words of a proof after := by. They are read, checked for shape and
\ recorded, not run: a tactic proof whose blocks all close stops at its
\ end NAME as not supported yet (error 80; running tactics is plan
\ FE1g-3), never accepted. The words, in the order Lean writes them:
\   t by-exact, t by-induction, t by-induction-with   take one value each;
\   by-rfl, by-intro: NAME (_ for an inaccessible hypothesis);
\   by-rw[ r1 .. rn ], by-rewrite[ r1 .. rn ]   the values built between
\     the brackets are the rules, in order (none is allowed, as in Lean);
\   | TAG NAMES... =>   an alternative of the by-induction-with block it is
\     right inside, up to the next | or the block's by-end;
\   by-case: TAG NAMES... =>   a case block, up to its by-end;
\   by-end   closes the innermost by-induction-with or by-case: block;
\   =>   ends a header; anywhere else it is an error.
\ The shape, each failure an error at the word's line and column (codes
\ in author/errors.fs): a tactic word only in a tactic proof (81); none
\ inside by-rw[ ] (82, and the bracket's place); none before the first |
\ of a by-induction-with (Lean's pre-tactic, with tac: not supported yet,
\ 72); no binder of a term left open (21); exactly the values the word
\ takes, none left (86; 87 instead when a hypothesis read since the last
\ tactic word could take the extra ones: how many values a hypothesis
\ takes is known only once its tactic runs); a header's tokens on its
\ line, its tag and names names and no words (84), the tag not _ or @TAG
\ and no second tag (72: Lean's wildcard, @ and | a | b forms, plan FE5);
\ an alternative or case block holds a tactic (85, as Lean's parser);
\ by-end, ] and | only where their block is open (83); end NAME with every
\ block closed (82, and the open block's place) and no value left (86).
\ An empty proof and a by-induction-with with no alternative are read:
\ Lean parses both and refuses them only when it runs them.
\
\ Names a header or by-intro: gives are hypotheses. Until the block they
\ were given in ends (by-intro:'s, the block it is in) a name spelt so
\ reads as a syntax node of kind syn-k-hyp (syntax.fs) taking no values,
\ when it is newer than every variable of that spelling (author/groups.fs,
\ lfa-hypothesis-run).
\
\ The record, format lf-tactic-format (1): the steps in the order read,
\ in a heap store, and their arguments in another. Step fields: tac-kind
\ (tac-k-*); tac-parent, the block it is in (-1 for the proof itself);
\ tac-at, its word's position; tac-from and tac-to, its text: from just
\ past the step before it to just past its last word (a block's closing
\ word; an alternative's last tactic; -1 while open); tac-arrow, a
\ header's => (else -1); tac-name, a header's tag (a name ID, else 0);
\ tac-first and tac-count, its arguments; tac-inner, the tactics right
\ inside a block; tac-entries, the names in scope before a header's.
\ Argument fields: targ-x, the syntax node of a term (by-exact's,
\ by-induction's, a rule) or the name ID of a hypothesis (0 for _), and
\ targ-at, its position. Positions are author/source.fs's. The parent
\ links are the stack of open blocks, so nesting is limited only by the
\ heap. Only positions are kept, not the text: reading a block again
\ (FE5's combinators) is the runner's to arrange (plan FE1g-3).
\
\ Untrusted: a record says what was written; tactics will only ever build
\ a term for the kernel to check. The words live in LF-WORDS
\ (author/words.fs) and the hypotheses in LF-LOCALS, so no Forth word
\ becomes reachable from the text.
\ Words: lf-tactic-proof? ( -- flag ), lf-tactic-count ( -- n ),
\ lf-tactic-step ( i -- addr ) (unchecked, valid until the next step),
\ lf-tactic-arg ( j -- x pos ) (unchecked), the kinds and fields above.
\ State: one context record, tac-read (the innermost open block, where
\ the next step's text begins, whether a hypothesis was read since the
\ last tactic word), and the stores tac-steps and tac-args, members of
\ the checker context (ADR 0009) whose blocks are on the heap.

require ../lib/lib.fs
require ../author/runner.fs
require ./syntax.fs
require ./reader.fs

1 constant lf-tactic-format

1 constant tac-k-by          \ the proof, from := by to end NAME (a block)
2 constant tac-k-rfl
3 constant tac-k-exact
4 constant tac-k-intro
5 constant tac-k-induction
6 constant tac-k-with        \ by-induction-with (a block of alternatives)
7 constant tac-k-alt         \ | TAG NAMES... => (a block)
8 constant tac-k-case        \ by-case: TAG NAMES... => (a block)
9 constant tac-k-rw          \ by-rw[ (a block of rules)
10 constant tac-k-rewrite    \ by-rewrite[ (a block of rules)

begin-structure /tac
  field: tac-kind
  field: tac-parent
  field: tac-at
  field: tac-from
  field: tac-to
  field: tac-arrow
  field: tac-name
  field: tac-first
  field: tac-count
  field: tac-inner
  field: tac-entries
end-structure
begin-structure /targ
  field: targ-x
  field: targ-at
end-structure
begin-structure /tac-read
  field: tac-read-open      \ the innermost open block, or -1
  field: tac-read-from      \ where the next step's text begins
  field: tac-read-hyp       \ true: a hypothesis read since the last tactic word
end-structure
/tac-read context-record: tac-read
store-header context-record: tac-steps
store-header context-record: tac-args

\ The stores grow on the heap up to a limit, only the heap's (plan 6.2.0).
16 constant tac-room
max-n store-header - /tac cell+ / constant tac-limit
max-n store-header - /targ cell+ / constant targ-limit
: tac-heap ( width limit store -- )
  >r swap tac-room swap 0 r@ store-heap-init ok? 0= abort" tactics: no heap"
  r> store-limit! ok? 0= abort" tactics: limit" ;
: tac-make ( -- ) /tac tac-limit tac-steps tac-heap /targ targ-limit tac-args tac-heap ;
' tac-make context-setup
:noname ( -- ) tac-steps store-heap-free tac-args store-heap-free ; context-teardown

\ The reading state.
: lft-open ( -- i ) tac-read tac-read-open @ ;
: lft-open! ( i -- ) tac-read tac-read-open ! ;
: lft-hyp? ( -- flag ) tac-read tac-read-hyp @ ;
: lft-hyp! ( flag -- ) tac-read tac-read-hyp ! ;
: lft-read-from ( -- pos ) tac-read tac-read-from @ ;
: lft-read-from! ( pos -- ) tac-read tac-read-from ! ;
: lft-reset ( -- )
  tac-steps store-clear tac-args store-clear -1 lft-open! false lft-hyp! ;
' lft-reset context-setup
\ A declaration starts: the reader's trees and the record are new.
: lft-fresh ( -- ) lfn-fresh lft-reset ;
' lft-fresh is lfa-declaration-fresh

\ Positions: just past the current token; the next step's text from there.
: lft-past ( -- pos ) lfa-here lfa-pos> lfa-token nip + lfa-pos ;
: lft-from! ( -- ) lft-past lft-read-from! ;

\ Records. A new one claimed from a store the heap cannot grow stops the
\ run (full). Indices only: an address moves when its store grows.
: lft-claim ( store -- addr i )
  dup store-ready ok? lfa-e-tac-full lfa-must store-new-slot lfa-e-tac-full lfa-must ;
: lft-rec ( i -- addr ) tac-steps store-slot ;
: targ# ( -- n ) tac-args store-count @ ;
: lf-tactic-count ( -- n ) tac-steps store-count @ ;
: lf-tactic-step ( i -- addr ) lft-rec ;
: lf-tactic-arg ( j -- x pos ) tac-args store-slot dup targ-x @ swap targ-at @ ;
\ A new step of kind at the current token, in the open block, its text
\ from where the step before ended, its arguments to come.
: lft-blank ( addr -- addr ) dup /tac erase -1 over tac-to ! -1 over tac-arrow ! ;
: lft-where ( addr -- addr )
  lfa-here over tac-at ! lft-read-from over tac-from ! lft-open over tac-parent ! ;
: lft-new ( kind -- i )
  tac-steps lft-claim >r lft-blank lft-where targ# over tac-first ! tac-kind ! r> ;
: lft-arg+ ( i x pos -- i )
  tac-args lft-claim drop tuck targ-at ! targ-x ! 1 over lft-rec tac-count +! ;

\ Term arguments: the values v1 .. vn, as syntax nodes, are step i's next
\ n arguments, in order (the last value is on top).
: lft-blanks ( i n -- i ) 0 ?do 0 0 lft-arg+ loop ;
: lft-term! ( v j -- )
  swap lfn>syntax dup syn-at@ rot tac-args store-slot tuck targ-at ! targ-x ! ;
: lft-fill ( v1 .. vn first n -- )
  ?dup if over + 1- do i lft-term! -1 +loop else drop then ;
: lft-terms ( v1 .. vn i n -- ) tuck lft-blanks lft-rec tac-first @ swap lft-fill ;

\ The open block.
: lft-kind ( -- kind ) lft-open lft-rec tac-kind @ ;
: lft-open-at ( -- pos ) lft-open lft-rec tac-at @ ;
: lft-proof? ( -- flag ) lft-open 0< 0= lfa-inside? and ;
: lf-tactic-proof? ( -- flag ) lft-proof? ;
: lft-bracket? ( kind -- flag ) dup tac-k-rw = swap tac-k-rewrite = or ;
\ Block i is open: the next step's text begins past the current token.
: lft-opened ( i -- ) lft-open! lft-from! false lft-hyp! ;
\ The open block ends at pos; the block around it is open again.
: lft-close ( pos -- )
  lft-open lft-rec tuck tac-to ! tac-parent @ lft-open! false lft-hyp! ;
: lft-to! ( i -- ) lft-past swap lft-rec tac-to ! ;
: lft-done ( i -- ) lft-to! lft-from! ;
: lft-inner+ ( -- ) 1 lft-open lft-rec tac-inner +! ;
: lft-tactic-new ( kind -- i ) lft-inner+ lft-new ;

\ Before a tactic word: in a tactic proof, outside by-rw[ ] (the error
\ names the word, and by-rw[ as the second place), no binder open.
: lft-in-proof ( -- ) lft-proof? lfa-e-tac-outside lfa-must ;
: lft-unbracketed ( -- )
  lft-kind lft-bracket? if lft-open-at lfa-e-tac-open lfa-fail-see then ;
: lft-ready ( -- ) lft-in-proof lft-unbracketed lfa-same-binders ;
\ Right inside by-induction-with comes an alternative; a tactic there is
\ Lean's pre-tactic (induction t with tac | ...), not supported yet.
: lft-not-pre ( -- ) lft-kind tac-k-with = if lfa-e-tactic lfa-fail then ;
\ Exactly want values above the frame. Too few is a mistake; too many
\ too, unless a hypothesis read since the last tactic word (taken as
\ taking none) may take some: not supported yet. A word that takes none
\ finds every value left, whatever a hypothesis takes.
: lft-count-code ( found want -- code )
  tuck > swap 0> and lft-hyp? and if lfa-e-tac-arity else lfa-e-tac-values then ;
: lft-count ( found want -- ) 2dup = if 2drop exit then lft-count-code lfa-fail ;
: lft-takes ( want -- ) >r lfa-above r> lft-count false lft-hyp! ;
: lft-tactic ( want -- ) lft-ready lft-not-pre lft-takes ;

\ Tactics.
: lft-term-step ( t kind -- i ) lft-tactic-new tuck 1 lft-terms ;
: lft-w-rfl ( -- ) 0 lft-tactic tac-k-rfl lft-tactic-new lft-done ;
: lft-w-exact ( t -- ) 1 lft-tactic tac-k-exact lft-term-step lft-done ;
: lft-w-induction ( t -- ) 1 lft-tactic tac-k-induction lft-term-step lft-done ;
: lft-w-with ( t -- ) 1 lft-tactic tac-k-with lft-term-step lft-opened ;
: lft-bracket ( kind -- ) lft-tactic-new lft-opened ;
: lft-w-rw ( -- ) 0 lft-tactic tac-k-rw lft-bracket ;
: lft-w-rewrite ( -- ) 0 lft-tactic tac-k-rewrite lft-bracket ;
\ ] : the rules are the values built since by-rw[ (or by-rewrite[).
: lft-in-bracket ( -- )
  lft-in-proof lft-kind lft-bracket? lfa-e-tac-closer lfa-must lfa-same-binders ;
: lft-rules ( v1 .. vn -- ) lfa-above lft-open swap lft-terms ;
: lft-w-bracket-end ( v1 .. vn -- )
  lft-in-bracket lft-rules lft-past lft-close lft-from! ;

\ Names given to hypotheses: _, or a name that is no LeanForth word,
\ which the block's text can use until the block ends (groups.fs).
: lft-hole? ( c-addr u -- flag ) s" _" lfa-token= ;
: lft-syntax-word? ( c-addr u -- flag )
  2dup lf-words search-wordlist 0= if 2drop false exit then
  >body lfa-syntax-name lfa-token= ;
: lft-no-word ( c-addr u -- c-addr u )
  2dup lft-syntax-word? 0= lfa-e-tac-header lfa-must ;
: lft-entry! ( c-addr u j -- )
  >r lf-locals lfa-entry-new lfa-entry-hypothesis r> rot lfa-entry-set ;
: lft-hypothesis ( i c-addr u -- i )
  lfa-word-name 2dup targ# lft-entry! lfa-intern lfa-here lft-arg+ ;
: lft-inaccessible ( i -- i ) 0 lfa-here lft-arg+ ;
: lft-given ( i c-addr u -- i )
  2dup lft-hole? if 2drop lft-inaccessible exit then lft-no-word lft-hypothesis ;
: lft-w-intro ( -- )
  0 lft-tactic tac-k-intro lft-tactic-new lfa-name-token lft-given lft-done ;

\ Headers: TAG NAMES... => on the opener's line. A line that ends first
\ stops the run at the last token read (=> is missing).
: lft-next ( -- c-addr u ) parse-name dup if 2dup lfa-token! then ;
: lft-header-token ( -- c-addr u ) lft-next dup 0<> lfa-e-tac-header lfa-must ;
: lft-arrow? ( c-addr u -- flag ) s" =>" lfa-token= ;
: lft-bar? ( c-addr u -- flag ) s" |" lfa-token= ;
\ The tag: a name. Lean's wildcard _ and @TAG (every field explicit) are
\ not supported yet.
: lft-tag-later? ( c-addr u -- flag ) 2dup lft-hole? -rot drop c@ [char] @ = or ;
: lft-tag ( c-addr u -- name )
  2dup lft-tag-later? if lfa-e-tactic lfa-fail then lft-no-word lfa-word-name lfa-intern ;
\ The names: | before => is a second tag (| a | b =>), not supported yet.
: lft-name ( i c-addr u -- i ) 2dup lft-bar? if lfa-e-tactic lfa-fail then lft-given ;
: lft-names ( i -- i )
  begin lft-header-token 2dup lft-arrow? 0= while lft-name repeat 2drop ;
: lft-entries! ( i -- i ) lfa-entry# over lft-rec tac-entries ! ;
: lft-tag! ( i -- i ) lft-header-token lft-tag over lft-rec tac-name ! ;
: lft-arrow! ( i -- i ) lfa-here over lft-rec tac-arrow ! ;
: lft-header ( kind -- ) lft-new lft-entries! lft-tag! lft-names lft-arrow! lft-opened ;

\ A block of names ends at pos: it held a tactic (else the error is at
\ the word that ends it, as Lean's parser reports), and its names go.
: lft-held ( addr -- addr ) dup tac-inner @ 0> lfa-e-tac-empty lfa-must ;
: lft-names-end ( pos -- )
  lft-open lft-rec lft-held tac-entries @ lfa-entries-cut lft-close ;
\ An alternative ends with its last tactic, at the next | or by-end.
: lft-alt-end ( -- ) lft-kind tac-k-alt = if lft-read-from lft-names-end then ;
: lft-in-with ( -- ) lft-kind tac-k-with = lfa-e-tac-closer lfa-must ;
: lft-w-bar ( -- ) lft-ready 0 lft-takes lft-alt-end lft-in-with tac-k-alt lft-header ;
: lft-w-case ( -- ) 0 lft-tactic lft-inner+ tac-k-case lft-header ;
: lft-block-end ( kind -- )
  case tac-k-with of lft-past lft-close endof tac-k-case of lft-past lft-names-end endof
    lfa-e-tac-closer lfa-fail endcase ;
: lft-w-by-end ( -- ) lft-ready 0 lft-takes lft-alt-end lft-kind lft-block-end lft-from! ;
: lft-w-arrow ( -- ) lft-in-proof lfa-e-tac-header lfa-fail ;

\ := by opens the proof; its end NAME needs every block closed and no
\ value left, and then the tactics would run (plan FE1g-3): the error
\ names end, and by as the second place. A declaration without by ends
\ as the reader's does (reader.fs).
: lft-w-by ( -- ) lfn-w-by lfa-here lft-read-from! tac-k-by lft-new lft-opened ;
: lft-closed ( -- )
  lft-kind tac-k-by = if exit then lft-open-at lfa-e-tac-open lfa-fail-see ;
: lft-unrun ( pos -- ) lft-open-at swap lft-close lfa-e-tac-run lfa-fail-see ;
\ The position just past end's NAME, which is the proof's end.
: lft-name-past ( c-addr u -- c-addr u pos ) 2dup + lfa-token-pos ;
: lft-end-proof ( above c-addr u -- )
  lft-name-past >r lfa-end-check lft-closed lfa-proof-ready 0 lft-count r> lft-unrun ;
: lft-end-declaration ( above c-addr u -- )
  lft-proof? if lft-end-proof else lfn-end-declaration then ;
: lft-w-end ( -- ) lfa-end-head ['] lft-end-declaration lfa-end-tail ;

\ Hypotheses, read (groups.fs): the newest entry of the token's spelling
\ if it is a hypothesis; entries are one array, so the newer has the
\ higher address. Its node takes no values (a pending ' is spent).
: lft-entry-of ( body kind -- entry|0 ) lfa-token-find 0= if 0 then ;
: lft-newest ( body -- entry|0 )
  dup lfa-entry-hypothesis lft-entry-of swap lfa-entry-variable lft-entry-of over u< and ;
: lft-hyp-node ( j -- node )
  dup tac-args store-slot targ-x @ syn-k-hyp lfa-here lfn-new swap syn-a! swap syn-b! ;
: lft-hyp-value ( j -- value ) lfa-untick drop lft-hyp-node lfn-value true lft-hyp! ;
: lft-hyp-run ( body -- body false | value true )
  dup lft-newest ?dup 0= if false exit then nip lfa-entry-value @ lft-hyp-value true ;
' lft-hyp-run is lfa-hypothesis-run

\ The natural meanings (author/groups.fs, lfa-natural!).
' lft-w-by lfa-natural! by
' lft-w-end lfa-natural! end
' lft-w-rfl lfa-natural! by-rfl
' lft-w-exact lfa-natural! by-exact
' lft-w-intro lfa-natural! by-intro:
' lft-w-induction lfa-natural! by-induction
' lft-w-with lfa-natural! by-induction-with
' lft-w-case lfa-natural! by-case:
' lft-w-bar lfa-natural! |
' lft-w-arrow lfa-natural! =>
' lft-w-by-end lfa-natural! by-end
' lft-w-rw lfa-natural! by-rw[
' lft-w-rewrite lfa-natural! by-rewrite[
' lft-w-bracket-end lfa-natural! ]

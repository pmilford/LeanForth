\ Tactic proofs, read (plan FE1g-2; design docs/design/FE1G_TACTICS.md
\ section 3, the owner's syntax of 2026-11-12): the natural meanings of
\ the words of a proof after := by. They are read, checked for shape and
\ recorded; a tactic proof whose blocks all close is run at its end NAME
\ (lf-tactic-proof-end, which src/front/tactic-run.fs sets: plan
\ FE1g-3), as Lean parses a declaration whole before it elaborates it.
\ The words, in the order Lean writes them:
\   t by-exact, t by-induction, t by-induction-with   take one value each;
\   by-rfl, by-sorry, by-intro: NAME (_ for an inaccessible hypothesis);
\   by-rw[ r1 .. rn ], by-rewrite[ r1 .. rn ]   the values built between
\     the brackets are the rules, in order (none is allowed, as in Lean);
\     every value is a rule: a hypothesis there takes no values, and one
\     applied is written with $ (ih k $ is Lean's rw [ih k]);
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
\ takes, none left (86; 87 instead when, outside by-rw[ ], a hypothesis
\ was read with values below it, which it could take: how many values a
\ hypothesis takes is known only once its tactic runs, so ih k by-exact
\ is 86, k ih by-exact 87); a header's tokens on its line, its tag and
\ names names and no words (84), the tag not _ or @TAG and no second tag
\ (72: Lean's wildcard, @ and | a | b forms, plan FE5); an alternative or
\ case block holds a tactic (85, at the word that ends it, and its => as
\ the second place, where Lean's parser reports it); by-end, ] and | only
\ where their block is open (83); end NAME with every block closed (82,
\ and the open block's place) and no value left (86). Without the runner
\ end NAME stops there, not supported yet (80, and by as the second place).
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
\ past the step before it (the proof: from its by) to just past its last
\ word (a block's closing word, end NAME's name for the proof; an
\ alternative's last tactic; -1 while open); tac-arrow, a
\ header's => (else -1); tac-name, a header's tag (a name ID, else 0);
\ tac-first and tac-count, its arguments; tac-inner, the tactics right
\ inside a block; tac-entries, the names in scope before a header's (an
\ index of the reader's entry store, for this run only: no serialized
\ form, FE1g-7, carries it).
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
\ lf-tactic-arg ( j -- x pos ) (unchecked), the kinds and fields above;
\ lf-tactic-proof-end ( -- ), deferred: what end NAME does with a proof
\ read whole, its by block closed (the runner's, tactic-run.fs).
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
11 constant tac-k-sorry      \ by-sorry (Lean's sorry tactic)

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
\ Forth's interpreter runs the text a word at a time and the data stack
\ holds the author's values, so what one word leaves for the next lives
\ here, in the checker context (ADR 0009), for one declaration.
begin-structure /tac-read
  field: tac-read-open      \ the innermost open block, or -1
  field: tac-read-from      \ where the next step's text begins
  field: tac-read-hyp       \ true: a hypothesis read since the last tactic
                            \ word may take values below it
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
\ A declaration starts: what the hook did before (the reader's trees and
\ metavariables, reader.fs), and the record is new.
action-of lfa-declaration-fresh constant lft-fresh-before
: lft-fresh ( -- ) lft-fresh-before execute lft-reset ;
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
: lft-bracket? ( kind -- flag ) tac-k-rw tac-k-rewrite one-of2? ;
\ Block i is open: the next step's text begins past the current token.
: lft-opened ( i -- ) lft-open! lft-from! ;
\ The open block ends at pos; the block around it is open again.
: lft-close ( pos -- ) lft-open lft-rec tuck tac-to ! tac-parent @ lft-open! ;
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
\ taking none) had values below it, which it may take: not supported yet.
\ A word that takes none finds a value left whatever a hypothesis takes,
\ since a term leaves one value. The doubt ends with each tactic word.
: lft-extra? ( found want -- flag ) tuck > swap 0> and ;
: lft-count-code ( found want -- code )
  lft-extra? lft-hyp? and if lfa-e-tac-arity else lfa-e-tac-values then ;
: lft-count ( found want -- ) 2dup = if 2drop exit then lft-count-code lfa-fail ;
: lft-takes ( want -- ) >r lfa-above r> lft-count false lft-hyp! ;
: lft-tactic ( want -- ) lft-ready lft-not-pre lft-takes ;

\ Tactics.
: lft-term-step ( t kind -- i ) lft-tactic-new tuck 1 lft-terms ;
\ (A word checks the values above the frame before it puts anything on
\ the stack, so the kind comes after lft-tactic.)
: lft-plain ( kind -- ) lft-tactic-new lft-done ;
: lft-w-rfl ( -- ) 0 lft-tactic tac-k-rfl lft-plain ;
: lft-w-sorry ( -- ) 0 lft-tactic tac-k-sorry lft-plain ;
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

\ Shapes (tactic plug-in design 3.2): how the word of a tactic that
\ registers itself (tactic-api.fs's lf-tactic:) is read. A shape is a
\ record: the values the word takes, then its builder ( v1 .. vn kind
\ -- ), which records the step. tac-shape-plain takes none (by-rfl's
\ shape), tac-shape-term one term (by-exact's). Shapes with headers,
\ names, rules or blocks are core work of their own branch.
begin-structure /lft-shape
  field: shape-want
  field: shape-build
end-structure
: lft-term-done ( t kind -- ) lft-term-step lft-done ;
create tac-shape-plain 0 , ' lft-plain ,
create tac-shape-term 1 , ' lft-term-done ,
\ A registered word of kind and shape is read so: the values above the
\ frame checked before the kind is put on the stack (as lft-w-exact does).
: lft-read-as ( kind shape -- )
  swap >r >r r@ shape-want @ lft-tactic r> r> swap shape-build @ execute ;

\ Names given to hypotheses: _, or a name that is no LeanForth word,
\ which the block's text can use until the block ends (groups.fs).
: lft-hole? ( c-addr u -- flag ) s" _" lfa-token= ;
\ The LeanForth words are the printer's reserved list (words.fs checks
\ each against it), which needs no name lookup in the front end.
: lft-no-word ( c-addr u -- c-addr u ) 2dup lf-pf-reserved? 0= lfa-e-tac-header lfa-must ;
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
: lft-at-sign? ( c-addr u -- flag ) drop 1 s" @" lfa-token= ;
: lft-tag-later? ( c-addr u -- flag ) 2dup lft-hole? -rot lft-at-sign? or ;
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

\ A block of names ends at pos: it held a tactic, and its names go. An
\ empty one stops the run at the word that ends it, with its => as the
\ second place (pinned Lean's parser reports just past =>).
: lft-held ( addr -- addr )
  dup tac-inner @ 0> if exit then dup tac-arrow @ lfa-e-tac-empty lfa-fail-see ;
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
\ value left, and then the tactics run (lf-tactic-proof-end; without the
\ runner, error 80 names end, and by as the second place). A declaration
\ without by ends as the reader's does (reader.fs).
: lft-w-by ( -- ) lfn-w-by lfa-here lft-read-from! tac-k-by lft-new lft-opened ;
\ The block by-end would close: an alternative's is its by-induction-with.
: lft-block ( -- addr )
  lft-open lft-rec dup tac-kind @ tac-k-alt = if tac-parent @ lft-rec then ;
: lft-closed ( -- )
  lft-kind tac-k-by = if exit then lft-block tac-at @ lfa-e-tac-open lfa-fail-see ;
\ The proof read whole (its block closed) goes to the runner.
: lft-unrun ( -- ) 0 lft-rec tac-at @ lfa-e-tac-run lfa-fail-see ;
defer lf-tactic-proof-end ( -- )
' lft-unrun is lf-tactic-proof-end
\ The position just past end's NAME, which is the proof's end.
: lft-name-past ( c-addr u -- c-addr u pos ) 2dup + lfa-token-pos ;
: lft-end-proof ( above c-addr u -- )
  lft-name-past >r lfa-end-check lft-closed lfa-proof-ready 0 lft-count r> lft-close
  lf-tactic-proof-end ;
: lft-end-declaration ( above c-addr u -- )
  lft-proof? if lft-end-proof else lfn-end-declaration then ;
: lft-w-end ( -- ) lfa-end-head ['] lft-end-declaration lfa-end-tail ;

\ Hypotheses, read (groups.fs): the token's hypothesis entry when it is
\ newer than every variable entry of the spelling (entries are one array,
\ so the newer has the higher address), else 0. Its node takes no values
\ (a pending ' is spent); read with values below it outside by-rw[ ],
\ it may take some once tactics run, which leaves a doubt (lft-count).
: lft-entry-of ( body kind -- entry|0 ) lfa-token-find 0= if 0 then ;
: lft-newer ( body -- entry|0 )
  dup lfa-entry-hypothesis lft-entry-of swap lfa-entry-variable lft-entry-of over u< and ;
: lft-bracketed? ( -- flag ) lft-proof? if lft-kind lft-bracket? else false then ;
: lft-may-take? ( -- flag ) lfa-above 0> lft-bracketed? 0= and ;
: lft-doubt ( -- ) lft-may-take? lft-hyp? or lft-hyp! ;
: lft-hyp-node ( j -- node )
  dup tac-args store-slot targ-x @ syn-k-hyp lfa-here lfn-new swap syn-a! swap syn-b! ;
: lft-hyp-value ( j -- value ) >r lft-doubt r> lfa-untick drop lft-hyp-node lfn-value ;
: lft-hyp-run ( body -- body false | value true )
  dup lft-newer ?dup 0= if false exit then nip lfa-entry-value @ lft-hyp-value true ;
' lft-hyp-run is lfa-hypothesis-run

\ The natural meanings (author/groups.fs, lfa-natural!).
' lft-w-by lfa-natural! by
' lft-w-end lfa-natural! end
' lft-w-rfl lfa-natural! by-rfl
' lft-w-sorry lfa-natural! by-sorry
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

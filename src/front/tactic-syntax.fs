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
\     applied is written with $ (ih k $ is Lean's rw [ih k]); <- right
\     after a rule makes it right to left (Lean's rw [← h]: ' h <-);
\   | TAG NAMES... =>   an alternative of the by-induction-with block it is
\     right inside, up to the next | or the block's by-end;
\   by-case: TAG NAMES... =>   a case block, up to its by-end (TAG _ the
\     main goal, Lean's case _); by-next NAMES... => the same with the tag
\     _ (Lean's next, a macro of case _: its step is a by-case: step);
\   by-end   closes the innermost by-induction-with or by-case: block;
\   =>   ends a header; anywhere else it is an error.
\ The shape, each failure an error at the word's line and column (codes
\ in author/errors.fs): a tactic word only in a tactic proof (81); none
\ inside a list (by-rw[ ], << >>: its closing word is missing, 458 at the
\ list's word, author/scopes.fs; plan row TB2, batch 3c, which lets a
\ list run over several lines); none before the first |
\ of a by-induction-with (Lean's pre-tactic, with tac: not supported yet,
\ 72); no binder of a term left open (21); exactly the values the word
\ takes, none left (86; 87 instead when, outside by-rw[ ], a hypothesis
\ was read with values below it, which it could take: how many values a
\ hypothesis takes is known only once its tactic runs, so ih k by-exact
\ is 86, k ih by-exact 87); a header's tokens on its line, its tag and
\ names names and no words (84), the tag not _ or @TAG and no second tag
\ (72: Lean's wildcard alternative, @ and | a | b forms, plan FE5;
\ by-case:'s tag may be _, Lean's case _); <- only right after a rule
\ inside a bracket of rules (83
\ outside one, 86 with no rule before it, as Lean's parser wants a term
\ after ←); an alternative or
\ case block holds a tactic (85, at the word that ends it, and its => as
\ the second place, where Lean's parser reports it); by-end, ] and | only
\ where their block is open (83); end NAME with every list closed (458)
\ and every block closed (82, and the open block's place) and no value
\ left (86). Without the runner
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
\ form, FE1g-7, carries it); tac-shape, the shape its word was read by
\ (below; 0 for by; tac-shape-with and tac-shape-headed for the fixed
\ blocks, which their own words read); tac-word, the word it was written
\ with when that is not its kind's (a counted string: by-next's, a
\ by-case: step; else 0), for its errors and the step log;
\ tac-then, true when <;> follows it (below, plan row TB2, blocks slice 2).
\ Argument fields: targ-x, the syntax node of a term (by-exact's,
\ by-induction's, a rule) or the name ID of a hypothesis (0 for _),
\ targ-at, its position, targ-symm, true for a rule written right to
\ left (<-, Lean's ←), and targ-span, a pattern item's span (the
\ arguments its node covers, itself included; pattern-syntax.fs), else
\ 0. Positions are author/source.fs's. The parent links are the stack of
\ open blocks, so nesting is limited only by the
\ heap. Only positions are kept, not the text: reading a block again
\ (FE5's combinators) is the runner's to arrange (plan FE1g-3).
\
\ Untrusted: a record says what was written; tactics will only ever build
\ a term for the kernel to check. The words live in LF-WORDS
\ (author/words.fs) and the hypotheses in LF-LOCALS, so no Forth word
\ becomes reachable from the text.
\ Words: lf-tactic-proof? ( -- flag ), lf-tactic-count ( -- n ),
\ lf-tactic-step ( i -- addr ) (unchecked, valid until the next step),
\ lf-tactic-arg ( j -- x pos ) (unchecked), lf-tactic-arg-symm? ( j --
\ flag ) (unchecked: argument j a rule written right to left),
\ lf-tactic-arg-span ( j -- n ) (unchecked: its span), the kinds
\ and fields above;
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
  field: tac-shape        \ the shape it was read by (lft-read-as), else 0
  field: tac-word         \ its word when not its kind's (a counted string), else 0
  field: tac-loc          \ its at[ ] (lft-w-at): 0 none, else tac-loc-* flags
  field: tac-loc#         \ the hypothesis names of its at[ ], after its arguments
  field: tac-then         \ true: <;> follows it, a then-block its next step (lft-w-then)
end-structure
begin-structure /targ
  field: targ-x
  field: targ-at
  field: targ-symm      \ a rule written right to left (<-)
  field: targ-span      \ a pattern item's span (pattern-syntax.fs), else 0
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
: lf-tactic-arg-symm? ( j -- flag ) tac-args store-slot targ-symm @ ;
: lf-tactic-arg-span ( j -- n ) tac-args store-slot targ-span @ ;
\ A new step of kind at the current token, in the open block, its text
\ from where the step before ended, its arguments to come.
: lft-blank ( addr -- addr ) dup /tac erase -1 over tac-to ! -1 over tac-arrow ! ;
: lft-where ( addr -- addr )
  lfa-here over tac-at ! lft-read-from over tac-from ! lft-open over tac-parent ! ;
: lft-new ( kind -- i )
  tac-steps lft-claim >r lft-blank lft-where targ# over tac-first ! tac-kind ! r> ;
\ A new argument record, its fields 0 (a rule left to right).
: lft-arg-new ( -- addr ) tac-args lft-claim drop dup /targ erase ;
: lft-arg! ( x pos -- ) lft-arg-new targ-x cell-pair! ;
: lft-arg+ ( i x pos -- i ) lft-arg! 1 over lft-rec tac-count +! ;

\ Term arguments: the values v1 .. vn, as syntax nodes, are step i's next
\ n arguments, in order (the last value is on top), after those it has.
: lft-blanks ( i n -- i ) 0 ?do 0 0 lft-arg+ loop ;
: lft-term! ( v j -- )
  swap lfn>syntax dup syn-at@ rot tac-args store-slot tuck targ-at ! targ-x ! ;
: lft-fill ( v1 .. vn first n -- )
  ?dup if over + 1- do i lft-term! -1 +loop else drop then ;
: lft-arg-next ( i -- j ) lft-rec dup tac-first @ swap tac-count @ + ;
: lft-terms ( v1 .. vn i n -- ) tuck lft-blanks lft-arg-next over - swap lft-fill ;

\ The open block.
: lft-kind ( -- kind ) lft-open lft-rec tac-kind @ ;
: lft-open-at ( -- pos ) lft-open lft-rec tac-at @ ;
: lft-proof? ( -- flag ) lft-open 0< 0= lfa-inside? and ;
: lf-tactic-proof? ( -- flag ) lft-proof? ;
\ Block i is open: the next step's text begins past the current token.
: lft-opened ( i -- ) lft-open! lft-from! ;
\ The open block ends at pos; the block around it is open again.
: lft-close ( pos -- ) lft-open lft-rec tuck tac-to ! tac-parent @ lft-open! ;
: lft-to! ( i -- ) lft-past swap lft-rec tac-to ! ;
: lft-done ( i -- ) lft-to! lft-from! ;
: lft-inner+ ( -- ) 1 lft-open lft-rec tac-inner +! ;
: lft-tactic-new ( kind -- i ) lft-inner+ lft-new ;

\ Names given to hypotheses: _ (namespaces.fs's lfa-underscore?), or a name
\ that is no LeanForth word, which the block's text can use until the
\ block ends (groups.fs). The LeanForth words are the printer's reserved
\ list (words.fs checks each against it), which needs no name lookup in
\ the front end.
: lft-no-word ( c-addr u -- c-addr u ) 2dup lf-pf-reserved? 0= lfa-e-tac-header lfa-must ;
: lft-entry! ( c-addr u j -- )
  >r lf-locals lfa-entry-new lfa-entry-hypothesis r> rot lfa-entry-set ;
: lft-hypothesis ( i c-addr u -- i )
  lfa-word-name 2dup targ# lft-entry! lfa-intern lfa-here lft-arg+ ;
: lft-inaccessible ( i -- i ) 0 lfa-here lft-arg+ ;
: lft-given ( i c-addr u -- i )
  2dup lfa-underscore? if 2drop lft-inaccessible exit then lft-no-word lft-hypothesis ;
\ k names after the word, each on its line (a missing one: error 2).
: lft-names-after ( i k -- i ) 0 ?do lfa-name-token lft-given loop ;
\ The next token on the line, current (none: an empty string).
: lft-next ( -- c-addr u ) parse-name dup if 2dup lfa-token! then ;

\ Shapes (tactic plug-in design 3.2; plan row TB2, tactic batch 2): how a
\ tactic word is read, as data, by the built-in words and by those a
\ tactic file registers (tactic-api.fs's lf-tactic:). A shape is a
\ record: the values the word takes before it, the names it takes after
\ it, and its builder ( v1 .. vn i shape -- ), which fills the new step
\ i (the record's last, its kind and shape set, in the open block):
\   tac-shape-terms ( n -- shape )  n values (tac-shape-plain none,
\       by-rfl's; tac-shape-term one, by-exact's), the last on top;
\   tac-shape-term-names ( n k -- shape )  n values, then k names after
\       the word on its line (Lean's binder names; tac-shape-name, 0 1,
\       is by-intro:'s, tac-shape-decl, 2 1, by-have:'s: T e by-have: h;
\       _ an inaccessible one), each a hypothesis until the block ends,
\       as by-intro:'s;
\   tac-shape-term-this ( n -- shape )  n values, and the hypothesis
\       this (Lean's name when none is given: have := e);
\   tac-shape-rules  by-x[ ... ]: no value; the word opens a bracket whose
\       values up to ] are its rules, in order (by-rw['s), each one left to
\       right or, followed by <-, right to left;
\   tac-shape-list  by-x[ ... ]: the same, its values terms (no <-:
\       Lean's exacts [e1, e2]); tac-shape-list+ the same with one term at
\       least (460; Lean's term,+: by-exists['s, batch 3c);
\   tac-shape-binders  by-x[ NAMES ]: no value; the names up to ], each a
\       hypothesis as by-intro:'s (_ an inaccessible one), none at all
\       allowed (by-intro['s; Lean's bare intro); tac-shape-binders+ the
\       same with one name at least (by-rename-i['s);
\   tac-shape-hyps  by-x[ NAMES ]: no value; the names up to ] of
\       hypotheses the goal has, one at least, _ refused (459;
\       by-revert['s, by-clear['s);
\   tac-shape-new ( n k xt -- shape )  a shape of n values and k names
\       built by xt ( v1 .. vn i shape -- ), for a reader of its own
\       (pattern-syntax.fs's tac-shape-pattern, plan row TB2 piece E);
\   tac-shape-at ( shape -- shape )  the shape made to take a trailing
\       at[ as well (below): tac-shape-plain-at and tac-shape-term-at are
\       tac-shape-plain's and tac-shape-term's so (by-symm's, by-change's,
\       by-delta's), and tac-shape-rules takes one (rw's, rwa's).
\ Arguments, in order: the values, then the names. A list sits between
\ its bracket word and ], on as many lines as it needs (the owner's rules
\ of 2026-11-22: a list never ends at the end of a line, and may run over
\ lines; plan row TB2, batch 3c); a list whose ] never comes, before a
\ word that is never its item, end NAME, := or the text's end, stops the
\ run at its word, 458; an empty list Lean's parser refuses is 460.
begin-structure /lft-shape
  field: shape-want      \ the values before the word
  field: shape-names     \ the names after it
  field: shape-build     \ ( v1 .. vn i shape -- )
  field: shape-at        \ true: a trailing at[ may follow (tac-shape-at)
  field: shape-some      \ true: a list of one item at least (tac-shape-list+)
  field: shape-block     \ a block's flags (tac-shape-block, below), else 0
end-structure
: tac-shape-new ( n k xt -- shape )
  align here /lft-shape allot dup /lft-shape erase
  tuck shape-build ! tuck shape-names ! tuck shape-want ! ;
\ The shape made to take a location too (Lean's (location)? after it).
: tac-shape-at ( shape -- shape ) true over shape-at ! ;
: lft-shape@ ( i -- shape ) lft-rec tac-shape @ ;
\ The values made step i's arguments, i and its shape kept.
: lft-values ( v1 .. vn i shape -- i shape ) 2dup 2>r shape-want @ lft-terms 2r> ;
: lft-build-terms ( v1 .. vn i shape -- ) lft-values drop lft-done ;
: lft-build-names ( v1 .. vn i shape -- )
  lft-values shape-names @ lft-names-after lft-done ;
: lft-build-this ( v1 .. vn i shape -- )
  lft-values drop s" this" lft-hypothesis lft-done ;
\ Every bracket list is an author bracket (author/scopes.fs) up to its ]:
\ its values its own, its word the place of error 458 when no ] comes.
: lft-close-square ( -- closer ) c" ]" ;
: lft-list-open ( -- ) lft-close-square lfa-bracket-open ;
: lft-build-rules ( i shape -- ) drop lft-opened lft-list-open ;
\ Lists of names (plan row TB2, tactic batch 3b; over several lines since
\ batch 3c): the tokens after the word up to ], read by lft-list-name,
\ reading on into the next lines (author/runner.fs's lfa-token-on). A
\ LeanForth word that is no item of a list of names (any but _, * and
\ ]) and the text's end stop the list: its ] is missing, error 458 at
\ its word (scopes.fs's lfa-list-unclosed).
459 outcome-invalid s" by-revert[ and by-clear[ take names of hypotheses up to ]"
  lfa-code: lfa-e-tac-hyp-names
460 outcome-invalid s" this list takes one item at least" lfa-code: lfa-e-tac-list-empty
: lft-closer? ( c-addr u -- flag ) s" ]" lfa-token= ;
: lft-star? ( c-addr u -- flag ) s" *" lfa-token= ;
: lft-item-word? ( c-addr u -- flag )
  2dup lfa-underscore? if 2drop true exit then
  2dup lft-star? if 2drop true exit then lft-closer? ;
: lft-stops? ( c-addr u -- flag )
  dup 0= if 2drop true exit then
  2dup lf-pf-reserved? if lft-item-word? 0= else 2drop false then ;
: lft-list-token ( -- c-addr u ) lfa-token-on 2dup lft-stops? if lfa-list-unclosed then ;
: lft-list-name ( -- c-addr u true | false )
  lft-list-token 2dup lft-closer? if 2drop lfa-bracket-drop false else true then ;
\ A hypothesis named: no LeanForth word (_ is a reserved word too).
: lft-loc-name? ( c-addr u -- flag ) lf-pf-reserved? 0= ;
: lft-hyp-ref ( i c-addr u -- i )
  2dup lft-loc-name? lfa-e-tac-hyp-names lfa-must lfn-name-id lfa-here lft-arg+ ;
: lft-binders] ( i -- i ) begin lft-list-name while lft-given repeat ;
: lft-hyps] ( i -- i ) begin lft-list-name while lft-hyp-ref repeat ;
: lft-some ( i -- i ) dup lft-rec tac-count @ 0> lfa-e-tac-list-empty lfa-must ;
: lft-build-binders ( i shape -- ) drop lft-list-open lft-binders] lft-done ;
: lft-build-binders+ ( i shape -- ) drop lft-list-open lft-binders] lft-some lft-done ;
: lft-build-hyps ( i shape -- ) drop lft-list-open lft-hyps] lft-some lft-done ;
: tac-shape-terms ( n -- shape ) 0 ['] lft-build-terms tac-shape-new ;
: tac-shape-term-names ( n k -- shape ) ['] lft-build-names tac-shape-new ;
: tac-shape-term-this ( n -- shape ) 0 ['] lft-build-this tac-shape-new ;
0 tac-shape-terms constant tac-shape-plain
1 tac-shape-terms constant tac-shape-term
0 tac-shape-terms tac-shape-at constant tac-shape-plain-at
1 tac-shape-terms tac-shape-at constant tac-shape-term-at
0 1 tac-shape-term-names constant tac-shape-name
\ T e word: name, have's and let's.
2 1 tac-shape-term-names constant tac-shape-decl
0 0 ' lft-build-rules tac-shape-new tac-shape-at constant tac-shape-rules
0 0 ' lft-build-rules tac-shape-new constant tac-shape-list
0 0 ' lft-build-rules tac-shape-new true over shape-some ! constant tac-shape-list+
0 0 ' lft-build-binders tac-shape-new constant tac-shape-binders
0 0 ' lft-build-binders+ tac-shape-new constant tac-shape-binders+
0 0 ' lft-build-hyps tac-shape-new constant tac-shape-hyps
\ Whether the open block is a bracket of rules.
\ (A block read by no shape, by's or a header's, has shape 0.)
: lft-rules? ( -- flag ) lft-open lft-shape@ tac-shape-rules = ;

\ A block's flags (tac-shape-block, below): tac-block, tac-block-cuts
\ (names given inside it go at its end), tac-block-self (closed by its
\ own }), tac-block-one (one step, closed lazily: <;>'s then-block).
1 constant tac-block
2 constant tac-block-cuts
4 constant tac-block-self
8 constant tac-block-one
\ tac-block-bars: its steps are alternatives, each begun by | (by-
\ induction-with); tac-block-headed: its word reads a header TAG NAMES
\ => (an alternative, by-case:, by-next), its => where its errors are
\ told (plan row 9.4.8s, blocks slice 2: the fixed blocks on shapes too).
16 constant tac-block-bars
32 constant tac-block-headed
\ tac-block-bare: its alternatives are bare, | then tactics, no header
\ (by-first's: Lean's first | tacs | tacs, Init/Tactics.lean:429).
64 constant tac-block-bare
: lft-block-shape? ( shape|0 -- flag ) dup if shape-block @ 0<> then ;
: tac-shape-has? ( shape bit -- flag ) swap shape-block @ and 0<> ;
: lft-self-closing? ( shape -- flag ) tac-block-self tac-shape-has? ;
: lft-flags-of ( i -- flags ) lft-shape@ dup if shape-block @ then ;
: lft-has? ( i bit -- flag ) swap lft-flags-of and 0<> ;
: lft-open-flags ( -- flags ) lft-open lft-flags-of ;
: lft-open-has? ( bit -- flag ) lft-open swap lft-has? ;
: lft-bars? ( -- flag ) tac-block-bars lft-open-has? ;
\ An alternative: a headed block right inside a block of bars, closed by
\ the next | or that block's by-end.
: lft-parent@ ( j -- p ) lft-rec tac-parent @ ;
: lft-up-bars? ( -- flag ) lft-open lft-parent@ tac-block-bars lft-has? ;
: lft-headed? ( -- flag ) tac-block-headed lft-open-has? ;
: lft-alt? ( -- flag ) lft-open 0> if lft-up-bars? else false then ;
\ A shape's block flags (tac-block and flags); the fixed blocks' shapes,
\ read by their own words, not by lft-read-as (no builder): by's (in its
\ row only: the reader keeps the proof's step at 0), by-induction-with's
\ (its term) and a header's (an alternative's, by-case:'s, by-next's).
: tac-shape-flags ( shape flags -- shape ) tac-block or over shape-block ! ;
: lft-fixed-shape ( n flags -- shape ) swap 0 0 tac-shape-new swap tac-shape-flags ;
0 0 lft-fixed-shape constant tac-shape-by
1 tac-block-bars lft-fixed-shape constant tac-shape-with
0 tac-block-headed tac-block-cuts or lft-fixed-shape constant tac-shape-headed
: lft-shape! ( i shape -- i ) over lft-rec tac-shape ! ;
\ A block that ends holds a tactic: an empty one stops the run at the
\ word that ends it, its => (a brace's }, a then-block's <;>) the second
\ place (pinned Lean's parser reports just past =>).
: lft-held ( addr -- addr )
  dup tac-inner @ 0> if exit then dup tac-arrow @ lfa-e-tac-empty lfa-fail-see ;

\ Before a tactic word: in a tactic proof, no list open (its closing word
\ is missing: 458 at the list's word, scopes.fs), no binder open
\ (lft-poised; at[, which amends the step before it, asks no more), and
\ the then-block of a <;> closed once it holds its step (lft-settle).
\ A then-block (blocks slice 2, lft-w-then) is closed lazily, past its
\ step's text (lft-read-from), at the first token that cannot extend that
\ step: a tactic word, { or <;> when it holds its step (lft-settle), a
\ closer (}, by-end, |, end) always, an empty one there 85 at the closer,
\ its <;> second (lft-settled). Its names stay (Lean's all_goals keeps
\ them). No then-block is right inside another (a <;> there settles the
\ first, or finds no step before it, 468), so one settle a token does.
: lft-in-proof ( -- ) lft-proof? lfa-e-tac-outside lfa-must ;
: lft-poised ( -- ) lft-in-proof lfa-brackets-closed lfa-same-binders ;
: lft-one? ( -- flag ) tac-block-one lft-open-has? ;
: lft-holding? ( -- flag ) lft-open lft-rec tac-inner @ 0<> ;
: lft-then-close ( -- ) lft-open lft-rec lft-held drop lft-read-from lft-close ;
: lft-settled ( -- ) lft-one? if lft-then-close then ;
: lft-settle ( -- ) lft-one? lft-holding? and if lft-then-close then ;
: lft-ready ( -- ) lft-poised lft-settle ;
\ Right inside a block of bars comes an alternative; a tactic there is
\ Lean's pre-tactic (induction t with tac | ...), not supported yet.
: lft-not-pre ( -- ) lft-bars? if lfa-e-tactic lfa-fail then ;
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
\ Before a closer (}, by-end, |): the then-block closed (lft-settled), no value.
: lft-closing ( -- ) lft-poised lft-settled 0 lft-takes ;

\ Tactics. A word is read by its shape (lf-tactic: keeps a registered
\ word's in its row): the values above the frame checked before the
\ kind and shape are put on the stack, then the new step built.
: lft-checked ( kind shape -- kind shape ) 2>r 2r@ nip shape-want @ lft-tactic 2r> ;
: lft-shaped ( kind shape -- i shape ) swap lft-tactic-new 2dup lft-rec tac-shape ! swap ;
: lft-read-as ( v1 .. vn kind shape -- )
  lft-checked lft-shaped dup shape-build @ execute ;
: lft-w-rfl ( -- ) tac-k-rfl tac-shape-plain lft-read-as ;
: lft-w-sorry ( -- ) tac-k-sorry tac-shape-plain lft-read-as ;
: lft-w-exact ( t -- ) tac-k-exact tac-shape-term lft-read-as ;
: lft-w-induction ( t -- ) tac-k-induction tac-shape-term lft-read-as ;
: lft-w-intro ( -- ) tac-k-intro tac-shape-name lft-read-as ;
: lft-w-rw ( -- ) tac-k-rw tac-shape-rules lft-read-as ;
: lft-w-rewrite ( -- ) tac-k-rewrite tac-shape-rules lft-read-as ;
: lft-term-step ( t kind -- i ) lft-tactic-new tuck 1 lft-terms ;
: lft-with-step ( t -- i ) tac-k-with lft-term-step tac-shape-with lft-shape! ;
: lft-w-with ( t -- ) 1 lft-tactic lft-with-step lft-opened ;
\ ] : the rules are the values built since the bracket's word (by-rw[),
\ after those a <- took: the innermost bracket's items (none open: 83;
\ a << open inside: 458 at <<).
: lft-rules ( v1 .. vn n -- ) lft-open swap lft-terms ;
\ A list of one item at least (tac-shape-list+) with none is 460.
: lft-some-wanted? ( -- flag ) lft-open lft-shape@ shape-some @ ;
: lft-some? ( n -- n ) dup 0= lft-some-wanted? and 0= lfa-e-tac-list-empty lfa-must ;
: lft-bracket-items ( v1 .. vn -- v1 .. vn n )
  lft-in-proof lft-close-square lfa-e-tac-closer lfa-bracket-close drop lft-some? ;
: lft-w-bracket-end ( v1 .. vn -- )
  lft-bracket-items lft-rules lft-past lft-close lft-from! ;
\ <- : the values so far the bracket's rules, the last one right to left
\ (Lean's ←, rwRule's symm flag): right inside a bracket of rules (83),
\ after a rule (86).
: lft-symm! ( -- ) true lft-open lft-arg-next 1- tac-args store-slot targ-symm ! ;
: lft-in-rules ( -- )
  lft-in-proof lfa-list-closer lft-close-square = lft-rules? and lfa-e-tac-closer lfa-must
  lfa-same-binders ;
: lft-w-symm ( v1 .. vn -- )
  lft-in-rules lfa-above dup 0> lfa-e-tac-values lfa-must lft-rules lft-symm! ;

\ Headers: TAG NAMES... => on the opener's line. A line that ends first
\ stops the run at the last token read (=> is missing).
: lft-header-token ( -- c-addr u ) lft-next dup 0<> lfa-e-tac-header lfa-must ;
: lft-arrow? ( c-addr u -- flag ) s" =>" lfa-token= ;
: lft-bar? ( c-addr u -- flag ) s" |" lfa-token= ;
\ The tag: a name. Lean's wildcard _ and @TAG (every field explicit) are
\ not supported yet.
: lft-at-sign? ( c-addr u -- flag ) drop 1 s" @" lfa-token= ;
: lft-tag-later? ( c-addr u -- flag ) 2dup lfa-underscore? -rot lft-at-sign? or ;
: lft-tag ( c-addr u -- name )
  2dup lft-tag-later? if lfa-e-tactic lfa-fail then lft-no-word lfn-name-id ;
\ The names: | before => is a second tag (| a | b =>), not supported yet.
: lft-name ( i c-addr u -- i ) 2dup lft-bar? if lfa-e-tactic lfa-fail then lft-given ;
: lft-names ( i -- i )
  begin lft-header-token 2dup lft-arrow? 0= while lft-name repeat 2drop ;
: lft-entries! ( i -- i ) lfa-entry# over lft-rec tac-entries ! ;
: lft-name! ( i name -- i ) over lft-rec tac-name ! ;
: lft-tag! ( i -- i ) lft-header-token lft-tag lft-name! ;
\ by-case:'s tag may be _ (Lean's case _: the main goal), kept as 0.
: lft-case-tag ( c-addr u -- name ) 2dup lfa-underscore? 0= if lft-tag exit then 2drop 0 ;
: lft-case-tag! ( i -- i ) lft-header-token lft-case-tag lft-name! ;
: lft-arrow! ( i -- i ) lfa-here over lft-rec tac-arrow ! ;
: lft-headed ( i -- ) lft-names lft-arrow! lft-opened ;
: lft-headed-new ( kind -- i ) lft-new tac-shape-headed lft-shape! lft-entries! ;
: lft-header ( kind -- ) lft-headed-new lft-tag! lft-headed ;

\ A block of names ends at pos: it held a tactic (lft-held), and its
\ names go (with cut?, lft-block-close; always, lft-names-end).
: lft-cut-names ( addr -- ) tac-entries @ lfa-entries-cut ;
: lft-close-names ( pos addr cut? -- ) if lft-cut-names else drop then lft-close ;
: lft-block-close ( pos cut? -- ) lft-open lft-rec lft-held swap lft-close-names ;
: lft-names-end ( pos -- ) true lft-block-close ;
\ An alternative ends with its last tactic, at the next | or by-end, its
\ names cut when its shape says so (an induction's; not first's, whose
\ goals keep them, TACTIC_BLOCKS.md 2).
: lft-alt-cut ( -- ) lft-read-from tac-block-cuts lft-open-has? lft-block-close ;
: lft-alt-end ( -- ) lft-alt? if lft-alt-cut then ;
: lft-in-with ( -- ) lft-bars? lfa-e-tac-closer lfa-must ;
\ A bare alternative (by-first's): | and then its tactics; its | the
\ second place of an empty one's 85.
0 0 lft-fixed-shape constant tac-shape-alt
: lft-bare-alt ( -- )
  tac-k-alt lft-tactic-new tac-shape-alt lft-shape! lft-arrow! lft-opened ;
: lft-alt-new ( -- )
  tac-block-bare lft-open-has? if lft-bare-alt else tac-k-alt lft-header then ;
: lft-w-bar ( -- ) lft-closing lft-alt-end lft-in-with lft-alt-new ;
: lft-case-new ( -- i ) 0 lft-tactic lft-inner+ tac-k-case lft-headed-new ;
: lft-w-case ( -- ) lft-case-new lft-case-tag! lft-headed ;
\ by-next NAMES... => : Lean's next, the macro case _ NAMES => (Init/
\ Tactics.lean:348), a by-case: step whose tag is _ (0), spelt by-next.
: lft-next-word ( -- c-addr ) c" by-next" ;
: lft-word! ( i c-addr -- i ) over lft-rec tac-word ! ;
: lft-w-next ( -- ) lft-case-new lft-next-word lft-word! lft-headed ;

\ Blocks a word opens (plan row TB2, blocks slice 1; docs/design/
\ TACTIC_BLOCKS.md 2): tac-shape-block ( n k flags -- shape ), n values
\ and k names as tac-shape-term-names takes them, then the steps after
\ it are its block, up to by-end or, with tac-block-self, its own }
\ ({ ... }, Lean's tacticSeqBracketed). With tac-block-cuts the names
\ given inside it go at its end (Lean's done and nested blocks: { },
\ by-have-by:, whose own name stays after it), else they stay to the
\ end of the block around it (by-focus). An empty one is 85 at by-end
\ (Lean's parser wants a tactic after by and focus); { } is read, as
\ Lean's parser reads it, and its run is Lean's unsolved goals (89) or
\ no goals (90). lft-block-shape? ( shape|0 -- flag ) and
\ lft-self-closing? ( shape -- flag ), above, tell them (the runner's
\ record check and errors).
: lft-build-block ( v1 .. vn i shape -- )
  lft-values shape-names @ lft-names-after lft-entries! lft-opened ;
: tac-shape-block ( n k flags -- shape )
  0 0 ['] lft-build-block tac-shape-new swap tac-shape-flags
  tuck shape-names ! tuck shape-want ! ;
\ t1 <;> t2 (plan row TB2, blocks slice 2; Lean's macro focus (t1;
\ all_goals t2), Init/Tactics.lean:451-456): <;>, read by tac-shape-then
\ (tactics/blocks.fs's kind), takes no value and settles (lft-ready);
\ t1 is the last step right inside the open block (a closed block too,
\ such as by-induction-with ... by-end), marked tac-then, none 468; the
\ then-block opens after it (tac-block-one), its <;> its second place
\ (tac-arrow), and t2 is its one step, a tactic or a block ({ ... }, a
\ by- block). a <;> b <;> c is (a <;> b) <;> c, Lean's left association:
\ the second <;> settles the first's then-block and takes it as its t1.
468 outcome-invalid s" <;> follows no tactic of its block (t1 <;> t2)"
  lfa-code: lfa-e-tac-then
: lft-deeper? ( b j -- b j flag ) 2dup < if 2dup lft-parent@ <> else false then ;
\ (The steps after block b are inside it: from j up to b's child.)
: lft-child ( b j -- b j' ) begin lft-deeper? while lft-parent@ repeat ;
: lft-before ( i -- j ) dup lft-parent@ swap 1- lft-child tuck < lfa-e-tac-then lfa-must ;
: lft-then! ( j -- ) true swap lft-rec tac-then ! ;
: lft-build-then ( i shape -- ) drop dup lft-before lft-then! lft-arrow! lft-opened ;
0 0 ' lft-build-then tac-shape-new tac-block-one tac-shape-flags constant tac-shape-then
\ } closes the innermost block, which must be a brace (else 83, the open
\ block's place second); its place is the brace's tac-arrow (where its
\ unsolved goals are told, as Lean's withRef stx[2]), and its names go.
: lft-closer-at ( -- ) lft-open-at lfa-e-tac-closer lfa-fail-see ;
: lft-brace? ( -- flag ) tac-block-self lft-open-has? ;
: lft-in-brace ( -- ) lft-brace? 0= if lft-closer-at then ;
: lft-brace-close ( -- ) lft-past lft-open lft-arrow! lft-rec true lft-close-names ;
: lft-w-brace-end ( -- ) lft-closing lft-in-brace lft-brace-close lft-from! ;
\ by-end at a block a word opened: 83 at none (the proof's by) and at a
\ brace (its { second); else the block's end, its names cut when its
\ shape says so.
: lft-not-brace ( flags -- flags ) dup tac-block-self and if lft-closer-at then ;
: lft-word-end ( -- )
  lft-open-flags dup 0<> lfa-e-tac-closer lfa-must lft-not-brace
  lft-past swap tac-block-cuts and lft-block-close ;
\ (by-induction-with's alternatives may be none: no held check; first's not.)
: lft-with? ( -- flag ) lft-bars? tac-block-bare lft-open-has? 0= and ;
: lft-block-end ( -- ) lft-with? if lft-past lft-close else lft-word-end then ;
: lft-w-by-end ( -- ) lft-closing lft-alt-end lft-block-end lft-from! ;
: lft-w-arrow ( -- ) lft-in-proof lfa-e-tac-header lfa-fail ;

\ Locations (plan row TB2, tactic batch 3a, written at[ ... ] since
\ batch 3b; Lean's location, " at" (locationWildcard <|> locationHyp),
\ Elab/Tactic/Location.lean:32-40's expandLocation): at[ amends the step
\ read just before it, which must be a tactic of the open block whose
\ shape takes a location and that has none yet (else 453), with no value
\ left (86). Its list up to ] (lft-list-name, over lines; else 458): *
\ alone (Lean's wildcard), or hypothesis names in order with |- or ⊢
\ among them for the goal (Lean's locationType), one at least (else 454,
\ as for _, a LeanForth word, a token after * or * after another). The
\ names, name IDs at their places, follow the step's arguments (tac-loc#
\ of them), its flags are tac-loc's, and its text ends past the ].
1 constant tac-loc-given     \ at[ was written
2 constant tac-loc-goal      \ |- or ⊢ among its names
4 constant tac-loc-all       \ at[ * ]
453 outcome-invalid s" at[ follows no tactic word that takes a location"
  lfa-code: lfa-e-tac-at
454 outcome-invalid s" at[ takes hypothesis names and |-, or * alone, up to ]"
  lfa-code: lfa-e-tac-at-names
: lft-at-shape? ( shape|0 -- flag ) dup if shape-at @ then ;
: lft-own? ( addr -- flag ) tac-parent @ lft-open = ;
: lft-locatable? ( addr -- flag )
  dup lft-own? over tac-loc @ 0= and swap tac-shape @ lft-at-shape? and ;
: lft-located ( -- i )
  lf-tactic-count 1- dup lft-rec lft-locatable? lfa-e-tac-at lfa-must ;
\ Step i's flags; nothing may follow a *.
: lft-loc@ ( i -- flags ) lft-rec tac-loc @ ;
: lft-loc-open ( i -- i ) dup lft-loc@ tac-loc-all and 0= lfa-e-tac-at-names lfa-must ;
: lft-loc! ( i flag -- i ) swap lft-loc-open swap over lft-rec tac-loc tuck @ or swap ! ;
: lft-turnstile? ( c-addr u -- flag )
  2dup s" |-" lfa-token= if 2drop true else s" ⊢" lfa-token= then ;
: lft-loc-hyp ( i c-addr u -- i )
  2dup lft-loc-name? lfa-e-tac-at-names lfa-must lfn-name-id lfa-here lft-arg!
  lft-loc-open 1 over lft-rec tac-loc# +! ;
\ * only first: nothing named yet.
: lft-loc-fresh? ( i -- flag )
  dup lft-loc@ tac-loc-given = swap lft-rec tac-loc# @ 0= and ;
: lft-loc-star ( i -- i )
  dup lft-loc-fresh? lfa-e-tac-at-names lfa-must tac-loc-all lft-loc! ;
: lft-loc-token ( i c-addr u -- i )
  2dup lft-turnstile? if 2drop tac-loc-goal lft-loc! exit then
  2dup lft-star? if 2drop lft-loc-star exit then lft-loc-hyp ;
: lft-loc-names ( i -- i ) begin lft-list-name while lft-loc-token repeat ;
: lft-loc-some ( i -- i ) dup lft-loc-fresh? 0= lfa-e-tac-at-names lfa-must ;
: lft-w-at ( -- )
  lft-poised 0 lft-takes lft-located tac-loc-given lft-loc! lft-list-open
  lft-loc-names lft-loc-some lft-done ;

\ := by opens the proof; its end NAME needs every block closed and no
\ value left, and then the tactics run (lf-tactic-proof-end; without the
\ runner, error 80 names end, and by as the second place). A declaration
\ without by ends as the reader's does (reader.fs).
: lft-w-by ( -- ) lfn-w-by lfa-here lft-read-from! tac-k-by lft-new lft-opened ;
\ The block by-end would close: an alternative's is its by-induction-with.
: lft-block ( -- addr ) lft-alt? lft-open lft-rec swap if tac-parent @ lft-rec then ;
: lft-closed ( -- )
  lft-kind tac-k-by = if exit then lft-block tac-at @ lfa-e-tac-open lfa-fail-see ;
\ The proof read whole (its block closed) goes to the runner.
: lft-unrun ( -- ) 0 lft-rec tac-at @ lfa-e-tac-run lfa-fail-see ;
defer lf-tactic-proof-end ( -- )
' lft-unrun is lf-tactic-proof-end
\ The position just past end's NAME, which is the proof's end.
: lft-name-past ( c-addr u -- c-addr u pos ) 2dup + lfa-token-pos ;
: lft-all-closed ( -- ) lft-settled lft-closed ;
: lft-end-proof ( above c-addr u -- )
  lft-name-past >r lfa-end-check lft-all-closed lfa-proof-ready 0 lft-count r> lft-close
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
: lft-may-take? ( -- flag ) lfa-above 0> lfa-bracketed? 0= and ;
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
' lft-w-next lfa-natural! by-next
' lft-w-bar lfa-natural! |
' lft-w-arrow lfa-natural! =>
' lft-w-by-end lfa-natural! by-end
' lft-w-brace-end lfa-natural! }
' lft-w-rw lfa-natural! by-rw[
' lft-w-rewrite lfa-natural! by-rewrite[
' lft-w-bracket-end lfa-natural! ]
' lft-w-symm lfa-natural! <-
' lft-w-at lfa-natural! at[

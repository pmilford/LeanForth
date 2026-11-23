\ Case patterns, read (plan row TB2, piece E, slice E1; docs/design/
\ TACTIC_PATTERNS.md section 2; the owner's decision "Case patterns" of
\ 2026-11-22): Lean's rcasesPat (Init/RCases.lean) without commas and
\ without parentheses, the bracket shape of by-obtain[ and by-rcases[,
\ tac-shape-pattern ( -- shape ): one value before the word, then the
\ pattern up to ], over as many lines as it needs (batch 3c's list
\ reader: author/runner.fs's lfa-token-on, which skips ( ... ) as Forth
\ does, so ( a | b ) inside a pattern is a comment).
\     item     := NAME | _ | - | rfl | << { element } >> | ⟨ { element } ⟩
\     element  := item { | item }   (Lean's alternatives: a bar binds
\                                    tighter than a space)
\     by-obtain[ and by-rcases[ take exactly one element, then ].
\ A plain loop with no lookahead: an item ends the open element unless a
\ bar since the last item set the join flag (then it joins the element
\ and clears the flag); a bar with no element open or the flag set is 472
\ (also before a closer); << and ⟨ open a tuple, >> and ⟩ close their
\ own (the other closer, or ] with a tuple open: 473); ] ends the top
\ level, which holds one element (else 474: Lean's rcases h with a b is
\ a parse error). Inside the bracket a bar is the pattern's, also at a
\ line's start: the reader takes its tokens itself, so no bar reaches
\ the runner's alternatives (TACTIC_BLOCKS.md's rule). A name is a
\ hypothesis until the block ends, as by-intro:'s; rfl is read and
\ answered unsupported when it runs (slice E2); a token beginning @ is
\ 72 (Lean's @pat, slice E5); a LeanForth word that is no item, end NAME
\ or the text's end leaves the list unclosed: 458 at its word, as every
\ list (author/scopes.fs).
\ The step's arguments: the value, then the items in postfix order
\ (children first, a node after them), each with its span
\ (tactic-syntax.fs's targ-span: the arguments its node covers, itself
\ included): a name's ID, 0 for _, pat-clear for -, pat-rfl, and the
\ nodes pat-tuple (a bracket) and pat-alts (an element of two items or
\ more); a walker steps back over its children's spans (rcases.fs).
\ Words: tac-shape-pattern, pat-clear pat-rfl pat-tuple pat-alts ( -- x ).
\ It uses tactic-syntax.fs's reader words (lft-values, lft-list-open,
\ lft-given, lft-arg+, lft-done, targ#, lft-at-sign?).
\ Untrusted: a pattern says what was written; only the kernel's check of
\ the finished term decides.
\ State: pat-frames (the open brackets of the pattern being read, one
\ record each, cleared as a pattern begins), in the checker context (ADR
\ 0009).

require ../lib/lib.fs
require ../lib/slab.fs
require ../lib/context.fs
require ../author/errors.fs
require ../author/runner.fs
require ../author/scopes.fs
require ./tactic-syntax.fs

-1 constant pat-clear   -2 constant pat-rfl   -3 constant pat-tuple   -4 constant pat-alts
472 outcome-invalid s" a pattern's bar | goes between two items" lfa-code: lfa-e-pat-bar
473 outcome-invalid s" this closer does not close the pattern's open bracket"
  lfa-code: lfa-e-pat-closer
474 outcome-invalid s" by-obtain[ and by-rcases[ take one pattern" lfa-code: lfa-e-pat-one

\ ---- The open brackets: the top level's (closer 3, ]) and each tuple's
\ (1 for <<, 2 for ⟨).
begin-structure /pfr
  field: pfr-closer      \ the closer it waits for: 1 >>, 2 ⟩, 3 ]
  field: pfr-from        \ the argument its contents begin at
  field: pfr-elem        \ the open element's first argument, else -1
  field: pfr-items       \ the open element's items
  field: pfr-join        \ true: a bar since the last item
  field: pfr-elems       \ the elements it holds
end-structure
/pfr context-slab: pat-frames
: pfr ( -- frame ) pat-frames slab-last ;
: pfr-open ( closer -- )
  pat-frames slab-claim-one ok? lfa-e-tac-full lfa-must dup /pfr erase
  tuck pfr-closer ! targ# over pfr-from ! -1 swap pfr-elem ! ;

\ ---- Arguments: a leaf, and a node over the arguments from from on.
: pat-span! ( n -- ) targ# 1- tac-args store-slot targ-span ! ;
: pat-leaf ( i x -- i ) lfa-here lft-arg+ 1 pat-span! ;
: pat-node ( i kind from -- i ) targ# swap - 1+ >r lfa-here lft-arg+ r> pat-span! ;

\ ---- Elements: an item joins the open one after a bar, else ends it
\ (an alts node over two items or more) and opens the next.
: pfr-end ( i -- i )
  pfr pfr-elem @ 0< if exit then
  pfr pfr-items @ 1 > if pat-alts pfr pfr-elem @ pat-node then
  -1 pfr pfr-elem ! 1 pfr pfr-elems +! ;
: pfr-begin ( -- ) targ# pfr pfr-elem ! 1 pfr pfr-items ! ;
: pfr-item ( i -- i )
  pfr pfr-join @ if false pfr pfr-join ! 1 pfr pfr-items +! exit then pfr-end pfr-begin ;
: pat-item ( i x -- i ) swap pfr-item swap pat-leaf ;
: pfr-bar ( -- )
  pfr pfr-elem @ 0< pfr pfr-join @ or if lfa-e-pat-bar lfa-fail then true pfr pfr-join ! ;
\ A closer: its own bracket's, no bar before it; the open element ends.
: pfr-close ( i closer -- i )
  pfr pfr-closer @ <> if lfa-e-pat-closer lfa-fail then
  pfr pfr-join @ if lfa-e-pat-bar lfa-fail then pfr-end ;
: pfr-tuple ( i closer -- i ) pfr-close pat-tuple pfr pfr-from @ pat-node
  pat-frames slab-drop ;
: pfr-top ( i -- i )
  3 pfr-close pfr pfr-elems @ 1 <> if lfa-e-pat-one lfa-fail then
  pat-frames slab-drop lfa-bracket-drop ;

\ ---- The items and closers: a word list searched by spelling (each
\ word ( i -- i more? )); any other token is a name.
wordlist constant pat-words
[defined] warnings [if] warnings @ warnings off [then]   \ _ and - spelt as words
get-current pat-words set-current
: | ( i -- i more? ) pfr-bar true ;
: << ( i -- i more? ) pfr-item 1 pfr-open true ;
: ⟨ ( i -- i more? ) pfr-item 2 pfr-open true ;
: >> ( i -- i more? ) 1 pfr-tuple true ;
: ⟩ ( i -- i more? ) 2 pfr-tuple true ;
: ] ( i -- i more? ) pfr-top false ;
: _ ( i -- i more? ) 0 pat-item true ;
: - ( i -- i more? ) pat-clear pat-item true ;
: rfl ( i -- i more? ) pat-rfl pat-item true ;
set-current
[defined] warnings [if] warnings ! [then]
\ A name: no LeanForth word (else the list is unclosed, 458), no @ (72).
: pat-word ( c-addr u -- c-addr u )
  dup 0= if lfa-list-unclosed then 2dup lft-at-sign? if lfa-e-tactic lfa-fail then
  2dup lf-pf-reserved? if lfa-list-unclosed then ;
: pat-name ( i c-addr u -- i true ) pat-word rot pfr-item -rot lft-given 1 pat-span!
  true ;
: pat-step ( i c-addr u -- i more? )
  2dup pat-words search-wordlist if nip nip execute else pat-name then ;
: lft-build-pattern ( v i shape -- )
  lft-values drop lft-list-open pat-frames slab-clear 3 pfr-open
  begin lfa-token-on pat-step 0= until lft-done ;
1 0 ' lft-build-pattern tac-shape-new constant tac-shape-pattern

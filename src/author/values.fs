\ LeanForth values on the Forth data stack (ADR 0017 §6): a term, a universe
\ level, a name (a variable and/or a universe parameter) or a constant
\ waiting for its universe arguments is one cell, a negative reference to
\ an item kept here. The runner reads only plain decimal numbers, which
\ are nonnegative, and Lean has no negative literals or levels, so a word
\ that takes a level or a term tells a number from a value by its sign: a
\ number is a level before ^, Type and Sort (and a natural-number literal
\ before $, not supported yet). Each value is used once: the word that
\ takes it marks its item used, and a cell that is not a live, unused
\ item stops the run. So a copy of a value, however it was made, can
\ never stand for a term a second time or after its binder has closed.
\ Items live for one declaration: a declaration starts with an empty stack
\ and clears them. A variable becomes its de Bruijn index when it is
\ used, and only while its binder is open; a constant becomes a term when
\ it is used, with exactly as many universe arguments as it has universe
\ parameters. Untrusted authoring code.
\ State: the store lfa-items, in the checker context (ADR 0009).

require ../lib/lib.fs
require ./build.fs
require ./constants.fs
require ./scopes.fs

512 constant lfa-item-capacity
1 constant lfa-kind-term
2 constant lfa-kind-level
3 constant lfa-kind-name
4 constant lfa-kind-const

begin-structure /lfa-item
  field: lfa-item-kind
  field: lfa-item-first    \ term node; level; variable slot or -1; declaration
  field: lfa-item-second   \ term: true when the node is new; name: universe
                           \ level or -1; constant: the value it adds a level
                           \ to, or 0 for the constant as written
  field: lfa-item-third    \ constant: the universe level it adds, or -1
  field: lfa-item-at       \ position of the word that made it
  field: lfa-item-taken    \ true once a word has used the value
end-structure
lfa-item-capacity /lfa-item 0 context-store: lfa-items

: lfa-items-reset ( -- ) lfa-items store-clear ;
\ A new item made at the current token; too many stop the run.
: lfa-item-new ( kind first second -- value )
  lfa-items store-new-slot lfa-e-values-full lfa-must >r
  tuck lfa-item-second ! tuck lfa-item-first ! tuck lfa-item-kind !
  -1 over lfa-item-third ! 0 over lfa-item-taken ! lfa-here swap lfa-item-at !
  r> 1+ negate ;
\ The item of a value an item holds (a constant's chain); unchecked, never
\ for a cell taken from the stack.
: lfa-slot ( value -- item ) negate 1- lfa-items store-slot ;
\ Take a value from the stack, once: a number, a stale value or a value
\ already used stops the run.
: lfa-live? ( value -- flag ) dup 0< if negate 1- lfa-items store-valid? else drop false then ;
: lfa-take ( value -- item )
  dup lfa-live? lfa-e-not-value lfa-must lfa-slot
  dup lfa-item-taken @ 0= lfa-e-not-value lfa-must true over lfa-item-taken ! ;

\ Making values.
: lfa-term-value ( term fresh -- value ) lfa-kind-term -rot lfa-item-new ;
: lfa-level-value ( level -- value ) lfa-kind-level swap 0 lfa-item-new ;
: lfa-name-value ( slot level -- value ) lfa-kind-name -rot lfa-item-new ;
: lfa-const-value ( decl -- value ) lfa-kind-const swap 0 lfa-item-new ;
\ c l ^: a new constant value with one more universe argument.
: lfa-more-levels ( value level -- value' )
  swap dup lfa-slot lfa-item-first @ swap lfa-kind-const -rot lfa-item-new
  tuck lfa-slot lfa-item-third ! ;

\ Constants as terms. Following the values a ^ added to gives the
\ universe arguments, last one first; their number must be the
\ constant's. Errors point at the ^ or $ that used it and at the constant.
: lfa-chain# ( item -- n ) 0 swap begin lfa-item-second @ ?dup while lfa-slot swap 1+ swap
  repeat ;
: lfa-base-item ( item -- item' ) begin dup lfa-item-second @ ?dup while nip lfa-slot
  repeat ;
: lfa-arity? ( item -- flag ) dup lfa-chain# swap lfa-item-first @ lfa-decl-universes = ;
: lfa-pair! ( level i -- )
  >r dup lf-level-identity drop swap lfa-sought-ref lfa-ref-pairs r> 2* cells + 2! ;
: lfa-levels! ( item n -- )
  begin 1- dup 0< 0= while
    over lfa-item-third @ over lfa-pair! swap lfa-item-second @ lfa-slot swap repeat
      2drop ;
: lfa-ref! ( item -- )
  dup lfa-item-first @ lfa-decl-name lfa-sought-ref lfa-ref-name !
  dup lfa-chain# dup lfa-sought-ref lfa-ref-count ! lfa-levels! ;
: lfa-const-at ( item -- pos ) lfa-base-item lfa-item-at @ ;
: lfa-const-term ( item -- term fresh )
  dup lfa-arity? 0= if lfa-const-at lfa-e-arity lfa-fail-see then
  dup lfa-ref! lfa-const-at lfa-sought-ref lfa-cref rot lfa-const ;

\ A value as a term, and whether that node is new. A variable's binder
\ must still be open.
: lfa-in-scope ( slot -- slot ) dup lfa-depth < lfa-e-not-value lfa-must ;
: lfa-var-term ( item -- term fresh )
  dup lfa-item-first @ dup 0< 0= lfa-e-universe-term lfa-must lfa-in-scope
  lfa-index swap lfa-item-at @ lfa-bvar ;
: lfa-item-term ( item -- term fresh )
  dup lfa-item-kind @ case
    lfa-kind-term of dup lfa-item-first @ swap lfa-item-second @ endof
    lfa-kind-name of lfa-var-term endof
    lfa-kind-const of lfa-const-term endof
    lfa-e-not-term lfa-fail endcase ;
: lfa>term+ ( value -- term fresh ) dup 0< lfa-e-literal lfa-must lfa-take lfa-item-term ;
: lfa>term ( value -- term ) lfa>term+ drop ;

\ A value as a universe level: a number n is the level n.
: lfa-universe ( item -- level ) lfa-item-second @ dup 0< 0= lfa-e-not-universe lfa-must ;
: lfa-item-level ( item -- level )
  dup lfa-item-kind @ case
    lfa-kind-level of lfa-item-first @ endof
    lfa-kind-name of lfa-universe endof
    lfa-e-not-level lfa-fail endcase ;
: lfa>level ( value -- level )
  dup 0< if lfa-take lfa-item-level else lfa-level-number then ;
\ A count: a number, never a value.
: lfa>count ( value -- n ) dup 0< 0= lfa-e-count lfa-must ;
\ The constant a value names before any ^: its declaration and position.
: lfa>constant ( value -- item )
  dup 0< lfa-e-not-constant lfa-must
  lfa-take dup lfa-item-kind @ lfa-kind-const = lfa-e-not-constant lfa-must ;

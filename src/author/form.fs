\ The two forms of LeanForth text (ADR 0021 D8; plan task FE1a): natural
\ LeanForth, the default, whose words build a syntax tree that the front
\ end elaborates later (src/front/), and the kernel form of ADR 0017, whose
\ words build kernel terms at once. The word kernel-form, outside every
\ declaration, switches a run to the kernel form for the rest of the run
\ (the printer writes it first, cli/print-lf.fs); lf-author-begin starts
\ every run in natural form. Each syntax word has a meaning in each form
\ (groups.fs); a name word, in natural form, takes its explicit arguments
\ (lfa-name-natural, which src/front/reader.fs sets; until a front end is
\ loaded a name in natural text is not supported yet).
\
\ Numerals in natural text. Forth's interpreter turns a plain decimal into
\ a number on the data stack before the next word runs, so its position is
\ lost there. The words check those tokens before they act (groups.fs,
\ lfa-read-to); in natural form each one's position is pushed here, in
\ order, on a stack parallel to the numbers on the data stack: proof text
\ sees no Forth word, so numbers only come and go at the top, and the
\ natural word that takes a number as a numeral pops its position
\ (lfa-numeral-at). A number taken any other way is an error that ends
\ the run, and a run starts with the stack empty.
\
\ The pending ' : ' NAME pushes the function NAME without applying it
\ (src/front/reader.fs). ' checks that a name follows on its line and
\ marks it pending; the name word that runs next takes no arguments, and
\ any syntax word that runs instead stops the run (error 59). Untrusted
\ authoring code.
\ lfa-front-made? says whether a declaration of the run came through the
\ front end's hand-over (src/front/handover.fs sets it).
\ State: one context record, lfa-form, and the store lfa-numerals, both
\ in the checker context (ADR 0009).

require ../lib/lib.fs
require ./errors.fs

512 constant lfa-numeral-capacity

begin-structure /lfa-form
  field: lfa-form-kernel      \ true: the kernel form
  field: lfa-form-tick        \ position of a pending ' , or -1
  field: lfa-form-front       \ true: a declaration came through the front end
end-structure
/lfa-form context-record: lfa-form
lfa-numeral-capacity 1 cells 0 context-store: lfa-numerals

: lfa-kernel-form? ( -- flag ) lfa-form lfa-form-kernel @ ;
: lfa-kernel-form! ( -- ) true lfa-form lfa-form-kernel ! ;
\ A declaration of the run was handed over by the front end
\ (src/front/handover.fs), so its records are written reached-only
\ (cli/check-lf.fs; review fe1f L3).
: lfa-front-made? ( -- flag ) lfa-form lfa-form-front @ ;
: lfa-front-made! ( -- ) true lfa-form lfa-form-front ! ;
: lfa-form-reset ( -- )
  false lfa-form lfa-form-kernel ! -1 lfa-form lfa-form-tick ! lfa-numerals store-clear
  false lfa-form lfa-form-front ! ;
' lfa-form-reset context-setup

\ Numerals: the positions of the numbers on the data stack, newest last.
: lfa-numeral-push ( pos -- )
  lfa-numerals store-new-slot lfa-e-values-full lfa-must drop ! ;
: lfa-numeral-at ( -- pos )
  lfa-numerals store-count @ dup 0> lfa-e-not-value lfa-must
  1- lfa-numerals store-slot @ lfa-numerals store-drop ;
\ The tokens c-addr u of the line, every one a plain decimal: in natural
\ form, their positions, in order.
: lfa-token-pos ( c-addr -- pos ) lfa-offset 1+ lfa-line swap lfa-pos ;
: lfa-numerals-read ( c-addr u -- )
  lfa-kernel-form? if 2drop exit then
  begin lfa-next-token dup while drop lfa-token-pos lfa-numeral-push repeat 2drop 2drop ;

\ The pending ' .
: lfa-tick ( -- pos ) lfa-form lfa-form-tick @ ;
: lfa-tick! ( pos -- ) lfa-form lfa-form-tick ! ;
: lfa-ticked? ( -- flag ) lfa-tick 0< 0= ;
\ The name word after ' takes it; any other word stops the run.
: lfa-untick ( -- flag ) lfa-ticked? -1 lfa-tick! ;
: lfa-tick-free ( -- ) lfa-ticked? if lfa-tick lfa-e-tick lfa-fail-see then ;

\ A declaration or a run starts: the front end forgets the trees of the
\ last one (src/front/reader.fs sets it).
defer lfa-declaration-fresh ( -- )
:noname ( -- ) ; is lfa-declaration-fresh

\ A name word's value in natural form (src/front/reader.fs sets it).
: lfa-no-natural ( value -- value' ) drop lfa-e-natural-later lfa-fail ;
defer lfa-name-natural ( value -- value' )
' lfa-no-natural is lfa-name-natural
: lfa-named-natural ( value -- value' ) lfa-kernel-form? 0= if lfa-name-natural then ;

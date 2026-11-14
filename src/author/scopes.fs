\ Binder scopes and stack frames for the authoring words (ADR 0017 §7): the
\ binders open now, innermost last, and the declaration they belong to. A
\ binder word opens a scope and fun or forall closes it; like Forth's
\ control-flow stack, each scope is a frame of the data stack: the depth
\ when the binder took its domain. Inside a scope no word may take a value
\ from below that depth, and when it closes exactly one value must be
\ above it. Outside every binder the declaration's own depth is the frame.
\ A variable is the binder's position (its slot); its de Bruijn index is
\ counted when it is used. Untrusted authoring code.
\ State: the binder store lfa-binders and one record, lfa-scope, both in
\ the checker context (ADR 0009). The binder store is a heap store that
\ grows as binders open, limited only by the heap (plan task 6.2.0); a
\ binder's address is valid until the next one opens.

require ../lib/lib.fs
require ../core/terms.fs
require ./errors.fs
require ./form.fs

begin-structure /lfa-binder
  field: lfa-binder-name      \ name ID
  field: lfa-binder-kind      \ binder kind (present/binder-table.fs)
  field: lfa-binder-domain    \ the domain term
  field: lfa-binder-mark      \ data-stack depth once the domain was taken
  field: lfa-binder-at        \ position of the binder word
  field: lfa-binder-entries   \ names defined before this binder's (groups.fs)
end-structure
store-header context-record: lfa-binders
\ The first room, and the largest limit a store of binders takes.
16 constant lfa-binder-room
max-n store-header - /lfa-binder cell+ / constant lfa-binder-limit
: lfa-binders-make ( -- )
  lfa-binder-room /lfa-binder 0 lfa-binders store-heap-init ok? 0= abort" author: no heap"
  lfa-binder-limit lfa-binders store-limit! ok? 0= abort" author: binder limit" ;
' lfa-binders-make context-setup
:noname ( -- ) lfa-binders store-heap-free ; context-teardown

begin-structure /lfa-scope
  field: lfa-scope-base       \ data-stack depth where the declaration began; -1 outside
  field: lfa-scope-params     \ binders that are its parameters; -1 before :=
  field: lfa-scope-floor      \ data-stack depth where the run began
end-structure
/lfa-scope context-record: lfa-scope

\ Outside every declaration and binder.
: lfa-scope-close ( -- ) lfa-binders store-clear -1 lfa-scope lfa-scope-base !
  -1 lfa-scope lfa-scope-params ! ;
' lfa-scope-close context-setup
\ The depth of the data stack below the author's values.
: lfa-floor ( -- depth ) lfa-scope lfa-scope-floor @ ;
: lfa-floor! ( depth -- ) lfa-scope lfa-scope-floor ! ;

\ Binders.
: lfa-depth ( -- n ) lfa-binders store-count @ ;
: lfa-binder ( slot -- binder ) lfa-binders store-slot ;
: lfa-innermost ( -- binder ) lfa-depth 1- lfa-binder ;
: lfa-index ( slot -- i ) lfa-depth 1- swap - ;
\ A new binder record, zeroed; a store the heap cannot grow stops the run.
: lfa-binder-push ( -- binder )
  lfa-binders store-ready drop
  lfa-binders store-new-slot lfa-e-binders-full lfa-must drop dup /lfa-binder erase ;
: lfa-binder-pop ( -- ) -1 lfa-binders store-count +! ;

\ The declaration.
: lfa-base ( -- depth ) lfa-scope lfa-scope-base @ ;
: lfa-inside? ( -- flag ) lfa-base 0< 0= ;
: lfa-params ( -- n ) lfa-scope lfa-scope-params @ ;
: lfa-params! ( n -- ) lfa-scope lfa-scope-params ! ;
\ Binders opened after :=, which fun or forall may close; before := every
\ open binder may be closed.
: lfa-closable ( -- n ) lfa-depth lfa-params 0 max - ;

\ The frame: the innermost binder's depth, else the declaration's, else
\ (natural text between declarations, where a command such as #check
\ takes a term: plan S1) the run's floor.
: lfa-outer ( -- depth ) lfa-base dup 0< if drop lfa-floor then ;
: lfa-frame ( -- depth )
  lfa-depth if lfa-innermost lfa-binder-mark @ else lfa-outer then ;
\ Terms stand inside a declaration, or in natural text anywhere.
: lfa-terms? ( -- flag ) lfa-inside? lfa-kernel-form? 0= or ;
\ Stop unless n values are above the frame, where terms may stand. Called
\ first thing by a word that takes n values, with nothing else pushed.
: lfa-args ( n -- )
  lfa-terms? lfa-e-outside lfa-must depth 1- over - lfa-frame < 0= lfa-e-missing lfa-must
  drop ;
\ Stop unless exactly n values are above the frame.
: lfa-exactly ( n code -- ) >r depth 1- lfa-frame - = r> lfa-must ;

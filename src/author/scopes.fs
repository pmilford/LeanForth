\ Binder scopes and stack frames for the authoring words (ADR 0017 §7): the
\ binders open now, innermost last, and the declaration they belong to. A
\ binder word opens a scope and fun or forall closes it; like Forth's
\ control-flow stack, each scope is a frame of the data stack: the depth
\ when the binder took its domain. Inside a scope no word may take a value
\ from below that depth, and when it closes exactly one value must be
\ above it. Outside every binder the declaration's own depth is the frame.
\ A variable is the binder's position (its slot); its de Bruijn index is
\ counted when it is used. Untrusted authoring code.
\ Brackets (plan row TB2, batch 3c): a list between its word and its
\ closing word (<< >>, by-rw[ ], a list of names), each open one a frame
\ as a binder's is, the innermost frame of the two: its words take only
\ its items, the values after its word. Each keeps the binders open when
\ it opened (they must be the same when it closes), its word's place and
\ spelling, and its closer, an address its closing words give. Words:
\ lfa-bracket-open ( closer -- ) opens one at the current token;
\ lfa-bracket-close ( closer code -- n pos ) closes the innermost one,
\ which must be closer's (else 458 at its word), with the same binders
\ open (else 21), n its items and pos its word's place; none open is
\ error code at the current token;
\ lfa-bracket-drop ( -- ) closes it, its items not counted (a list of
\ names, read whole); lfa-bracketed? ( -- flag ) whether one is open;
\ lfa-list-closer ( -- closer|0 ) the innermost one's; lfa-list-unclosed
\ ( -- ) error 458 at the innermost one's word: its closing word never
\ came (a word that never is an item, end NAME, :=, the text's end);
\ lfa-brackets-closed ( -- ) that error when one is open.
\ State: the binder store lfa-binders, the slab lfa-brackets and one
\ record, lfa-scope, all in
\ the checker context (ADR 0009). The binder store is a heap store that
\ grows as binders open, limited only by the heap (plan task 6.2.0); a
\ binder's address is valid until the next one opens.

require ../lib/lib.fs
require ../lib/bounds.fs
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
/lfa-binder store-most constant lfa-binder-limit
: lfa-binders-make ( -- )
  lfa-store-room /lfa-binder 0 lfa-binders store-heap-init lfa-heap-must
  lfa-binder-limit lfa-binders store-limit! lfa-heap-must ;
' lfa-binders-make context-setup
:noname ( -- ) lfa-binders store-heap-free ; context-teardown

begin-structure /lfa-scope
  field: lfa-scope-base       \ data-stack depth where the declaration began; -1 outside
  field: lfa-scope-params     \ binders that are its parameters; -1 before :=
  field: lfa-scope-floor      \ data-stack depth where the run began
end-structure
/lfa-scope context-record: lfa-scope
begin-structure /lfa-bracket
  field: lfa-bracket-mark     \ data-stack depth when it opened
  field: lfa-bracket-binders  \ binders open then
  field: lfa-bracket-at       \ position of its word
  field: lfa-bracket-closer   \ its closing words' address
  cell lfa-token-keep chars + +field lfa-bracket-word   \ its spelling, cell-counted
end-structure
/lfa-bracket context-slab: lfa-brackets

\ Outside every declaration, binder and bracket.
: lfa-scope-close ( -- ) lfa-binders store-clear -1 lfa-scope lfa-scope-base !
  -1 lfa-scope lfa-scope-params ! lfa-brackets slab-clear ;
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
: lfa-binder-frame ( -- depth )
  lfa-depth if lfa-innermost lfa-binder-mark @ else lfa-outer then ;

\ Brackets (see the header).
458 outcome-invalid s" this list is never closed: its ] or >> is missing"
  lfa-code: lfa-e-list-open
: lfa-bracketed? ( -- flag ) lfa-brackets slab-count 0<> ;
: lfa-bracket ( -- addr ) lfa-brackets slab-last ;
: lfa-list-closer ( -- closer|0 )
  lfa-bracketed? if lfa-bracket lfa-bracket-closer @ else 0 then ;
\ (No room for one is full, as for a binder: 65.)
: lfa-bracket-new ( -- addr ) lfa-brackets slab-claim-one ok? lfa-e-binders-full lfa-must ;
: lfa-bracket-word! ( addr -- )
  lfa-token lfa-token-keep min rot lfa-bracket-word lfa-token-keep cell-counted! drop ;
: lfa-bracket-place ( addr -- addr )
  lfa-depth over lfa-bracket-binders ! lfa-here over lfa-bracket-at ! dup lfa-bracket-word! ;
: lfa-bracket-fill ( mark closer addr -- )
  tuck lfa-bracket-closer ! tuck lfa-bracket-mark ! lfa-bracket-place drop ;
: lfa-bracket-open ( closer -- ) depth 1- swap lfa-bracket-new lfa-bracket-fill ;
: lfa-bracket-drop ( -- ) lfa-brackets slab-drop ;
: lfa-list-unclosed ( -- )
  lfa-bracket dup lfa-bracket-word cell-count rot lfa-bracket-at @ lfa-e-list-open lfa-fail-at ;
: lfa-brackets-closed ( -- ) lfa-bracketed? if lfa-list-unclosed then ;
: lfa-bracket-own ( closer code -- )
  lfa-bracketed? 0= if nip lfa-fail then drop lfa-list-closer <> if lfa-list-unclosed then ;
: lfa-bracket-binders? ( -- )
  lfa-depth lfa-bracket lfa-bracket-binders @ = if exit then
  lfa-innermost lfa-binder-at @ lfa-e-open-binder lfa-fail-see ;
: lfa-bracket-items ( -- n pos )
  depth lfa-bracket lfa-bracket-mark @ - lfa-bracket lfa-bracket-at @ ;
: lfa-bracket-close ( closer code -- n pos )
  lfa-bracket-own lfa-bracket-binders? lfa-bracket-items lfa-bracket-drop ;

\ The frame: the innermost bracket's, binder's or declaration's.
: lfa-frame ( -- depth )
  lfa-binder-frame lfa-bracketed? if lfa-bracket lfa-bracket-mark @ max then ;
\ Terms stand inside a declaration, or in natural text anywhere.
: lfa-terms? ( -- flag ) lfa-inside? lfa-kernel-form? 0= or ;
\ Stop unless n values are above the frame, where terms may stand. Called
\ first thing by a word that takes n values, with nothing else pushed.
: lfa-args ( n -- )
  lfa-terms? lfa-e-outside lfa-must depth 1- over - lfa-frame < 0= lfa-e-missing lfa-must
  drop ;
\ Stop unless exactly n values are above the frame.
: lfa-exactly ( n code -- ) >r depth 1- lfa-frame - = r> lfa-must ;

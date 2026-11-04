\ Feeding a staged export to the checker (plan task 3.2.2; ADR 0016 C9
\ step 3): the declarations of a sealed stage (import/stage.fs) become the
\ current context's input (core/input.fs), in file order, ready for
\ check-declaration (lf-check-input, kernel/check-declaration.fs).
\ Untrusted [import] code, fail-closed; it decides nothing about types.
\
\ The stage's names stay in its input tier, shared and read-only: the
\ context attaches that tier as its names (lf-name-attach,
\ core/names.fs), so a name's ID is its number in the stage, equal names
\ are one ID, and the environment finds the declarations of a name through
\ the input's name index instead of scanning (ADR 0012 E5, ADR 0016 C4).
\ Levels, expressions and declarations are copied into the context's
\ stores, whose capacities lf-feed raises to fit the stage plus room for
\ the checks' scratch: the checker reads terms through handles and
\ identities, which the input tier does not have (ADR 0016 C9 step 3
\ keeps them until the environment's handles replace them). Copied as
\ ndjson-input.fs (tests/support) stages a file: a Sort as a symbolic
\ Sort, a constant through its reference, a let, projection, literal or
\ mdata expression as the leaf of its form (core/unsupported-forms.fs,
\ refused by the audit, U2); binder names and binder information are not
\ copied, as Lean's kernel ignores them. An inductive block, a record
\ with no name, gives no declaration but a header in the input's
\ inductive data (core/input.fs); its types, constructors and recursors
\ are declarations that point at the header and carry their exported
\ numbers, lists, flags and rules there (plan task 5.2.1a; the checker of
\ blocks, kernel/check-block.fs, decides them together). Every universe
\ parameter a level names joins the session's level context first.
\
\ lf-feed ( stage feed -- outcome ): ok; invalid for a stage that is not
\ sealed, a record the stores refuse as malformed or a failed loading
\ end; full for a store, the level context, a universe list longer than
\ the checker takes, or no heap; feed-at then gives the expression or
\ declaration number where it stopped. The input is left partly filled
\ after a failure: lf-input-reset (or another feed) starts over.
\ feed-free frees the loading aids (lf-feed frees them itself).
\
\ State: none of its own; every word takes a feed record (/feed), which
\ owns its heap blocks (the export-to-store maps) only during lf-feed.

require ../lib/bytes.fs
require ../core/compact.fs
require ../core/input.fs
require ../core/unsupported-forms.fs
require ../core/constant-term-boundary.fs
require ./stage.fs

\ Room for the checks' scratch above the input, in each store.
1048576 constant feed-term-room
65536 constant feed-level-room
262144 constant feed-cref-room

begin-structure /feed
  field: feed-stage        \ the sealed stage
  field: feed-levels       \ heap: per stage level, its store index
  field: feed-exprs        \ heap: per stage expression, its term handle (2 cells)
  field: feed-where        \ the expression or declaration where it stopped
  field: feed-header       \ the current block's header cell, plus one; 0 for none
  field: feed-members      \ members of the current block still to come
  lf-cref-argument-capacity 2* cells +field feed-pairs
  /lf-idecl +field feed-decl
end-structure

: feed-tier ( feed -- tier ) feed-stage @ stage-tier ;
: feed-at ( feed -- n ) feed-where @ ;
: feed-free ( feed -- )
  dup feed-levels heap-release dup feed-exprs heap-release drop ;

\ ---- Capacities: the stage's records plus room for the checks; a
\ setting is only ever raised.
: feed-numbers ( feed xt -- n ) swap feed-tier swap execute cons-numbers ;
: feed-set ( outcome n xt -- outcome )
  rot dup ok? if drop execute else nip nip then ;
: feed-capacities ( feed -- outcome )
  >r outcome-ok
  r@ ['] tier-exprs feed-numbers feed-term-room + lf-term-capacity max
  ['] lf-term-capacity! feed-set
  r@ ['] tier-levels feed-numbers feed-level-room + lf-level-capacity max
  ['] lf-level-capacity! feed-set
  r@ ['] tier-exprs feed-numbers feed-cref-room + lf-cref-capacity max
  ['] lf-cref-capacity! feed-set
  r> feed-stage @ stage-decls lf-input-capacity max ['] lf-input-capacity! feed-set ;

\ ---- Maps: heap blocks of cells, freed by feed-free.
: feed-block ( cells addr -- outcome )
  >r cells 1 max allocate if drop r> drop outcome-full exit then r> ! outcome-ok ;
: feed-maps ( feed -- outcome )
  dup ['] tier-levels feed-numbers over feed-levels feed-block dup ok? 0= if nip exit then
  drop dup ['] tier-exprs feed-numbers 2* swap feed-exprs feed-block ;
: feed-level! ( index l feed -- ) feed-levels @ swap cells + ! ;
: feed-level@ ( l feed -- index ) feed-levels @ swap cells + @ ;
: feed-handle ( l feed -- index identity )
  feed-level@ dup lf-level-identity 0= if 0 then ;
: feed-expr-at ( e feed -- addr ) feed-exprs @ swap 2* cells + ;
: feed-term@ ( e feed -- index identity ) feed-expr-at 2@ ;
: feed-root ( e feed -- index ) feed-term@ drop ;

\ ---- The level context: every parameter a level names.
: feed-param ( name -- outcome )
  dup lf-lscope-member? if drop outcome-ok exit then
  lf-lscope-context-add if outcome-ok else outcome-full then ;
: feed-level-param ( l tier -- outcome )
  2dup level-tag@ tag-level-param = if level-name@ feed-param else 2drop outcome-ok then ;
: feed-context ( feed -- outcome )
  dup feed-tier swap ['] tier-levels feed-numbers 0 ?do
    i over feed-level-param dup ok? 0= if nip unloop exit then drop
  loop drop outcome-ok ;

\ ---- Levels, in number order; number 0 is level zero, the store's 0.
: feed-made ( index true | false -- index outcome )
  if outcome-ok else -1 outcome-full then ;
: feed-a ( l feed -- index ) tuck feed-tier level-a@ swap feed-level@ ;
: feed-b ( l feed -- index ) tuck feed-tier level-b@ swap feed-level@ ;
: feed-two ( l feed -- left right ) 2dup feed-a -rot feed-b ;
: feed-level-made ( l feed -- index true | false )
  2dup feed-tier level-tag@ case
    tag-level-succ of feed-a lf-level-succ endof
    tag-level-max of feed-two lf-level-max endof
    tag-level-imax of feed-two lf-level-imax endof
    tag-level-param of feed-tier level-name@ lf-level-param endof
    >r 2drop false r> endcase ;
: feed-level ( l feed -- outcome )
  2dup feed-level-made feed-made dup ok? if drop -rot feed-level! outcome-ok
  else nip nip nip then ;
: feed-levels-all ( feed -- outcome )
  0 0 2 pick feed-level!
  dup ['] tier-levels feed-numbers 1 ?do
    i over feed-level dup ok? 0= if nip unloop exit then drop
  loop drop outcome-ok ;

\ ---- Expressions, in number order (a letE spans two records).
: feed-kept ( index identity true | false e feed -- outcome )
  rot 0= if 2drop outcome-full exit then feed-expr-at 2! outcome-ok ;
: feed-a-term ( e feed -- index identity ) tuck feed-tier expr-a@ swap feed-term@ ;
: feed-b-term ( e feed -- index identity ) tuck feed-tier expr-b@ swap feed-term@ ;
: feed-children ( e feed -- l lid r rid ) 2dup feed-a-term 2swap feed-b-term ;
\ A constant's universe arguments, as level handles in the feed's pairs.
\ Pairs hold the index first, then the identity (lf-cref-pair@).
: feed-pair! ( l k feed -- )
  >r swap r@ feed-handle swap rot r> feed-pairs swap lf-cref-pair 2! ;
: feed-args ( t feed -- n outcome )
  dup feed-tier tier-tuples rot swap 2dup tuple-length
  dup lf-cref-argument-capacity > if >r 2drop drop r> outcome-full exit then
  dup >r 0 ?do i 2 pick 2 pick tuple-item i 4 pick feed-pair! loop
  2drop drop r> outcome-ok ;
: feed-const ( e feed -- index identity true | false )
  2dup feed-tier expr-b@ over feed-args ok? 0= if drop 2drop false exit then
  >r tuck feed-tier expr-a@ lf-name-generation @ rot feed-pairs r> lf-cref-new
  if lf-cterm-new else false then ;
\ The unsupported form of each expression tag, 0 for a supported one
\ (core/unsupported-forms.fs); a table filled while loading.
tag-mdata 1+ constant feed-tags#
create feed-forms feed-tags# cells allot  feed-forms feed-tags# cells erase
: feed-form! ( form tag -- ) cells feed-forms + ! ;
lf-form-let tag-let feed-form!  lf-form-let tag-let-nondep feed-form!
lf-form-proj tag-proj feed-form!  lf-form-nat tag-nat feed-form!
lf-form-string tag-str feed-form!  lf-form-mdata tag-mdata feed-form!
: feed-form@ ( tag -- form )
  dup 0 feed-tags# within if cells feed-forms + @ else drop 0 then ;
: feed-binder ( e feed tag -- index identity true | false )
  >r feed-children r> tag-pi < if lf-hterm-lam else lf-hterm-pi then ;
: feed-sort ( e feed -- index identity true | false )
  tuck feed-tier expr-a@ swap feed-handle lf-hterm-sort ;
: feed-core ( e feed tag -- index identity true | false )
  case tag-bvar of feed-tier expr-a@ lf-hterm-bvar endof  tag-sort of feed-sort endof
    tag-const of feed-const endof  tag-app of feed-children lf-hterm-app endof
    >r 2drop false r> endcase ;
: feed-term-made ( e feed tag -- index identity true | false )
  dup binder-tag? if feed-binder exit then
  dup feed-form@ ?dup if nip nip nip lf-hterm-unsupported else feed-core then ;
: feed-expr ( e feed -- outcome )
  2dup >r >r 2dup feed-tier expr-tag@ feed-term-made r> r> feed-kept ;
: feed-span ( e feed -- units ) feed-tier expr-tag@ let-tag? if 2 else 1 then ;
: feed-exprs-all ( feed -- outcome )
  0 begin over ['] tier-exprs feed-numbers over > while
    dup 2 pick feed-where ! 2dup swap feed-expr dup ok? 0= if nip nip exit then drop
    2dup swap feed-span +
  repeat 2drop outcome-ok ;

\ ---- Declarations, in file order. Kinds as the reader codes them
\ (import/ndjson.fs), the checker's (core/input.fs) per kind, 0 for a
\ block.
create feed-kinds
  lf-kind-axiom , lf-kind-definition , lf-kind-theorem , lf-kind-opaque ,
  lf-kind-quotient , 0 , lf-kind-inductive , lf-kind-constructor , lf-kind-recursor ,
: feed-kind ( d stage -- kind ) staged-kind@ kind-axiom - cells feed-kinds + @ ;
: feed-decl! ( x field-xt feed -- ) feed-decl swap execute ! ;
\ A field of declaration d, read from the stage with xt ( d stage -- x ).
: feed-staged ( d feed xt -- d feed x ) >r 2dup feed-stage @ r> execute ;
\ A field holding the term of the stage's expression read with xt.
: feed-term! ( d feed xt field-xt -- d feed )
  >r feed-staged over feed-root r> 2 pick feed-decl! ;
: feed-blank ( feed -- )
  dup feed-decl /lf-idecl erase  lf-hint-opaque ['] lf-idecl-hint 2 pick feed-decl!
  -1 ['] lf-idecl-value rot feed-decl! ;
: feed-start ( d feed -- )
  dup feed-blank ['] feed-kind feed-staged ['] lf-idecl-kind 2 pick feed-decl!
  ['] staged-name@ feed-staged ['] lf-idecl-name 2 pick feed-decl!
  ['] staged-type@ ['] lf-idecl-type feed-term! 2drop ;
\ A definition's safety and hints; any other kind is safe unless marked
\ unsafe (a theorem has no such mark).
: feed-height ( d feed hints -- d feed )
  lf-hint-regular = if ['] staged-hint@ feed-staged ['] lf-idecl-height 2 pick feed-decl!
  then ;
: feed-def ( d feed -- )
  ['] staged-safety@ feed-staged ['] lf-idecl-safety 2 pick feed-decl!
  ['] staged-hints@ feed-staged dup ['] lf-idecl-hint 3 pick feed-decl!
  feed-height 2drop ;
: feed-safe ( unsafe? -- safety ) if lf-safety-unsafe else lf-safety-safe then ;
: feed-safety ( d feed -- )
  ['] staged-unsafe? feed-staged feed-safe ['] lf-idecl-safety rot feed-decl! drop ;
: feed-valued? ( kind -- flag )
  dup lf-kind-definition = over lf-kind-theorem = or swap lf-kind-opaque = or ;
: feed-value ( d feed -- ) ['] staged-value@ ['] lf-idecl-value feed-term! 2drop ;
: feed-kind@ ( feed -- kind ) feed-decl lf-idecl-kind @ ;
: feed-details ( d feed -- )
  dup feed-kind@ dup feed-valued? if >r 2dup feed-value r> then
  lf-kind-definition = if feed-def else feed-safety then ;
: feed-params ( d feed -- outcome )
  tuck feed-stage @ staged-params@ over feed-tier tier-tuples 2dup tuple-length
  dup lf-param-capacity > if 2drop 2drop outcome-full exit then
  dup 4 pick feed-decl lf-idecl-arity ! 0 ?do
    i 2 pick 2 pick tuple-item 3 pick feed-decl lf-idecl-params i cells + !
  loop 2drop drop outcome-ok ;
\ ---- Inductive blocks (plan task 5.2.1a; ADR 0015 B1): the block
\ record gives a header in the input's inductive data, [first types ctors
\ recursors] (core/input.fs), and the next types + ctors + recursors
\ declarations are its members, each pointing at the header and at its
\ own data cells. A block with no type, or with members missing, cannot
\ come from lean4export and is invalid, as is a member outside a block.
\ Item k of declaration d's data tuple; a cell appended to the data when
\ the outcome so far is ok.
: feed-item@ ( k d feed -- u ) feed-stage @ staged-item ;
: feed-nth ( d feed k -- d feed u ) >r 2dup r> -rot feed-item@ ;
: feed, ( outcome x -- outcome ) swap dup ok? if drop lf-more, else nip then ;
: feed-num, ( d feed outcome k -- d feed outcome ) 3 pick 3 pick feed-item@ feed, ;
\ A tuple as a list: its count, then its items.
: feed-list-item ( outcome t cons i -- outcome t cons )
  >r 2dup r> -rot tuple-item >r rot r> feed, -rot ;
: feed-list, ( outcome t cons -- outcome )
  2dup tuple-length >r rot r@ feed, -rot r> 0 ?do i feed-list-item loop 2drop ;
: feed-names, ( d feed outcome k -- d feed outcome )
  3 pick 3 pick feed-item@ 2 pick feed-tier tier-tuples feed-list, ;
\ A recursor's rules: their count, then constructor, nfields and right
\ side (the term the stage's expression became) of each.
: feed-rule-item ( outcome t feed j -- outcome t feed )
  >r 2dup feed-tier tier-tuples r@ -rot tuple-item
  r> 3 mod 2 = if over feed-root then >r rot r> feed, -rot ;
: feed-rules, ( outcome t feed -- outcome )
  2dup feed-tier tier-tuples tuple-length >r
  r@ 3 mod if r> drop 2drop drop outcome-invalid exit then
  rot r@ 3 / feed, -rot r> 0 ?do i feed-rule-item loop 2drop ;
: feed-flags ( d feed -- flags )
  2dup feed-stage @ staged-rec? lf-ity-rec-bit and >r
  feed-stage @ staged-reflexive? lf-ity-reflexive-bit and r> or ;
: feed-type-data ( d feed -- d feed outcome )
  outcome-ok more-type-params feed-num, more-type-indices feed-num,
  more-type-nested feed-num, >r 2dup feed-flags r> swap feed,
  more-type-all feed-names, more-type-ctors feed-names, ;
: feed-ctor-data ( d feed -- d feed outcome )
  outcome-ok more-ctor-induct feed-num, more-ctor-cidx feed-num,
  more-ctor-params feed-num, more-ctor-fields feed-num, ;
: feed-rec-data ( d feed -- d feed outcome )
  outcome-ok more-rec-params feed-num, more-rec-indices feed-num,
  more-rec-motives feed-num, more-rec-minors feed-num,
  >r 2dup feed-stage @ staged-k? r> swap feed, more-rec-all feed-names,
  more-rec-rules 3 pick 3 pick feed-item@ 2 pick feed-rules, ;
: feed-kind-data ( d feed kind -- d feed outcome )
  case kind-type of feed-type-data endof  kind-ctor of feed-ctor-data endof
    kind-recursor of feed-rec-data endof outcome-invalid swap endcase ;
: feed-data ( d feed -- outcome )
  lf-more-here 1+ over feed-decl lf-idecl-more !
  2dup feed-stage @ staged-kind@ feed-kind-data nip nip ;
\ The block record: its header, and the number of members to come.
: feed-header! ( feed -- ) lf-more-here 1+ swap feed-header ! ;
: feed-total ( d feed -- n ) 0 3 0 do i 3 pick 3 pick feed-item@ + loop nip nip ;
: feed-members! ( d feed outcome -- outcome )
  >r 2dup feed-total swap feed-members ! drop r> ;
: feed-block-ok? ( d feed -- flag )
  2dup feed-stage @ staged-items 3 = over feed-members @ 0= and
  if more-block-types feed-nth nip nip 0<> else 2drop false then ;
: feed-header-record ( d feed -- outcome )
  2dup feed-block-ok? 0= if 2drop outcome-invalid exit then
  dup feed-header! outcome-ok lf-input-count feed,
  more-block-types feed-num, more-block-ctors feed-num, more-block-recursors feed-num,
  feed-members! ;
\ A member of the current block, or any other declaration.
: feed-member? ( d feed -- flag )
  feed-stage @ staged-kind@ dup kind-type = over kind-ctor = or swap kind-recursor = or ;
: feed-member ( d feed -- outcome )
  dup feed-members @ 0= if 2drop outcome-invalid exit then
  -1 over feed-members +! dup feed-header @ over feed-decl lf-idecl-block ! feed-data ;
: feed-outside ( d feed -- outcome )
  nip feed-members @ if outcome-invalid else outcome-ok then ;
: feed-joined ( d feed -- outcome )
  2dup feed-member? if feed-member else feed-outside then ;
: feed-block? ( d feed -- flag ) feed-stage @ staged-kind@ kind-inductive = ;
: feed-one ( d feed -- outcome )
  2dup feed-block? if feed-header-record exit then
  2dup feed-start 2dup feed-details 2dup feed-joined dup ok? 0= if nip nip exit then drop
  tuck feed-params dup ok? 0= if nip exit then
  drop feed-decl lf-input-add nip ;
: feed-decls-all ( feed -- outcome )
  dup feed-stage @ stage-decls 0 ?do
    i over feed-where ! i over feed-one dup ok? 0= if nip unloop exit then drop
  loop drop outcome-ok ;

\ ---- The whole feed: the steps ( feed -- outcome ), in order.
: feed-fresh ( feed -- outcome )
  lf-input-reset lf-term-reset lf-level-reset lf-cref-reset lf-lscope-context-reset
  feed-tier lf-name-attach ;
: feed-session ( feed -- outcome ) drop lf-ssession-begin flag>outcome ;
: feed-end ( feed -- outcome ) feed-members @ if outcome-invalid else lf-input-end then ;
create feed-steps
  ' feed-fresh , ' feed-capacities , ' feed-maps , ' feed-context , ' feed-session ,
  ' feed-levels-all , ' feed-exprs-all , ' feed-decls-all , ' feed-end ,
here feed-steps - 1 cells / constant feed-steps#
: feed-step ( feed k -- outcome ) cells feed-steps + @ execute ;
: feed-run ( feed -- outcome )
  feed-steps# 0 do dup i feed-step dup ok? 0= if nip unloop exit then drop loop
  drop outcome-ok ;
\ Feed the sealed stage into this context's input (see the header).
: lf-feed ( stage feed -- outcome )
  dup /feed erase tuck feed-stage !
  dup feed-stage @ stage-sealed? 0= if drop outcome-invalid exit then
  dup feed-run swap feed-free ;

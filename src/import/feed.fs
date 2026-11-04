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
\ The context's scratch tier then points into the stage's input tier, so
\ the stage must outlive the view: free it only after lf-name-detach, or
\ after the context is freed.
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
\ sealed, a level or expression of a kind the checker's stores do not
\ hold (a free or meta variable), a declaration of a kind it does not
\ know, a block with no type or with members missing, a member outside a
\ block, or a failed loading end; full for a store that refuses a record
\ (its capacity, no heap), the level context, or a universe list longer
\ than the checker takes; feed-at then gives the expression or
\ declaration number where it stopped. The input is left partly filled
\ after a failure: lf-input-reset (or another feed) starts over.
\ feed-free frees the loading aids (lf-feed frees them itself).
\
\ State: none of its own; every word takes a feed record (/feed), which
\ owns its heap blocks (the export-to-store maps, zeroed, so that an
\ entry never set is no handle) only during lf-feed.

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
  field: feed-d            \ the declaration being fed
  field: feed-header       \ the current block's header cell, plus one; 0 for none
  field: feed-members      \ members of the current block still to come
  2 cells +field feed-pair-buf   \ heap: a constant's level pairs, and their room
  2 cells +field feed-param-buf  \ heap: a declaration's parameters, and their room
  /lf-idecl +field feed-decl
end-structure

: feed-tier ( feed -- tier ) feed-stage @ stage-tier ;
: feed-at ( feed -- n ) feed-where @ ;
: feed-free ( feed -- )
  dup feed-levels heap-release dup feed-exprs heap-release
  dup feed-pair-buf heap-release feed-param-buf heap-release ;
\ A heap buffer of the feed's (its address, then its room in units):
\ room for n units of u address units, grown, never shrunk, freed by
\ feed-free. There is no other limit (plan task 6.2.0); no heap is full.
: feed-grow ( n u buffer -- outcome )
  >r over r@ cell+ @ > 0= if 2drop r> drop outcome-ok exit then
  over * 1 max r@ @ ?dup if swap resize else allocate then
  if 2drop r> drop outcome-full exit then
  r@ ! r> cell+ ! outcome-ok ;
: feed-pairs ( feed -- addr ) feed-pair-buf @ ;

\ ---- Capacities: the stage's records plus room for the checks; a
\ setting is only ever raised. One row per setting: the stage's records
\ ( feed -- n ), the room added, and the setting's reader and writer.
: feed-numbers ( feed xt -- n ) swap feed-tier swap execute cons-numbers ;
: feed-exprs# ( feed -- n ) ['] tier-exprs feed-numbers ;
: feed-levels# ( feed -- n ) ['] tier-levels feed-numbers ;
: feed-decls# ( feed -- n ) feed-stage @ stage-decls ;
begin-structure /feed-setting
  field: setting-records   \ xt ( feed -- n )
  field: setting-room
  field: setting-get       \ xt ( -- n )
  field: setting-set       \ xt ( n -- outcome )
end-structure
create feed-settings
  ' feed-exprs# , feed-term-room , ' lf-term-capacity , ' lf-term-capacity! ,
  ' feed-levels# , feed-level-room , ' lf-level-capacity , ' lf-level-capacity! ,
  ' feed-exprs# , feed-cref-room , ' lf-cref-capacity , ' lf-cref-capacity! ,
  ' feed-decls# , 0 , ' lf-input-capacity , ' lf-input-capacity! ,
here feed-settings - /feed-setting / constant feed-settings#
\ Raise a setting to n, after an earlier ok; the first failure stays.
: feed-raise ( outcome n get-xt set-xt -- outcome )
  >r execute max r> rot dup ok? if drop execute else nip nip then ;
: feed-setting ( outcome feed row -- outcome )
  >r r@ setting-records @ execute r@ setting-room @ +
  r@ setting-get @ r> setting-set @ feed-raise ;
: feed-capacities ( feed -- outcome )
  outcome-ok feed-settings# 0 do
    over i /feed-setting * feed-settings + feed-setting
  loop nip ;

\ ---- Maps: heap blocks of cells, zeroed, freed by feed-free.
: feed-block ( cells addr -- outcome )
  >r cells 1 max dup allocate if 2drop r> drop outcome-full exit then
  tuck swap erase r> ! outcome-ok ;
: feed-maps ( feed -- outcome )
  dup feed-levels# over feed-levels feed-block dup ok? 0= if nip exit then
  drop dup feed-exprs# 2* swap feed-exprs feed-block ;
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
  dup feed-tier swap feed-levels# 0 ?do
    i over feed-level-param dup ok? 0= if nip unloop exit then drop
  loop drop outcome-ok ;

\ ---- Levels, in number order; number 0 is level zero, the store's 0. A
\ store that refuses a node is full; a level of another kind is invalid.
: feed-made ( index true | false -- index outcome )
  if outcome-ok else -1 outcome-full then ;
: feed-a ( l feed -- index ) tuck feed-tier level-a@ swap feed-level@ ;
: feed-b ( l feed -- index ) tuck feed-tier level-b@ swap feed-level@ ;
: feed-two ( l feed -- left right ) 2dup feed-a -rot feed-b ;
: feed-level-made ( l feed -- index outcome )
  2dup feed-tier level-tag@ case
    tag-level-succ of feed-a lf-level-succ feed-made endof
    tag-level-max of feed-two lf-level-max feed-made endof
    tag-level-imax of feed-two lf-level-imax feed-made endof
    tag-level-param of feed-tier level-name@ lf-level-param feed-made endof
    >r 2drop -1 outcome-invalid r> endcase ;
: feed-level ( l feed -- outcome )
  2dup feed-level-made dup ok? if drop -rot feed-level! outcome-ok
  else nip nip nip then ;
: feed-levels-all ( feed -- outcome )
  0 0 2 pick feed-level!
  dup feed-levels# 1 ?do
    i over feed-level dup ok? 0= if nip unloop exit then drop
  loop drop outcome-ok ;

\ ---- Expressions, in number order (a letE spans two records). A store
\ that refuses a term is full; an expression of a kind the checker's stores
\ do not hold (a free or meta variable) is invalid.
: feed-built ( index identity true | false -- index identity outcome )
  if outcome-ok else 0 0 outcome-full then ;
: feed-kept ( index identity outcome e feed -- outcome )
  2>r dup ok? if drop 2r> feed-expr-at 2! outcome-ok else nip nip 2r> 2drop then ;
: feed-a-term ( e feed -- index identity ) tuck feed-tier expr-a@ swap feed-term@ ;
: feed-b-term ( e feed -- index identity ) tuck feed-tier expr-b@ swap feed-term@ ;
: feed-children ( e feed -- l lid r rid ) 2dup feed-a-term 2swap feed-b-term ;
\ A constant's universe arguments, as level handles in the feed's pairs.
\ Pairs hold the index first, then the identity (lf-cref-pair@).
: feed-pair! ( l k feed -- )
  >r swap r@ feed-handle swap rot r> feed-pairs swap lf-cref-pair 2! ;
: feed-args ( t feed -- n outcome )
  dup feed-tier tier-tuples rot swap 2dup tuple-length
  dup 2 cells 5 pick feed-pair-buf feed-grow ok? 0=
  if >r 2drop drop r> outcome-full exit then
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
: feed-core ( e feed tag -- index identity outcome )
  case tag-bvar of feed-tier expr-a@ lf-hterm-bvar feed-built endof
    tag-sort of feed-sort feed-built endof
    tag-const of feed-const feed-built endof
    tag-app of feed-children lf-hterm-app feed-built endof
    >r 2drop 0 0 outcome-invalid r> endcase ;
: feed-term-made ( e feed tag -- index identity outcome )
  dup binder-tag? if feed-binder feed-built exit then
  dup feed-form@ ?dup if nip nip nip lf-hterm-unsupported feed-built else feed-core then ;
: feed-expr ( e feed -- outcome )
  2dup >r >r 2dup feed-tier expr-tag@ feed-term-made r> r> feed-kept ;
: feed-span ( e feed -- units ) feed-tier expr-tag@ let-tag? if 2 else 1 then ;
: feed-exprs-all ( feed -- outcome )
  0 begin over feed-exprs# over > while
    dup 2 pick feed-where ! 2dup swap feed-expr dup ok? 0= if nip nip exit then drop
    2dup swap feed-span +
  repeat 2drop outcome-ok ;

\ ---- Declarations, in file order: the one being fed is feed-d. Kinds as
\ the reader codes them (import/ndjson.fs, kind-axiom on), the checker's
\ (core/input.fs) per kind, 0 for a block; any other kind is invalid.
create feed-kinds
  lf-kind-axiom , lf-kind-definition , lf-kind-theorem , lf-kind-opaque ,
  lf-kind-quotient , 0 , lf-kind-inductive , lf-kind-constructor , lf-kind-recursor ,
here feed-kinds - 1 cells / constant feed-kinds#
\ A field of the declaration being fed, read from the stage with xt
\ ( d stage -- x ); a field of the record being filled, with field-xt
\ ( decl -- addr ); a staged field copied into it, a staged expression as
\ its term.
: feed-staged@ ( feed xt -- x ) >r dup feed-d @ swap feed-stage @ r> execute ;
: feed-field ( feed field-xt -- addr ) swap feed-decl swap execute ;
: feed-copy ( feed xt field-xt -- ) >r over swap feed-staged@ swap r> feed-field ! ;
: feed-term-copy ( feed xt field-xt -- )
  >r over swap feed-staged@ over feed-root swap r> feed-field ! ;
: feed-code ( feed -- i ) ['] staged-kind@ feed-staged@ kind-axiom - ;
: feed-known-kind? ( feed -- flag ) feed-code 0 feed-kinds# within ;
: feed-kind ( feed -- kind ) feed-code cells feed-kinds + @ ;
: feed-kind@ ( feed -- kind ) feed-decl lf-idecl-kind @ ;
: feed-blank ( feed -- )
  dup feed-decl /lf-idecl erase  lf-hint-opaque over ['] lf-idecl-hint feed-field !
  -1 swap ['] lf-idecl-value feed-field ! ;
: feed-start ( feed -- )
  dup feed-blank dup feed-kind over ['] lf-idecl-kind feed-field !
  dup ['] staged-name@ ['] lf-idecl-name feed-copy
  ['] staged-type@ ['] lf-idecl-type feed-term-copy ;
\ A definition's safety and hints, its height when they are regular; any
\ other kind is safe unless marked unsafe (a theorem has no such mark).
: feed-height ( feed -- )
  dup ['] lf-idecl-hint feed-field @ lf-hint-regular =
  if ['] staged-hint@ ['] lf-idecl-height feed-copy else drop then ;
: feed-def ( feed -- )
  dup ['] staged-safety@ ['] lf-idecl-safety feed-copy
  dup ['] staged-hints@ ['] lf-idecl-hint feed-copy feed-height ;
: feed-safe ( unsafe? -- safety ) if lf-safety-unsafe else lf-safety-safe then ;
: feed-safety ( feed -- )
  dup ['] staged-unsafe? feed-staged@ feed-safe swap ['] lf-idecl-safety feed-field ! ;
: feed-valued? ( kind -- flag )
  dup lf-kind-definition = over lf-kind-theorem = or swap lf-kind-opaque = or ;
: feed-value ( feed -- ) ['] staged-value@ ['] lf-idecl-value feed-term-copy ;
: feed-details ( feed -- )
  dup feed-kind@ feed-valued? if dup feed-value then
  dup feed-kind@ lf-kind-definition = if feed-def else feed-safety then ;
\ ---- Inductive blocks (plan task 5.2.1a; ADR 0015 B1): the block
\ record gives a header in the input's inductive data, [first types ctors
\ recursors] (core/input.fs), and the next types + ctors + recursors
\ declarations are its members, each pointing at the header and at its
\ own data cells. A block with no type, or with members missing, cannot
\ come from lean4export and is invalid, as is a member outside a block.
\ Item k of declaration d's data tuple; a cell appended to the data when
\ the outcome so far is ok. The export's numbers are u32 (stage-records);
\ one that is no positive cell (on a host with 32-bit cells) is invalid
\ rather than a negative count (review rvI21 L3).
: feed-item@ ( k d feed -- u ) feed-stage @ staged-item ;
: feed-nth ( d feed k -- d feed u ) >r 2dup r> -rot feed-item@ ;
: feed, ( outcome x -- outcome ) swap dup ok? if drop lf-more, else nip then ;
: feed-u, ( outcome u -- outcome ) dup 0< if 2drop outcome-invalid else feed, then ;
: feed-num, ( d feed outcome k -- d feed outcome ) swap >r feed-nth r> swap feed-u, ;
\ A tuple as a list: its count, then its items.
: feed-list-item ( outcome t cons i -- outcome t cons )
  >r 2dup r> -rot tuple-item >r rot r> feed, -rot ;
: feed-list, ( outcome t cons -- outcome )
  2dup tuple-length >r rot r@ feed, -rot r> 0 ?do i feed-list-item loop 2drop ;
: feed-names, ( d feed outcome k -- d feed outcome )
  swap >r feed-nth over feed-tier tier-tuples r> -rot feed-list, ;
\ A recursor's rules: their count, then constructor, nfields and right
\ side (the term the stage's expression became) of each.
: feed-rule-item ( outcome t feed j -- outcome t feed )
  >r 2dup feed-tier tier-tuples r@ -rot tuple-item
  r> /rule-items mod rule-rhs-item = if over feed-root then >r rot r> feed, -rot ;
: feed-rules, ( outcome t feed -- outcome )
  2dup feed-tier tier-tuples tuple-length >r
  r@ /rule-items mod if r> drop 2drop drop outcome-invalid exit then
  rot r@ /rule-items / feed, -rot r> 0 ?do i feed-rule-item loop 2drop ;
: feed-rules-of, ( d feed outcome k -- d feed outcome )
  swap >r feed-nth over r> -rot feed-rules, ;
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
  more-rec-rules feed-rules-of, ;
: feed-kind-data ( d feed kind -- d feed outcome )
  case kind-type of feed-type-data endof  kind-ctor of feed-ctor-data endof
    kind-recursor of feed-rec-data endof outcome-invalid swap endcase ;
: feed-data ( d feed -- outcome )
  lf-more-here 1+ over feed-decl lf-idecl-more !
  2dup feed-stage @ staged-kind@ feed-kind-data nip nip ;
\ The block record: its header, and the number of members to come.
: feed-header! ( feed -- ) lf-more-here 1+ swap feed-header ! ;
: feed-total ( d feed -- n )
  more-block-types feed-nth >r more-block-ctors feed-nth >r
  more-block-recursors feed-nth nip nip r> + r> + ;
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
\ The universe parameters: their tuple, and parameter i of it, into the
\ feed's buffer, which the record points at; a list the heap cannot hold
\ is full.
: feed-tuple ( feed -- t tuples ) dup ['] staged-params@ feed-staged@ swap feed-tier tier-tuples ;
: feed-param! ( i feed -- )
  2dup feed-tuple tuple-item -rot feed-param-buf @ swap cells + ! ;
: feed-params-room ( feed n -- feed n outcome ) dup 1 cells 3 pick feed-param-buf feed-grow ;
: feed-params ( feed -- outcome )
  dup feed-tuple tuple-length feed-params-room ok? 0= if 2drop outcome-full exit then
  over feed-param-buf @ 2 pick feed-decl lf-idecl-params !
  2dup swap feed-decl lf-idecl-arity ! 0 ?do i over feed-param! loop drop outcome-ok ;
\ The block words above take ( d feed ): the declaration being fed, then
\ the record.
: feed-dfeed ( feed -- d feed ) dup feed-d @ swap ;
: feed-block? ( feed -- flag ) ['] staged-kind@ feed-staged@ kind-inductive = ;
: feed-added ( feed -- outcome )
  dup feed-start dup feed-details dup feed-dfeed feed-joined dup ok? 0= if nip exit then
  drop dup feed-params dup ok? 0= if nip exit then
  drop feed-decl lf-input-add nip ;
: feed-one ( d feed -- outcome )
  tuck feed-d ! dup feed-known-kind? 0= if drop outcome-invalid exit then
  dup feed-block? if feed-dfeed feed-header-record else feed-added then ;
: feed-decls-all ( feed -- outcome )
  dup feed-decls# 0 ?do
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

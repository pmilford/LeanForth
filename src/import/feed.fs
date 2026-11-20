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
\ The expressions are read in place (compact-store plan step S5; see "In
\ place" below): the stage's tier is the term store's input view
\ (core/terms.fs), so expression e's term is the input node 2e + 1, a let
\ and a projection included, and only an mdata expression, which the view
\ does not read, and every node above one are copied; lf-name-detach ends
\ that view too. (The copy of every expression, the way before the view,
\ was retired by step S5's parts 4-5, once the two gave the same reports;
\ tests/cli/test_leanforth.py pins them.) Levels and declarations, and
\ copied expressions, go into the context's stores, whose capacities
\ lf-feed raises to fit the stage plus room for the checks' scratch
\ (feed-room). A copy is made as ndjson-input.fs (tests/support) stages a
\ file: a Sort as a symbolic Sort, a constant through its reference, a
\ projection as the projection of its leaf and its structure term
\ (core/projections.fs; plan task 5.2.2), a natural-number literal as a
\ literal leaf (core/literals.fs; plan task 5.2.3), a string literal as a
\ string leaf of its UTF-8 bytes (core/string-literals.fs; text that is
\ not UTF-8 is invalid), a let as the let of its value and the lambda of
\ its type and body (core/let-terms.fs; plan task 4.2.3), an mdata
\ expression as the leaf of its form (core/unsupported-forms.fs, refused
\ by the audit, U2); binder names and binder information are not copied,
\ as Lean's kernel ignores them (an input binder keeps them in its
\ record, for the printer). An inductive block, a record
\ with no name, gives no declaration but a header in the input's
\ inductive data (core/input.fs); its types, constructors and recursors
\ are declarations that point at the header and carry their exported
\ numbers, lists, flags and rules there (plan task 5.2.1a; the checker of
\ blocks, kernel/check-block.fs, decides them together). Every universe
\ parameter a level names joins the session's level context first.
\
\ lf-feed ( stage feed -- outcome ): ok; invalid for a stage that is not
\ sealed, a level or expression of a kind the checker's stores do not
\ hold (a free or meta variable), a string literal that is not UTF-8, a
\ declaration of a kind it does not
\ know, a block with no type or with members missing, a member outside a
\ block, or a failed loading end; full for a store that refuses a record
\ (its capacity, no heap), the level context, or a universe list longer
\ than the checker takes; feed-at then gives the expression or
\ declaration number where it stopped. The input is left partly filled
\ after a failure: lf-input-reset (or another feed) starts over.
\ feed-free frees the loading aids (lf-feed frees them itself).
\ lf-feed-hooked ( stage feed binder-hook decl-hook -- outcome ) is lf-feed
\ with two optional hooks for a presentation that reads what the feed
\ drops (see "Hooks" below); lf-feed is it with none.
\
\ Shared input (ADR 0016 S8; plan task 7.2.1). lf-feed-shared ( stage
\ feed source -- outcome ) feeds a parallel check's worker
\ (cli/check-run.fs) without a copy of its own: the source context, which
\ lf-feed fed from the same stage and which makes nothing while others
\ read it, keeps the one input every worker reads in place -- its
\ declarations, their name index and inductive data (core/input.fs's
\ lf-input-borrow), the view's leaf and binder tables (core/terms.fs's
\ lf-term-borrow) and its references (core/constant-references.fs's
\ lf-cref-borrow) -- and the worker builds only what its checks write
\ beside or above: its levels (made as the source made them, so equal
\ numbers and identities), the level context, the session, its literals'
\ limbs and bytes (copied: a few kilobytes) and the copies of mdata
\ expressions, of binders the source gave an earlier binder of their ==
\ class, and of the nodes above them, if the source made any. Its
\ input's fingerprint is then the source's (cli/check-run.fs checks it).
\
\ State: none of its own; every word takes a feed record (/feed), which
\ owns its heap blocks (the levels' export-to-store map, zeroed, so that
\ an entry never set is no handle; a bit per expression and the list of
\ copies) only during lf-feed.

require ../lib/bytes.fs
require ../lib/blocks.fs
require ../lib/bits.fs
require ../core/compact.fs
require ../core/input.fs
require ../core/unsupported-forms.fs
require ../core/constant-term-boundary.fs
require ../core/let-terms.fs
require ../core/literals.fs
require ../core/string-literals.fs
require ../core/projections.fs
require ./stage.fs

\ Room for the checks' scratch above the input, in each store (plan task
\ 6.2.2; compact-store plan step S5): the context's setting
\ (core/input.fs's lf-input-room!), or with none the most a store may
\ hold, about 2^31 records, so that term numbers stay below 2^32 above an
\ input of up to 2^31 nodes (fewer on a host whose cells address less).
\ The block grows only as records are made. Before step S5 the rooms were
\ fixed: 1,048,576 term nodes, 65,536 levels, 262,144 references.
: feed-most ( -- n ) max-n 256 / 1 31 lshift 1- min ;
: feed-scratch ( -- n ) lf-input-room ?dup 0= if feed-most then ;
: feed-term-room ( -- n ) feed-scratch ;
: feed-level-room ( -- n ) feed-scratch ;
: feed-cref-room ( -- n ) feed-scratch ;

begin-structure /feed
  field: feed-stage        \ the sealed stage
  field: feed-levels       \ heap: per stage level, its store index
  field: feed-where        \ the expression or declaration where it stopped
  field: feed-d            \ the declaration being fed
  field: feed-header       \ the current block's header cell, plus one; 0 for none
  field: feed-binder-hook  \ xt ( term name kind -- ) of each binder made, or 0
  field: feed-decl-hook    \ xt ( d before after -- ) of each declaration fed, or 0
  field: feed-members      \ members of the current block still to come
  2 cells +field feed-pair-buf   \ heap: a constant's level pairs, and their room
  2 cells +field feed-param-buf  \ heap: a declaration's parameters, and their room
  field: feed-dirty        \ heap: a bit per stage expression copied
  2 cells +field feed-copy-buf   \ heap: the copies, and their room
  field: feed-copies#      \ the copies made
  field: feed-source       \ lf-feed-shared's source context, or 0
  /lf-idecl +field feed-decl
end-structure

: feed-tier ( feed -- tier ) feed-stage @ stage-tier ;
: feed-at ( feed -- n ) feed-where @ ;
: feed-free ( feed -- )
  dup feed-levels heap-release dup feed-dirty heap-release
  dup feed-copy-buf heap-release dup feed-pair-buf heap-release
  feed-param-buf heap-release ;
\ A heap buffer of the feed's (its address, then its room in units):
\ room for n units of u address units, grown, never shrunk, freed by
\ feed-free. There is no other limit (plan task 6.2.0); no heap is full.
: feed-grow ( n u buffer -- outcome )
  >r over r@ cell+ @ > 0= if 2drop r> drop outcome-ok exit then
  over * r@ block-resize dup ok? if swap r> cell+ ! else nip r> drop then ;
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
  field: setting-room      \ xt ( -- n )
  field: setting-get       \ xt ( -- n )
  field: setting-set       \ xt ( n -- outcome )
end-structure
: feed-no-room ( -- 0 ) 0 ;
create feed-settings
  ' feed-exprs# , ' feed-term-room , ' lf-term-capacity , ' lf-term-capacity! ,
  ' feed-levels# , ' feed-level-room , ' lf-level-capacity , ' lf-level-capacity! ,
  ' feed-exprs# , ' feed-cref-room , ' lf-cref-capacity , ' lf-cref-capacity! ,
  ' feed-decls# , ' feed-no-room , ' lf-input-capacity , ' lf-input-capacity! ,
here feed-settings - /feed-setting / constant feed-settings#
\ Raise a setting to n, after an earlier ok; the first failure stays.
: feed-raise ( outcome n get-xt set-xt -- outcome )
  >r execute max r> rot dup ok? if drop execute else nip nip then ;
: feed-setting ( outcome feed row -- outcome )
  >r r@ setting-records @ execute r@ setting-room @ execute +
  r@ setting-get @ r> setting-set @ feed-raise ;
\ The term store holds only the copies (see "In place"): its
\ hash-consing table is not sized for every expression, and feed-room
\ sets its capacity to what the copies left.
: feed-capacities ( feed -- outcome )
  outcome-ok feed-settings# 0 do
    over i /feed-setting * feed-settings + feed-setting
  loop nip ;

\ After the expressions are fed the term store's capacity is set to the
\ copies plus the room: each check gets the whole of feed-term-room.
: feed-room ( feed -- outcome ) drop lf-term-count @ feed-term-room + lf-term-capacity! ;

\ ---- Maps: heap blocks of cells, zeroed, freed by feed-free.
: feed-block ( cells addr -- outcome ) swap cells swap block-zeroed ;
\ The expressions need no map (see "In place" below), only a bit each,
\ set for the ones copied.
: feed-expr-map ( feed -- outcome )
  dup feed-exprs# bits>cells swap feed-dirty feed-block ;
: feed-maps ( feed -- outcome )
  dup feed-levels# over feed-levels feed-block dup ok? 0= if nip exit then
  drop feed-expr-map ;
: feed-level! ( index l feed -- ) feed-levels @ swap cells + ! ;
: feed-level@ ( l feed -- index ) feed-levels @ cell-at@ ;
: feed-handle ( l feed -- index identity )
  feed-level@ lf-level-handle ;

\ ---- In place (compact-store plan step S5; core/terms.fs's input view).
\ The term store reads the stage's expressions in place, lets and
\ projections too (parts 4-5), so the feed copies only what the view does
\ not read: an mdata expression and every node above one (none in an
\ export written without --export-mdata). A copied expression's bit is
\ set, and its term handle kept with it in a list in ascending expression
\ order (copies are made in number order), found by binary search; any
\ other expression e's term is the input node 2e + 1 (terms.fs's
\ numbering). Leaves whose fields are this context's get them in the
\ view's leaf table: a Sort its level, a constant its reference (made as
\ when copying), a literal its limbs or bytes in the context's slabs.
\ Levels, references and declarations are as when copying.
: feed-dirty? ( e feed -- flag ) feed-dirty @ bit@ ;
: feed-dirty! ( e feed -- ) feed-dirty @ bit-on ;
begin-structure /feed-copy
  field: feed-copied-e                  \ the expression
  2 cells +field feed-copied-handle     \ its term handle: index, identity (2@)
end-structure
: feed-copy-at ( k feed -- addr ) feed-copy-buf @ swap /feed-copy * + ;
: feed-copy-e ( k feed -- e ) feed-copy-at feed-copied-e @ ;
\ Room for one more copy; the next copy, counted.
: feed-copy-room ( feed -- outcome )
  dup feed-copies# @ 1+ /feed-copy rot feed-copy-buf feed-grow ;
: feed-copy-next ( feed -- addr )
  dup feed-copies# dup @ swap 1 swap +! swap feed-copy-at ;
: feed-copy+ ( index identity e feed -- outcome )
  dup feed-copy-room ok? 0= if 2drop 2drop outcome-full exit then
  feed-copy-next tuck feed-copied-e ! feed-copied-handle 2! outcome-ok ;
\ Binary search (lib/bits.fs): the first copy whose expression is not
\ below e.
: feed-copy-below? ( e feed k -- e feed flag ) over feed-copy-e 2 pick < ;
: feed-seek ( e feed -- e feed k )
  0 over feed-copies# @ ['] feed-copy-below? lower-bound ;
\ Copy k when it is expression e's, else 0.
: feed-copy-of ( e feed k -- addr|0 )
  2dup swap feed-copies# @ < 0= if 2drop drop 0 exit then
  swap feed-copy-at tuck feed-copied-e @ = and ;
\ A copied expression's handle; 0 0, no handle, for one not in the list.
: feed-copy@ ( e feed -- index identity )
  feed-seek feed-copy-of ?dup if feed-copied-handle 2@ else 0 0 then ;
: feed-term@ ( e feed -- index identity )
  2dup feed-dirty? if feed-copy@ else drop lf-tin-child dup lf-term-input-identity then ;
: feed-root ( e feed -- index ) feed-term@ drop ;

\ ---- The level context: every parameter a level names.
: feed-param ( name -- outcome )
  dup lf-lscope-member? if drop outcome-ok exit then
  lf-lscope-context-add if outcome-ok else outcome-full then ;
: feed-level-param ( l tier -- outcome )
  2dup level-tag@ tag-level-param = if level-name@ feed-param else 2drop outcome-ok then ;
: feed-param-at ( tier l -- tier outcome ) over feed-level-param ;
: feed-context ( feed -- outcome )
  dup feed-tier swap feed-levels# ['] feed-param-at ok-each nip ;

\ ---- Levels, in number order; number 0 is level zero, the store's 0. A
\ store that refuses a node is full; a level of another kind is invalid.
: feed-a ( l feed -- index ) tuck feed-tier level-a@ swap feed-level@ ;
: feed-b ( l feed -- index ) tuck feed-tier level-b@ swap feed-level@ ;
: feed-two ( l feed -- left right ) 2dup feed-a -rot feed-b ;
: feed-level-made ( l feed -- index outcome )
  2dup feed-tier level-tag@ case
    tag-level-succ of feed-a lf-level-succ room-result endof
    tag-level-max of feed-two lf-level-max room-result endof
    tag-level-imax of feed-two lf-level-imax room-result endof
    tag-level-param of feed-tier level-name@ lf-level-param room-result endof
    >r 2drop -1 outcome-invalid r> endcase ;
: feed-level ( l feed -- outcome )
  2dup feed-level-made dup ok? if drop -rot feed-level! outcome-ok
  else nip nip nip then ;
\ Level k + 1 (number 0 is zero, set first).
: feed-level-next ( feed k -- feed outcome ) 1+ over feed-level ;
: feed-levels-all ( feed -- outcome )
  0 0 2 pick feed-level! dup feed-levels# 1- ['] feed-level-next ok-each nip ;

\ ---- Hooks (lf-feed-hooked): a presentation reads what the feed drops, the
\ names and kinds of binders and the line each declaration came from, while
\ the maps that give a stage record's term exist. A hook that is 0 is not
\ called, so a feed without hooks is the feed of lf-feed.
\ The binder hook is given the term's index, the binder's name and its kind
\ (0 explicit, 1 implicit, 2 strict implicit, 3 instance), after the term
\ is made.
: feed-binder-info ( tag -- kind ) tag-lam - 3 and ;
: feed-note-binder ( e feed hook -- )
  >r 2dup feed-root >r 2dup feed-tier expr-payload@ >r feed-tier expr-tag@
  feed-binder-info r> swap r> -rot r> execute ;
: feed-binder-noted ( e feed -- )
  dup feed-binder-hook @ ?dup 0= if 2drop exit then
  >r 2dup feed-tier expr-tag@ binder-tag? if r> feed-note-binder else r> drop 2drop then ;
\ ---- Expressions, in number order (a letE spans two records). A store
\ that refuses a term is full; an expression of a kind the checker's stores
\ do not hold (a free or meta variable) is invalid.
: feed-built ( index identity true | false -- index identity outcome )
  if outcome-ok else 0 0 outcome-full then ;
\ The term made for expression e kept in the list of copies (full when
\ the heap cannot hold it).
: feed-kept ( index identity outcome e feed -- outcome )
  2>r dup ok? if drop 2r> feed-copy+ else nip nip 2r> 2drop then ;
: feed-a-term ( e feed -- index identity ) tuck feed-tier expr-a@ swap feed-term@ ;
: feed-b-term ( e feed -- index identity ) tuck feed-tier expr-b@ swap feed-term@ ;
: feed-children ( e feed -- l lid r rid ) 2dup feed-a-term 2swap feed-b-term ;
\ A constant's universe arguments, as level handles in the feed's pairs.
\ Pairs hold the index first, then the identity (lf-cref-pair@).
: feed-pair! ( l k feed -- )
  >r swap r@ feed-handle swap rot r> feed-pairs swap lf-cref-pair 2! ;
: feed-pairs-room ( n feed -- outcome ) 2 cells swap feed-pair-buf feed-grow ;
\ Level k of tuple t as pair k.
: feed-arg ( t k feed -- )
  >r tuck swap r@ feed-tier tier-tuples tuple-item swap r> feed-pair! ;
: feed-args ( t feed -- n outcome )
  2dup feed-tier tier-tuples tuple-length dup 2 pick feed-pairs-room ok? 0=
  if nip nip outcome-full exit then
  dup >r 0 ?do over i 2 pick feed-arg loop 2drop r> outcome-ok ;
: feed-cref ( e feed -- cref identity true | false )
  2dup feed-tier expr-b@ over feed-args ok? 0= if drop 2drop false exit then
  >r tuck feed-tier expr-a@ lf-name-generation @ rot feed-pairs r> lf-cref-new ;
\ The unsupported form of each expression tag, 0 for a supported one
\ (core/unsupported-forms.fs); a table filled while loading.
tag-mdata 1+ constant feed-tags#
create feed-forms feed-tags# cells allot  feed-forms feed-tags# cells erase
: feed-form! ( form tag -- ) cells feed-forms + ! ;
lf-form-mdata tag-mdata feed-form!
: feed-form@ ( tag -- form )
  dup 0 feed-tags# within if cells feed-forms + @ else drop 0 then ;
\ A projection (plan task 5.2.2): the leaf of its structure's name and
\ field index with its structure term (core/projections.fs).
: feed-proj ( e feed -- index identity true | false )
  2dup feed-tier expr-payload@ >r 2dup feed-tier expr-b@ r> swap lf-hterm-proj
  0= if 2drop false exit then
  2swap feed-a-term lf-hterm-projection ;
\ A literal's text (plan task 5.2.3): a natural number's decimal digits,
\ a string's UTF-8 bytes.
: feed-text ( e feed -- addr u ) feed-tier tuck expr-a@ swap tier-texts text@ ;
\ A let (plan task 4.2.3): let x : T := v; b as the let of v and
\ fun x : T => b, with the nonDep flag (core/let-terms.fs); the body is
\ the letE's second record.
: feed-let-body ( e feed -- index identity ) tuck feed-tier expr-body@ swap feed-term@ ;
: feed-let-lam ( e feed -- index identity true | false )
  2dup feed-a-term 2swap feed-let-body lf-hterm-lam ;
: feed-let ( e feed nondep -- index identity true | false )
  >r 2dup feed-let-lam 0= if 2drop r> drop false exit then
  2swap feed-b-term 2swap r> lf-hterm-let ;
: feed-binder ( e feed tag -- index identity true | false )
  >r feed-children r> tag-pi < if lf-hterm-lam else lf-hterm-pi then ;
\ A copy is made only of an mdata expression or a node above one (see
\ "In place" below), never of a leaf, which has no child.
: feed-core ( e feed tag -- index identity outcome )
  case tag-app of feed-children lf-hterm-app feed-built endof
    tag-proj of feed-proj feed-built endof
    tag-let of false feed-let feed-built endof
    tag-let-nondep of true feed-let feed-built endof
    >r 2drop 0 0 outcome-invalid r> endcase ;
: feed-term-made ( e feed tag -- index identity outcome )
  dup binder-tag? if feed-binder feed-built exit then
  dup feed-form@ ?dup if nip nip nip lf-hterm-unsupported feed-built else feed-core then ;
: feed-expr ( e feed -- outcome )
  2dup >r >r 2dup feed-tier expr-tag@ feed-term-made r> r> 2dup 2>r feed-kept
  dup ok? if 2r> feed-binder-noted else 2r> 2drop then ;
: feed-span ( e feed -- units ) feed-tier expr-tag@ let-tag? if 2 else 1 then ;
\ In place (see "In place" above): a copied expression is made as when
\ copying; any other is read in place, a leaf whose fields are this
\ context's given them in the view's leaf table, with the same outcomes
\ as when copying (full when a level is not live or a store refuses,
\ invalid for text that is not UTF-8 or a kind the checker does not
\ hold).
: feed-a-copied? ( e feed -- flag ) tuck feed-tier expr-a@ swap feed-dirty? ;
: feed-b-copied? ( e feed -- flag ) tuck feed-tier expr-b@ swap feed-dirty? ;
: feed-child-copied? ( e feed -- flag ) 2dup feed-a-copied? >r feed-b-copied? r> or ;
: feed-let-copied? ( e feed -- flag )
  2dup feed-child-copied? >r tuck feed-tier expr-body@ swap feed-dirty? r> or ;
: feed-to-copy? ( e feed tag -- flag )
  case tag-mdata of 2drop true endof  tag-proj of feed-a-copied? endof
    tag-let of feed-let-copied? endof  tag-let-nondep of feed-let-copied? endof
    tag-app of feed-child-copied? endof
    binder-tag? if feed-child-copied? else 2drop false then 0 endcase ;
: feed-leaf! ( first second stamp e -- outcome ) lf-tin-child lf-term-input-leaf ;
: feed-leaf0! ( first second e -- outcome ) 0 swap feed-leaf! ;
: feed-sort-leaf ( e feed -- outcome )
  over >r tuck feed-tier expr-a@ swap feed-handle
  2dup lf-hlevel-valid? 0= if 2drop r> drop outcome-full exit then 0 swap r> feed-leaf! ;
: feed-const-leaf ( e feed -- outcome )
  over >r feed-cref 0= if r> drop outcome-full exit then 0 swap r> feed-leaf! ;
: feed-nat-leaf ( e feed -- outcome )
  over >r feed-text lf-lit-decimal 0= if r> drop outcome-full exit then r> feed-leaf0! ;
: feed-str-leaf ( e feed -- outcome )
  over >r feed-text lf-str-fields ok-then2? 0= if r> drop exit then r> feed-leaf0! ;
\ A projection: its leaf the first input leaf of the same structure name
\ and field index, else the record's own (term 2e), entered; then the
\ projection of that leaf and its structure term (core/terms.fs).
: feed-proj-fields ( e feed -- name idx )
  2dup feed-tier expr-payload@ -rot feed-tier expr-b@ ;
: feed-proj-leaf ( e feed -- leaf outcome )
  over >r feed-proj-fields 2dup lf-tag-proj -rot lf-tin-leaf-find
  if nip nip r> drop outcome-ok exit then
  0 r@ 2* lf-term-input-leaf r> 2* swap ;
: feed-projection ( e feed -- outcome )
  2dup feed-proj-leaf ok-then? 0= if nip nip exit then
  -rot over swap feed-tier expr-a@ lf-tin-child swap feed-leaf0! ;
\ A let: the let of its value and its lambda, the first input binder of
\ the lambda's type and body (an earlier lambda equal to it, or the
\ let's own, term 2e, which feed-mark entered), so that the two are one
\ node, as when copied.
: feed-let-lam-node ( e feed -- lam )
  feed-tier over >r 2dup expr-a@ lf-tin-child -rot expr-body@ lf-tin-child
  lf-tag-lam -rot lf-tin-binder-find if r> drop else r> 2* then ;
: feed-let-leaf ( e feed -- outcome )
  2dup feed-let-lam-node >r over swap feed-tier expr-b@ lf-tin-child r> rot feed-leaf0! ;
\ A let's tag (its nonDep flag) and fields in the leaf table: its value
\ and lambda.
: feed-let-fields ( e feed -- tag first second )
  over lf-tin-child lf-tin-tag@ >r 2dup feed-let-lam-node >r
  feed-tier expr-b@ lf-tin-child r> r> -rot ;
: feed-read-kind? ( tag -- flag )
  dup tag-bvar = over tag-app = or swap binder-tag? or ;
: feed-leaf ( e feed tag -- outcome )
  dup feed-read-kind? if drop 2drop outcome-ok exit then
  case tag-sort of feed-sort-leaf endof  tag-const of feed-const-leaf endof
    tag-nat of feed-nat-leaf endof  tag-str of feed-str-leaf endof
    tag-proj of feed-projection endof
    tag-let of 2drop outcome-ok endof  tag-let-nondep of 2drop outcome-ok endof
    >r 2drop outcome-invalid r> endcase ;
\ Two passes. The first marks the expressions to copy and enters every
\ binder read in place, and every let's lambda, in the view's binder
\ table (core/terms.fs), so that a binder made equal to it is it (a
\ binder a copy or a check makes; before step S5's parts 4-5 a let's
\ lambda copied before the binder's own number came up: 47 such binders
\ in Init cost 22 of its declarations more fuel without this pass); a
\ binder == to one entered before it is marked to copy instead (below).
\ The second makes the copies and the leaves' fields.
\ A binder read in place that is == to one entered before it (the same tag
\ and children, another binder name or information) is copied instead,
\ and the copy is that earlier binder (lf-term-add finds it in the binder
\ table), so that every == class of input binders is one node and so is
\ every node above them: a check no longer meets another declaration's
\ or a snapshot's record of a binder's class (review rvSN4 B1; ADR 0014
\ Amendment 7, rule 1; rules 2 and 3 are terms.fs's and levels.fs's). Only
\ without a binder hook: the print command, which sets one, keeps each
\ binder's own name.
\ Lets likewise (review rvRS F2): Lean's == compares a let's type, value,
\ body and nonDep flag, never its name (expr_eq_fn.cpp 104-109), so a let
\ read in place that is == to one entered before it (the same tag, value
\ and lambda in the leaf table) is copied instead, and its copy is that
\ earlier let (lf-term-add finds it in the leaf table by its fields).
\ Every other let's leaf is entered here, in the first pass, so that a
\ later let finds it; the second pass has nothing left to give a let.
: feed-merging? ( feed -- flag ) feed-binder-hook @ 0= ;
: feed-redirect? ( feed first? -- flag ) 0= swap feed-merging? and ;
: feed-merge ( e feed first? outcome -- outcome )
  dup ok? 0= if >r drop 2drop r> exit then drop
  over swap feed-redirect? if feed-dirty! else 2drop then outcome-ok ;
: feed-enter-binder ( e feed -- outcome )
  over lf-tin-child lf-term-input-binder-first feed-merge ;
: feed-let-merged? ( e feed -- flag )
  dup feed-merging? 0= if 2drop false exit then
  feed-let-fields lf-tin-leaf-find dup if nip then ;
: feed-enter-let ( e feed -- outcome )
  over 2* lf-term-input-binder ok-then2? 0= if exit then
  2dup feed-let-merged? if feed-dirty! outcome-ok else feed-let-leaf then ;
: feed-enter ( e feed tag -- outcome )
  dup binder-tag? if drop feed-enter-binder exit then
  let-tag? if feed-enter-let else 2drop outcome-ok then ;
: feed-mark ( e feed -- outcome )
  2dup feed-tier expr-tag@ >r 2dup r@ feed-to-copy?
  if r> drop feed-dirty! outcome-ok exit then r> feed-enter ;
: feed-place ( e feed -- outcome )
  2dup feed-dirty? if feed-expr exit then 2dup feed-tier expr-tag@ feed-leaf ;
: feed-each ( feed xt -- outcome )
  >r 0 begin over feed-exprs# over > while
    dup 2 pick feed-where ! 2dup swap r@ execute dup ok? 0= if r> drop nip nip exit then
    drop 2dup swap feed-span +
  repeat r> drop 2drop outcome-ok ;
: feed-exprs-all ( feed -- outcome )
  dup ['] feed-mark feed-each dup ok? 0= if nip exit then drop ['] feed-place feed-each
  dup ok? if drop lf-term-view-grown then ;

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
: feed-value ( feed -- ) ['] staged-value@ ['] lf-idecl-value feed-term-copy ;
: feed-details ( feed -- )
  dup feed-kind@ lf-kind-valued? if dup feed-value then
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
: feed-nth ( d feed k -- d feed u ) 2dup-under -rot feed-item@ ;
: feed, ( outcome x -- outcome ) swap dup ok? if drop lf-more, else nip then ;
: feed-u, ( outcome u -- outcome ) dup 0< if 2drop outcome-invalid else feed, then ;
: feed-num, ( d feed outcome k -- d feed outcome ) swap >r feed-nth r> swap feed-u, ;
\ A tuple as a list: its count, then its items.
: feed-list-item ( outcome t cons i -- outcome t cons )
  2dup-under -rot tuple-item >r rot r> feed, -rot ;
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
  if 2dup more-block-types feed-nth nip nip 0<> >r feed-total 0= r> or
  else 2drop false then ;
\ An empty block (no type, constructor or recursor; ADR 0016 amendment 1)
\ becomes one declaration of kind lf-kind-block, a member of its own
\ block: the checker rejects it as Lean's kernel does (emptyBlock).
: feed-empty-block ( feed -- outcome )
  dup feed-blank lf-kind-block over ['] lf-idecl-kind feed-field !
  -1 over ['] lf-idecl-type feed-field !
  dup feed-header @ over ['] lf-idecl-block feed-field !
  feed-decl lf-input-add nip ;
: feed-emptied ( outcome feed -- outcome )
  over ok? over feed-members @ 0= and if nip feed-empty-block else drop then ;
: feed-header-record ( d feed -- outcome )
  2dup feed-block-ok? 0= if 2drop outcome-invalid exit then
  dup >r dup feed-header! outcome-ok lf-input-count feed,
  more-block-types feed-num, more-block-ctors feed-num, more-block-recursors feed-num,
  feed-members! r> feed-emptied ;
\ A member of the current block, or any other declaration.
: feed-member? ( d feed -- flag )
  feed-stage @ staged-kind@ kind-type kind-ctor kind-recursor one-of3? ;
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
: feed-tuple ( feed -- t tuples )
  dup ['] staged-params@ feed-staged@ swap feed-tier tier-tuples ;
: feed-param! ( i feed -- )
  2dup feed-tuple tuple-item -rot feed-param-buf @ swap cells + ! ;
: feed-params-room ( feed n -- feed n outcome )
  dup 1 cells 3 pick feed-param-buf feed-grow ;
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
\ Declaration d fed: the declaration hook is given d and the numbers of
\ input declarations before and after it (a block's members one by one,
\ its header none).
: feed-decl-noted ( d before feed -- )
  feed-decl-hook @ ?dup if >r lf-input-count r> execute else 2drop then ;
: feed-decl-one ( d feed -- outcome )
  2dup lf-input-count -rot feed-one
  dup ok? if drop swap feed-decl-noted outcome-ok else >r 2drop drop r> then ;
: feed-decl-at ( feed d -- feed outcome ) 2dup swap feed-where ! over feed-decl-one ;
: feed-decls-all ( feed -- outcome ) dup feed-decls# ['] feed-decl-at ok-each nip ;

\ ---- The whole feed: the steps ( feed -- outcome ), in order. The first
\ ends any earlier term view and attaches the stage's tier as the terms'
\ view (core/terms.fs) after its names.
: feed-unview ( -- ) lf-term-viewed? if lf-term-detach drop then ;
: feed-fresh ( feed -- outcome )
  feed-unview lf-input-reset lf-term-reset lf-level-reset lf-cref-reset
  lf-lscope-context-reset dup feed-tier lf-name-attach dup ok? 0= if nip exit then
  drop feed-tier lf-term-attach ;
: feed-session ( feed -- outcome ) drop lf-ssession-begin flag>outcome ;
: feed-end ( feed -- outcome ) feed-members @ if outcome-invalid else lf-input-end then ;

\ ---- Sharing (see "Shared input" in the header): what the source context
\ fed is read in place or copied, each share ( source -- outcome ) in
\ order; then the source's copies, if it made any, are made again.
create feed-shares
  ' lf-term-borrow , ' lf-cref-borrow , ' lf-input-borrow ,
  ' lf-lit-copy , ' lf-str-copy ,
here feed-shares - 1 cells / constant feed-shares#
: feed-share ( source k -- source outcome ) cells feed-shares + @ over swap execute ;
: feed-borrow ( feed -- outcome ) feed-source @ feed-shares# ['] feed-share ok-each nip ;
\ The copies: the same expressions marked (no binder entered: the table
\ is the source's) and copied, each with the horizon of its expression
\ (core/terms.fs's lf-term-horizon!), so that it finds only the leaves
\ the source's feed had entered when it made that copy. A binder the
\ source gave an earlier one of its == class (feed-merge, above; the
\ source has no binder hook: the print command, which sets one, makes no
\ workers) is one whose class the source's table holds another binder
\ for; without it the worker's copies, and so its fingerprint, would not
\ be the source's and no worker could be made.
\ A let likewise: the source's leaf table holds an earlier let of its ==
\ class (whose leaf the source entered instead of this one's).
: feed-let-was-merged? ( e feed -- flag )
  over >r feed-let-fields lf-tin-leaf-find if r> lf-tin-child <> else r> drop false then ;
: feed-was-merged? ( e feed tag -- flag )
  dup let-tag? if drop feed-let-was-merged? exit then
  binder-tag? if drop lf-tin-child lf-term-input-binder-merged? else 2drop false then ;
: feed-shared-copy? ( e feed tag -- flag )
  >r 2dup r@ feed-to-copy? if 2drop r> drop true else r> feed-was-merged? then ;
: feed-mark-copy ( e feed -- outcome )
  2dup 2dup feed-tier expr-tag@ feed-shared-copy? if feed-dirty! else 2drop then
  outcome-ok ;
: feed-place-copy ( e feed -- outcome )
  2dup feed-dirty? 0= if 2drop outcome-ok exit then over 2* lf-term-horizon! feed-expr ;
: feed-made-copies? ( feed -- flag )
  lf-terms swap feed-source @ lf-member-in store-count @ 0<> ;
: feed-copies ( feed -- outcome )
  dup feed-made-copies? 0= if drop outcome-ok exit then
  dup ['] feed-mark-copy feed-each dup ok? 0= if nip exit then
  drop ['] feed-place-copy feed-each lf-term-unbounded ;

\ The steps of a feed and of a shared feed, as many in each.
create feed-steps
  ' feed-fresh , ' feed-capacities , ' feed-maps , ' feed-context , ' feed-session ,
  ' feed-levels-all , ' feed-exprs-all , ' feed-room , ' feed-decls-all , ' feed-end ,
here feed-steps - 1 cells / constant feed-steps#
create feed-shared-steps
  ' feed-fresh , ' feed-capacities , ' feed-maps , ' feed-context , ' feed-session ,
  ' feed-levels-all , ' feed-borrow , ' feed-copies , ' feed-room , ' feed-end ,
here feed-shared-steps - 1 cells / feed-steps# <>
[if] .( feed.fs: the shared feed must have as many steps) cr abort [then]
: feed-table ( feed -- addr ) feed-source @ if feed-shared-steps else feed-steps then ;
: feed-step ( feed k -- feed outcome ) cells over feed-table + @ over swap execute ;
: feed-run ( feed -- outcome ) feed-steps# ['] feed-step ok-each nip ;
\ Feed the sealed stage into this context's input (see the header).
\ The same with hooks, each an xt or 0: binder-hook ( term name kind -- ),
\ called for every binder after its term is made, and decl-hook
\ ( d before after -- ), called after each declaration; neither may change a
\ store of the checker (the presentation's side table is not one; this is
\ not enforced). A THROW from a hook passes on after the feed's loading aids
\ are freed; the names stay attached to the stage, as after any THROW in a
\ feed, so the caller detaches them (lf-name-detach; cli/check-run.fs's
\ ck-release does).
\ The binder hook sees only the binders the feed copies (those above an
\ mdata expression): an input binder read in place keeps its name and
\ kind in its record (core/terms.fs's lf-term-input-binder@, which the
\ print command's side table reads).
: feed-set ( stage feed binder-hook decl-hook -- feed )
  2>r dup /feed erase tuck feed-stage !
  2r> 2 pick feed-decl-hook ! over feed-binder-hook ! ;
: feed-go ( feed -- outcome )
  dup feed-stage @ stage-sealed? 0= if drop outcome-invalid exit then
  dup ['] feed-run catch ?dup if >r drop feed-free r> throw then swap feed-free ;
: lf-feed-hooked ( stage feed binder-hook decl-hook -- outcome ) feed-set feed-go ;
: lf-feed ( stage feed -- outcome ) 0 0 lf-feed-hooked ;
\ The shared feed (see "Shared input" in the header): this context shares
\ the input that the source context, another, was fed from the same stage
\ by lf-feed and has not changed since: ok; invalid when it cannot be
\ shared (another stage, a source that made references since it sealed or
\ shares another's itself, or this context itself), or as lf-feed. A
\ THROW passes on as from lf-feed.
: lf-feed-shared ( stage feed source -- outcome )
  >r 0 0 feed-set r> over feed-source ! feed-go ;
\ Detaching the names of a stage ends its term view too (core/names.fs).
:noname ( -- ) feed-unview ; is lf-name-detach-hook

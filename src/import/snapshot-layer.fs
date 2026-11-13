\ A layer's tier entered on into a loaded tier (ADR 0020 amendment 1, F5;
\ plan task 6.2.5, step SN4). Untrusted [format][import] code,
\ fail-closed; LeanForth-specific. A layer (kernel/env-snapshot.fs) holds
\ the records a run that read an export on into its base's tier added to
\ it, numbered on from the base's counts (the firsts), and the
\ declarations that run checked. ly-load enters a layer's records into a
\ filled stage that holds the base, and any layers loaded before it, the
\ way a continued read enters an export's (stage-continue): each record
\ is built again by its family's builder (core/compact*.fs, lib/pools.fs),
\ which checks it (ADR 0016 C8) and finds an equal one already there,
\ after its parts are given their numbers here -- a number below the
\ base's count is the base's own; from it on, the layer's record, which
\ must come earlier in the layer and was entered already. So two layers
\ written on one base load together, sharing their equal records. A
\ list's items have no kind of their own: a list is built again for the
\ kind its user says (a constant's levels; a declaration's parameter
\ names and kind data), and a list a user names must start a list of the
\ layer. A name's or a text's bytes are the layer's own (a new record's
\ bytes come after the base's). The declarations are translated into
\ ly-decl records, their chains not set; the caller (kernel/env-layers.fs)
\ enters each it keeps with ly-enter, which checks it as the stage checks
\ a draft and links it to its name.
\
\ The sections are the tier's (import/snapshot-tier.fs): 1 name bytes, 2
\ names, 3 levels, 4 lists, 5 text bytes, 6 texts, 7 expressions, 8
\ declarations, 9 lines. The layer's metadata texts are not read (the
\ base's stand). Each section is a family (/ly-fam): where it was read,
\ the map of its own records, the base's count of it.
\
\ Outcomes (ADR 0008): ok; invalid for a malformed layer or a reference
\ that is not a record (ly-why names the section, ly-where the record);
\ full for no heap or the stage's memory limit. Records entered stay
\ entered after a failure: the caller frees the stage. State: one /layer
\ record per layer being entered, used by one task, holding one /ly-fam
\ record per section; ly-free frees their blocks.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/outcome.fs
require ../lib/u32.fs
require ../lib/bytes.fs
require ../lib/slab.fs
require ../lib/cons.fs
require ../lib/pools.fs
require ../lib/sections.fs
require ../core/compact.fs
require ./stage.fs
require ./snapshot-tier.fs

\ A section of the layer, the family of its records.
begin-structure /ly-fam
  field: fam-layer     \ the layer it is a section of
  field: fam-pos       \ its position, 1-9
  field: fam-block     \ the section read whole, 32-bit fields made the host's
  field: fam-map       \ per own record: its number here + 1
  field: fam-first     \ the base's count of the family (sections 1-8)
  field: fam-begun     \ while it is entered: its count before
  field: fam-top       \ and the highest number this layer kept of it
end-structure
begin-structure /layer
  field: ly-tf                            \ the layer's tier file (its sections)
  field: ly-stage                         \ the stage entered into
  tier-sections# /ly-fam * +field ly-fams \ the sections' families, by position
  field: ly-why                           \ counted string: the section refused, or 0
  field: ly-where                         \ the record refused
end-structure
\ Positions of the sections.
1 constant lp-name-bytes  2 constant lp-names  3 constant lp-levels  4 constant lp-lists
5 constant lp-text-bytes  6 constant lp-texts  7 constant lp-exprs  8 constant lp-decls
9 constant lp-lines

: ly@ ( i addr -- u ) swap u32s + u32@ ;
: ly! ( u i addr -- ) swap u32s + u32! ;
: ly-fam ( i ly -- fam ) ly-fams swap /ly-fam * + ;
: ly-units ( i ly -- n ) ly-tf @ tf-units ;
: ly-tier ( ly -- tier ) ly-stage @ stage-tier ;
: ly-lists ( ly -- fam ) lp-lists swap ly-fam ;
: fam-ly ( fam -- ly ) fam-layer @ ;
: fam-tier ( fam -- tier ) fam-ly ly-tier ;
: fam-units ( fam -- n ) dup fam-pos @ swap fam-ly ly-units ;
: fam-length ( fam -- u ) dup fam-pos @ swap fam-ly ly-tf @ tf-length ;
: fam@ ( k fam -- u ) fam-block @ ly@ ;
\ Record j of the family, a unit of its section's size.
: fam-rec ( j fam -- addr ) tuck fam-pos @ tier-unit * swap fam-block @ + ;
: fam-free ( fam -- ) dup fam-block heap-release fam-map heap-release ;
: ly-free ( ly -- ) tier-sections# 0 do i over ly-fam fam-free loop drop ;
\ Start: the tier file whose sections were checked (tf-start), the stage,
\ the base's counts of sections 1-8 (8 cells).
: fam-init ( i ly -- ) 2dup ly-fam tuck fam-layer ! fam-pos ! ;
: ly-fams-init ( ly -- ) tier-sections# 0 do i over fam-init loop drop ;
: ly-firsts! ( firsts ly -- )
  lp-lines 1 do over i 1- cells + @ i 2 pick ly-fam fam-first ! loop 2drop ;
: ly-init ( tf stage firsts ly -- )
  dup /layer erase dup ly-fams-init tuck ly-firsts! tuck ly-stage ! ly-tf ! ;
\ A family's failure names its section and the record (at); ok passes.
: ly-blame ( at outcome fam -- outcome )
  over ok? if drop nip exit then
  rot over fam-ly ly-where ! dup fam-pos @ tier-title swap fam-ly ly-why ! ;
\ A failure that drops two values and gives no result.
: ly-none2 ( x1 x2 outcome -- -1 outcome ) nip nip no-result ;

\ ---- The sections, read whole, 32-bit fields made the host's.
: fam-alloc ( fam -- addr outcome )
  dup fam-length 1 max allocate if 2drop 0 outcome-full exit then
  tuck swap fam-block ! outcome-ok ;
: ly-field? ( i -- flag ) dup lp-name-bytes <> swap lp-text-bytes <> and ;
: fam-pack ( fam -- ) dup fam-block @ swap fam-length 1 u32s / le-packed ;
: fam-load ( addr fam -- outcome ) dup fam-pos @ swap fam-ly ly-tf @ tf-read ;
: fam-read ( fam -- outcome )
  dup fam-alloc ok-then? 0= if nip exit then over fam-load ok-then? 0= if exit then
  dup fam-pos @ ly-field? if fam-pack else drop then outcome-ok ;
\ The maps: per own record of each family, zeroed.
: ly-zeros ( n addr -- outcome )
  swap u32s 1 max dup allocate if 2drop drop outcome-full exit then
  dup rot erase swap ! outcome-ok ;
: fam-section ( fam -- outcome )
  dup fam-read ok-then? 0= if exit then dup fam-units swap fam-map ly-zeros ;
: ly-sections ( ly -- outcome )
  tier-sections# 1 do
    i over ly-fam fam-section dup ok? 0= if nip unloop exit then drop
  loop drop outcome-ok ;

\ ---- Numbers here. A family's number n: the base's below its count;
\ from it on, the own record's, entered before (ok); else 0 and invalid.
\ Every translation word, and every xt this file passes one (u ly -- u'
\ outcome), gives an outcome.
: fam-own ( n fam -- idx true | false )
  2dup fam-first @ u< if 2drop false exit then
  tuck fam-first @ - swap fam-units over u> if true else drop false then ;
: fam-xlate ( n fam -- n' outcome )
  2dup fam-first @ u< if drop outcome-ok exit then
  tuck fam-own 0= if drop 0 outcome-invalid exit then
  swap fam-map @ ly@ dup if 1- outcome-ok else outcome-invalid then ;
: fam-kept ( n' idx fam -- ) fam-map @ swap u32s + swap 1+ swap u32! ;
\ A record built again must be a new record of the tier, or one an
\ earlier layer made (sibling layers share them); never the base's (a
\ layer holds only what its run added) nor this layer's own given twice
\ (review rvSN4 m1): the numbers of its new records rise.
: fam-count ( fam -- n ) dup fam-pos @ swap fam-ly ly-stage @ tier-slab slab-count ;
: fam-begin ( fam -- ) dup fam-count 2dup swap fam-begun ! 1- swap fam-top ! ;
: fam-fresh? ( n' fam -- flag )
  2dup fam-first @ u< if 2drop false exit then
  2dup fam-begun @ u< if 2drop true exit then
  2dup fam-top @ > if fam-top ! true else 2drop false then ;
: fam-keep ( n' idx fam -- outcome )
  2 pick over fam-fresh? 0= if 2drop drop outcome-invalid exit then fam-kept outcome-ok ;
: ly-name ( n ly -- n' outcome ) lp-names swap ly-fam fam-xlate ;
: ly-level ( n ly -- n' outcome ) lp-levels swap ly-fam fam-xlate ;
: ly-e ( n ly -- n' outcome ) lp-exprs swap ly-fam fam-xlate ;
: ly-number ( u ly -- u outcome ) drop outcome-ok ;
\ Bytes of a pool (names' or texts'): the layer's own, inside the pool.
: fam-bytes ( offset len fam -- c-addr u flag )
  >r over r@ fam-first @ u< if r> drop 2drop 0 0 false exit then
  swap r@ fam-first @ - swap 2dup + r@ fam-length u>
  if r> drop 2drop 0 0 false exit then
  swap r> fam-block @ + swap true ;
: ly-head ( addr -- tag payload ) quad-head u32@ dup head-tag swap head-payload ;

\ ---- Names, levels and texts.
\ A string name's bytes: (offset, length) are its b field and payload.
: ly-name-span ( addr -- offset len ) dup quad-b u32@ swap quad-head u32@ head-payload ;
: ly-str-name ( prefix addr ly -- n outcome )
  >r ly-name-span lp-name-bytes r@ ly-fam fam-bytes
  0= if 2drop drop r> drop -1 outcome-invalid exit then r> ly-tier name-str ;
: ly-num-name ( prefix addr ly -- n outcome ) ly-tier swap quad-b u32@ swap name-num ;
: ly-name-of ( addr ly -- n outcome )
  2dup swap quad-a u32@ swap ly-name ok-then? 0= if ly-none2 exit then
  -rot over ly-head drop case
    tag-name-str of ly-str-name endof  tag-name-num of ly-num-name endof
    2drop 2drop -1 outcome-invalid 0 endcase ;
\ A level's head, its parameter's name (the payload) made this tier's.
: ly-level-head ( addr ly -- head outcome )
  >r ly-head over tag-level-param = if r> ly-name else r> drop outcome-ok then
  >r pack-head r> ;
\ A child of a level, unless it is a parameter's (whose fields are 0).
: ly-level-part ( u tag ly -- u' outcome )
  over tag-level-param = if 2drop outcome-ok else nip ly-level then ;
\ A child of the level at addr, its field xt ( addr -- field ) (quad-a or
\ quad-b), made this tier's; both of them.
: ly-child ( addr xt ly -- u' outcome )
  >r over swap execute u32@ swap ly-head drop r> ly-level-part ;
: ly-level-parts ( addr ly -- a' b' outcome )
  2dup ['] quad-a swap ly-child >r -rot ['] quad-b swap ly-child r> swap outcome-and ;
: ly-level-of ( addr ly -- l outcome )
  2dup ly-level-head ok-then? 0= if ly-none2 exit then -rot
  dup >r ly-level-parts ok-then? 0= if r> drop ly-none2 exit then
  r> ly-tier level-build ;
\ A text record is (offset, length) into the text bytes.
: ly-text-of ( addr ly -- t outcome )
  >r dup u32@ swap 1 u32s + u32@ lp-text-bytes r@ ly-fam fam-bytes
  0= if 2drop r> drop -1 outcome-invalid exit then r> ly-tier tier-texts text-intern ;
\ The record at addr built again by its family's builder.
: fam-build ( addr fam -- n outcome )
  dup fam-ly swap fam-pos @ case
    lp-names of ly-name-of endof  lp-levels of ly-level-of endof
    lp-texts of ly-text-of endof  2drop drop -1 outcome-invalid 0 endcase ;
\ Own record j of names, levels or texts built again and kept.
: fam-step ( j fam -- outcome )
  2dup fam-rec over fam-build ok-then? 0= if nip nip exit then -rot fam-keep ;
\ Every own record in order: the first that fails, and its outcome.
: fam-each ( fam -- at outcome )
  dup fam-units 0 ?do
    i over fam-step dup ok? 0= if nip i swap unloop exit then drop
  loop drop 0 outcome-ok ;
: fam-enter ( fam -- outcome ) dup fam-begin dup fam-each rot ly-blame ;
: ly-family ( i ly -- outcome ) ly-fam fam-enter ;

\ ---- Lists: where each starts (a length, then that many items, inside
\ the section), then built again for the kind its user says.
: fam-start! ( idx fam -- ) fam-map @ 1 -rot ly! ;
\ Each list's start marked; where the last one ends.
: fam-starts ( fam -- fam end )
  0 begin 2dup swap fam-units u< while
    2dup swap fam-start! 2dup swap fam@ 1+ +
  repeat ;
: ly-starts ( ly -- outcome ) ly-lists fam-starts swap fam-units = flag>outcome ;
\ List t of the layer: the address of its first item and its length, when
\ t starts one.
: fam-list ( t fam -- a n true | false )
  tuck fam-own 0= if drop false exit then
  2dup swap fam-map @ ly@ 0= if 2drop false exit then
  swap fam-block @ swap u32s + dup u32@ swap 1 u32s + swap true ;
: ly-list ( t ly -- a n true | false ) ly-lists fam-list ;
: ly-base-list? ( t ly -- flag ) ly-lists fam-first @ u< ;
\ Item k of the n items at a, or 0 false past their end.
: items-at ( k a n -- u flag ) rot tuck u> if u32s + u32@ true else 2drop 0 false then ;
: fam-tuples ( fam -- cons ) fam-tier tier-tuples ;
\ The item at a (or the n items from a), a number of family fam made
\ this tier's, added to the tuple begun; then a tuple filled so, or a
\ failure, ended.
: fam-add ( a fam -- outcome )
  tuck swap u32@ swap fam-xlate ok-then? 0= if nip exit then swap fam-tuples tuple-add ;
: fam-adds ( a n fam -- outcome )
  swap 0 ?do
    2dup fam-add dup ok? 0= if nip nip unloop exit then drop swap 1 u32s + swap
  loop 2drop outcome-ok ;
: fam-fill ( a n fam -- outcome )
  dup fam-tuples tuple-start ok-then3? 0= if exit then fam-adds ;
: ly-tuple-end ( outcome ly -- t' outcome )
  swap dup ok? 0= if nip no-result exit then drop ly-tier tier-tuples tuple-end ;
\ List t: the base's as it is; the layer's built again for family fam.
: fam-tuple ( t fam -- t' outcome )
  2dup fam-ly ly-base-list? if drop outcome-ok exit then
  swap over fam-ly ly-list 0= if drop -1 outcome-invalid exit then
  rot dup >r fam-fill r> fam-ly ly-tuple-end ;
: ly-levels ( t ly -- t' outcome ) lp-levels swap ly-fam fam-tuple ;
: ly-names ( t ly -- t' outcome ) lp-names swap ly-fam fam-tuple ;

\ ---- Expressions (a letE spans two numbers).
\ Operands a and b both expressions; or a alone of family fam.
: ly-two ( a b ly -- a' b' outcome )
  lp-exprs swap ly-fam tuck fam-xlate 2swap fam-xlate 2swap rot swap outcome-and ;
: fam-a ( a b fam -- a' b' outcome ) rot swap fam-xlate rot swap ;
: ly-a-level ( a b ly -- a' b' outcome ) lp-levels swap ly-fam fam-a ;
: ly-a-expr ( a b ly -- a' b' outcome ) lp-exprs swap ly-fam fam-a ;
: ly-a-text ( a b ly -- a' b' outcome ) lp-texts swap ly-fam fam-a ;
\ A constant's levels (a list built again: full when the heap or the
\ stage's limit refuses) and name; the levels' outcome first.
: ly-const ( a b ly -- a' b' outcome )
  tuck ly-levels 2swap ly-name 2swap rot outcome-and ;
: ly-ab ( a b tag ly -- a' b' outcome )
  swap case
    tag-bvar of drop outcome-ok endof  tag-sort of ly-a-level endof
    tag-const of ly-const endof  tag-app of ly-two endof
    tag-proj of ly-a-expr endof  tag-nat of ly-a-text endof  tag-str of ly-a-text endof
    tag-mdata of ly-a-expr endof
    binder-tag? if ly-two else drop outcome-invalid then 0 endcase ;
\ The payload: a binder's, a letE's or a projection's name; else 0.
: ly-named? ( tag -- flag ) dup binder-tag? over let-tag? or swap tag-proj = or ;
: ly-payload ( tag payload ly -- tag payload' outcome )
  2 pick ly-named? if ly-name else drop dup 0= flag>outcome then ;
\ Record j's head, its payload made this tier's.
: fam-head ( j fam -- head outcome )
  tuck fam-rec ly-head rot fam-ly ly-payload >r pack-head r> ;
\ Record j + 1: a letE's body record; the body.
: fam-body ( j fam -- body' outcome )
  swap 1+ 2dup swap fam-units u< 0= if 2drop 0 outcome-invalid exit then
  over fam-rec dup ly-head drop tag-let-body <> if 2drop 0 outcome-invalid exit then
  quad-a u32@ swap fam-xlate ;
: fam-operands ( j fam -- a b ) fam-rec dup quad-a u32@ swap quad-b u32@ ;
: fam-two ( a b fam -- a' b' outcome ) fam-ly ly-two ;
\ A letE (head, at record j): its body, then its type and value.
: fam-let ( head j fam -- e outcome )
  dup >r 2dup fam-body ok-then? 0= if r> drop nip nip nip no-result exit then
  -rot fam-operands r@ fam-two ok-then? 0= if r> drop nip nip nip no-result exit then
  rot r> fam-tier expr-let ;
\ The record at addr's operands made this tier's, as its tag says.
: ly-operands ( addr ly -- a' b' outcome )
  >r dup quad-a u32@ over quad-b u32@ rot ly-head drop r> ly-ab ;
: fam-plain ( head addr fam -- e outcome )
  dup >r fam-ly ly-operands ok-then? 0= if r> drop ly-none2 exit then
  r> fam-tier expr-make ;
: fam-expr-of ( j fam -- e outcome )
  2dup fam-head ok-then? 0= if nip nip no-result exit then
  dup head-tag let-tag? if -rot fam-let exit then -rot tuck fam-rec swap fam-plain ;
: fam-mdata ( j fam -- )
  tuck fam-rec ly-head drop tag-mdata =
  if fam-ly ly-stage @ 1 swap stage-mdata +! else drop then ;
: fam-span ( j fam -- n ) fam-rec ly-head drop let-tag? if 2 else 1 then ;
: fam-expr-step ( j fam -- j' outcome )
  2dup fam-expr-of ok-then? 0= if nip nip -1 swap exit then
  -rot 2dup fam-mdata 2dup fam-span 2 pick + >r fam-keep r> swap ;
: fam-exprs ( fam -- outcome )
  dup fam-begin 0 begin 2dup swap fam-units u< while
    2dup swap fam-expr-step ok-then? 0= if rot ly-blame exit then nip
  repeat 2drop outcome-ok ;
: ly-exprs ( ly -- outcome ) lp-exprs swap ly-fam fam-exprs ;

\ ---- Every family in order.
: ly-starts-noted ( ly -- outcome ) dup ly-starts 0 swap rot ly-lists ly-blame ;
: ly-records ( ly -- outcome )
  lp-names over ly-family ok-then? 0= if exit then
  lp-levels over ly-family ok-then? 0= if exit then
  lp-texts over ly-family ok-then? 0= if exit then
  dup ly-starts-noted ok-then? 0= if exit then ly-exprs ;

\ ---- Declarations: each translated in place, its chain cleared.
: ly-decls# ( ly -- n ) lp-decls swap ly-units ;
: ly-decl ( i ly -- addr ) lp-decls swap ly-fam fam-rec ;
: ly-line ( i ly -- u ) lp-lines swap ly-fam fam@ ;
: ly-kind ( addr -- kind ) staged-head u32@ head-tag ;
\ A field: none stays none; else through xt ( u ly -- u' outcome ).
: ly-field ( addr ly xt -- outcome )
  2 pick u32@ dup none? if 2drop 2drop outcome-ok exit then
  -rot execute ok-then? if swap u32! outcome-ok else nip then ;
\ Item k of list t: an own list's, or a tuple of the base's; 0 false past
\ its end.
: ly-base-at ( k t ly -- u flag )
  >r 2dup + 1+ r@ ly-base-list? 0= if 2drop r> drop 0 false exit then
  r> ly-tier tier-tuples 2dup tuple-length 3 pick u>
  if tuple-item true else 2drop drop 0 false then ;
: ly-at ( k t ly -- u flag ) 2dup ly-list if 2swap 2drop items-at exit then ly-base-at ;
\ A recursor's rules, [ctor nfields rhs] each, as a new tuple.
: ly-rule-item ( u k ly -- u' outcome )
  swap 3 mod case 0 of ly-name endof 1 of drop outcome-ok endof drop ly-e 0 endcase ;
: ly-rule-adds ( a n ly -- outcome )
  swap 0 ?do
    over i u32s + u32@ i 2 pick ly-rule-item ok-then? 0= if nip nip unloop exit then
    over ly-tier tier-tuples tuple-add dup ok? 0= if nip nip unloop exit then drop
  loop 2drop outcome-ok ;
: ly-rule-fill ( a n ly -- outcome )
  dup ly-tier tier-tuples tuple-start ok-then3? 0= if exit then ly-rule-adds ;
: ly-rules ( t ly -- t' outcome )
  2dup ly-base-list? if drop outcome-ok exit then
  tuck ly-list 0= if drop 0 outcome-invalid exit then
  dup /rule-items mod if 2drop drop 0 outcome-invalid exit then
  rot dup >r ly-rule-fill r> ly-tuple-end ;
\ Kind data: the items of t, each through its xt in table (a count, then
\ the xts), as a new tuple of the stage's items (import/stage-records.fs).
: ly-more ( t table ly -- t' outcome )
  dup ly-stage @ items-clear over @ 0 ?do
    i 3 pick 2 pick ly-at 0= if 2drop 2drop 0 outcome-invalid unloop exit then
    over 3 pick i 1+ cells + @ execute ok-then? 0= if nip ly-none2 unloop exit then
    over ly-stage @ item,
  loop nip nip ly-stage @ items>tuple ;
create ly-block-data 3 , ' ly-number , ' ly-number , ' ly-number ,
create ly-type-data
  5 , ' ly-number , ' ly-number , ' ly-names , ' ly-names , ' ly-number ,
create ly-ctor-data 4 , ' ly-name , ' ly-number , ' ly-number , ' ly-number ,
create ly-rec-data
  6 , ' ly-names , ' ly-number , ' ly-number , ' ly-number , ' ly-number , ' ly-rules ,
\ The table of a kind's data; 0 for a kind with none, or with its
\ parameter names only (a definition, theorem or opaque declaration).
: ly-table ( kind -- table|0 )
  case kind-inductive of ly-block-data endof  kind-type of ly-type-data endof
    kind-ctor of ly-ctor-data endof  kind-recursor of ly-rec-data endof  0 swap endcase ;
: ly-names-kind? ( kind -- flag )
  dup kind-def = over kind-thm = or swap kind-opaque = or ;
: ly-data ( t kind ly -- t' outcome )
  over ly-names-kind? if nip ly-names exit then
  swap ly-table ?dup if swap ly-more else drop outcome-invalid then ;
: ly-more-field ( addr ly -- outcome )
  over staged-more u32@ dup none? if drop 2drop outcome-ok exit then
  2 pick ly-kind rot ly-data ok-then? if swap staged-more u32! outcome-ok else nip then ;
\ Each field translated in place (all of them, as before), the first
\ failure the outcome.
: ly-xlate-decl ( addr ly -- outcome )
  over staged-name over ['] ly-name ly-field >r
  over staged-params over ['] ly-names ly-field r> swap outcome-and >r
  over staged-type over ['] ly-e ly-field r> swap outcome-and >r
  over staged-value over ['] ly-e ly-field r> swap outcome-and >r
  over 0 swap staged-prev u32! ly-more-field r> swap outcome-and ;
: fam-decls ( fam -- at outcome )
  dup fam-units 0 ?do
    i over fam-rec over fam-ly ly-xlate-decl dup ok? 0= if nip i swap unloop exit then
    drop
  loop drop 0 outcome-ok ;
: ly-decls ( ly -- outcome ) lp-decls swap ly-fam dup fam-decls rot ly-blame ;

\ Read a layer's sections and enter its records, then translate its
\ declarations (see the header): ok, invalid or full.
: ly-load ( ly -- outcome )
  dup ly-sections ok-then? 0= if exit then
  dup ly-records ok-then? 0= if exit then ly-decls ;
\ Enter translated declaration i into the stage, checked as the stage
\ checks a draft (import/snapshot-tier.fs decl-ok?, stage-records.fs
\ draft-close), linked to its name, with its line: ok, invalid or full.
: ly-room ( i ly stage -- outcome )
  1 over stage-decl-records slab-room ok-then? 0= if nip nip exit then
  >r ly-line r> stage-lines fields-push ;
: ly-enter ( i ly -- outcome )
  2dup dup ly-stage @ ly-room ok-then? 0= if nip exit then
  dup ly-stage @ >r ly-decl r@ draft /staged move
  r@ decl-ok? 0= if r> drop outcome-invalid exit then r> draft-close ;

base !   \ the BASE this file was loaded with

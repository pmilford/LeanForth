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
\ base's stand).
\
\ Outcomes (ADR 0008): ok; invalid for a malformed layer or a reference
\ that is not a record (ly-why names the section, ly-at the record); full
\ for no heap or the stage's memory limit. Records entered stay entered
\ after a failure: the caller frees the stage. State: one /layer record
\ per layer being entered, used by one task; ly-free frees its blocks.

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

begin-structure /layer
  field: ly-tf                            \ the layer's tier file (its sections)
  field: ly-stage                         \ the stage entered into
  tier-sections# cells +field ly-blocks   \ sections 1-9 read, by position
  8 cells +field ly-firsts                \ the base's counts of tier sections 1-8
  tier-sections# cells +field ly-maps     \ per own record: its number here + 1
  field: ly-why                           \ counted string: the section refused, or 0
  field: ly-where                         \ the record refused
  field: ly-begun                         \ the family being entered: its count before
  field: ly-top                           \ and the highest number this layer kept of it
end-structure
\ Positions of the sections.
1 constant lp-name-bytes  2 constant lp-names  3 constant lp-levels  4 constant lp-lists
5 constant lp-text-bytes  6 constant lp-texts  7 constant lp-exprs  8 constant lp-decls
9 constant lp-lines

: ly@ ( i addr -- u ) swap u32s + u32@ ;
: ly! ( u i addr -- ) swap u32s + u32! ;
: ly-block ( i ly -- addr ) ly-blocks swap cells + @ ;
: ly-units ( i ly -- n ) ly-tf @ tf-units ;
: ly-first ( i ly -- u ) ly-firsts swap 1- cells + @ ;
: ly-map ( i ly -- addr ) ly-maps swap cells + @ ;
: ly-tier ( ly -- tier ) ly-stage @ stage-tier ;
: ly-free ( ly -- )
  tier-sections# 0 do
    dup ly-blocks i cells + heap-release dup ly-maps i cells + heap-release
  loop drop ;
\ Start: the tier file whose sections were checked (tf-start), the stage,
\ the base's counts of sections 1-8 (8 cells).
: ly-init ( tf stage firsts ly -- )
  dup /layer erase >r r@ ly-firsts 8 cells move r@ ly-stage ! r> ly-tf ! ;
: ly-note ( outcome at i ly -- outcome )
  >r 2 pick ok? if 2drop r> drop exit then swap r@ ly-where ! tier-title r> ly-why ! ;

\ ---- The sections, read whole, 32-bit fields made the host's.
: ly-alloc ( i ly -- addr outcome )
  2dup ly-tf @ tf-length 1 max allocate if drop 2drop 0 outcome-full exit then
  dup >r -rot ly-blocks swap cells + ! r> outcome-ok ;
: ly-field? ( i -- flag ) dup lp-name-bytes <> swap lp-text-bytes <> and ;
: ly-pack ( addr i ly -- ) ly-tf @ tf-length 1 u32s / le-packed ;
: ly-read ( i ly -- outcome )
  2dup ly-alloc ok-then? 0= if nip nip exit then
  dup 3 pick 3 pick ly-tf @ tf-read dup ok? 0= if nip nip nip exit then drop
  2 pick ly-field? if -rot ly-pack else drop 2drop then outcome-ok ;
\ The maps: per own record of each family, zeroed.
: ly-zeros ( n addr -- outcome )
  >r u32s 1 max dup allocate if 2drop r> drop outcome-full exit then
  dup rot erase r> ! outcome-ok ;
: ly-section ( i ly -- outcome )
  2dup ly-read dup ok? 0= if nip nip exit then drop
  2dup ly-units -rot ly-maps swap cells + ly-zeros ;
: ly-sections ( ly -- outcome )
  tier-sections# 1 do i over ly-section dup ok? 0= if nip unloop exit then drop loop
  drop outcome-ok ;

\ ---- Numbers here. Family i's number n: the base's below its count;
\ from it on, the own record's, entered before; else 0 and false.
: ly-own ( n i ly -- idx true | false )
  >r 2dup r@ ly-first u< if 2drop r> drop false exit then
  tuck r@ ly-first - swap r> ly-units over u> if true else drop false then ;
: ly-xlate ( n i ly -- n' flag )
  >r 2dup r@ ly-first u< if drop r> drop true exit then
  2dup r@ ly-own 0= if 2drop r> drop 0 false exit then
  rot drop swap r> ly-map ly@ dup if 1- true else false then ;
: ly-kept ( n' idx i ly -- ) ly-map >r swap 1+ swap r> ly! ;
\ A record built again must be a new record of the tier, or one an
\ earlier layer made (sibling layers share them); never the base's (a
\ layer holds only what its run added) nor this layer's own given twice
\ (review rvSN4 m1): the numbers of its new records rise.
: ly-count ( i ly -- n ) ly-stage @ tier-slab slab-count ;
: ly-begin ( i ly -- ) tuck ly-count dup 2 pick ly-begun ! 1- swap ly-top ! ;
: ly-fresh? ( n' i ly -- flag )
  >r over swap r@ ly-first u< if drop r> drop false exit then
  dup r@ ly-begun @ u< if drop r> drop true exit then
  dup r@ ly-top @ > if r> ly-top ! true else drop r> drop false then ;
: ly-keep ( n' idx i ly -- outcome )
  3 pick 2 pick 2 pick ly-fresh? 0= if 2drop 2drop outcome-invalid exit then
  ly-kept outcome-ok ;
: ly-name ( n ly -- n' flag ) lp-names swap ly-xlate ;
: ly-level ( n ly -- n' flag ) lp-levels swap ly-xlate ;
: ly-text ( n ly -- n' flag ) lp-texts swap ly-xlate ;
: ly-e ( n ly -- n' flag ) lp-exprs swap ly-xlate ;
: ly-number ( u ly -- u flag ) drop true ;
\ Bytes of pool i (names' or texts'): the layer's own, inside the pool.
: ly-bytes ( offset len i ly -- c-addr u flag )
  2>r over 2r@ ly-first u< if 2r> 2drop 2drop 0 0 false exit then
  swap 2r@ ly-first - swap 2dup + 2r@ ly-tf @ tf-length u>
  if 2r> 2drop 2drop 0 0 false exit then
  swap 2r> ly-block + swap true ;
: ly-rec ( j i ly -- addr ) ly-block swap /quad * + ;
: ly-head ( addr -- tag payload ) quad-head u32@ dup head-tag swap head-payload ;

\ ---- Names, levels and texts.
: ly-str-name ( prefix addr ly -- n outcome )
  >r dup quad-b u32@ swap quad-head u32@ head-payload lp-name-bytes r@ ly-bytes
  0= if 2drop drop r> drop -1 outcome-invalid exit then r> ly-tier name-str ;
: ly-num-name ( prefix addr ly -- n outcome ) >r quad-b u32@ r> ly-tier name-num ;
: ly-name-of ( addr ly -- n outcome )
  2dup >r quad-a u32@ r> ly-name 0= if drop 2drop -1 outcome-invalid exit then
  -rot over ly-head drop case
    tag-name-str of ly-str-name endof  tag-name-num of ly-num-name endof
    >r drop 2drop -1 outcome-invalid r> endcase ;
\ A level's head, its parameter's name (the payload) made this tier's.
: ly-level-head ( addr ly -- head flag )
  >r ly-head over tag-level-param = if r@ ly-name else true then r> drop >r pack-head r> ;
\ A child of a level, unless it is a parameter's (whose fields are 0).
: ly-level-part ( u tag ly -- u' flag )
  over tag-level-param = if 2drop true else nip ly-level then ;
\ A child of the level at addr, its field xt ( addr -- field ) (quad-a or
\ quad-b), made this tier's; both of them.
: ly-child ( addr xt ly -- u' flag )
  >r over swap execute u32@ swap ly-head drop r> ly-level-part ;
: ly-level-parts ( addr ly -- a' b' flag )
  2dup ['] quad-a swap ly-child >r -rot ['] quad-b swap ly-child r> and ;
: ly-level-of ( addr ly -- l outcome )
  2dup ly-level-head 0= if drop 2drop -1 outcome-invalid exit then -rot
  dup >r ly-level-parts 0= if r> drop 2drop drop -1 outcome-invalid exit then
  r> ly-tier level-build ;
\ A text record is (offset, length) into the text bytes.
: ly-text-of ( addr ly -- t outcome )
  >r dup u32@ swap 1 u32s + u32@ lp-text-bytes r@ ly-bytes
  0= if 2drop r> drop -1 outcome-invalid exit then r> ly-tier tier-texts text-intern ;

\ ---- Lists: where each starts (a length, then that many items, inside
\ the section), then built again for the kind its user says.
: ly-start! ( idx ly -- ) lp-lists swap ly-map 1 -rot ly! ;
: ly-starts ( ly -- outcome )
  0 begin dup lp-lists 3 pick ly-units u< while
    2dup swap ly-start! dup lp-lists 3 pick ly-block ly@ 1+ +
  repeat lp-lists rot ly-units = if outcome-ok else outcome-invalid then ;
\ List t of the layer: its own index and length, when t starts one.
: ly-list ( t ly -- idx n true | false )
  2dup lp-lists swap ly-own 0= if 2drop false exit then rot drop swap
  2dup lp-lists swap ly-map ly@ 0= if 2drop false exit then
  over swap lp-lists swap ly-block ly@ true ;
: ly-item ( k idx ly -- u ) lp-lists swap ly-block -rot + 1+ swap ly@ ;
\ Every item of own list idx through xt ( u ly -- u' flag ), as a new tuple.
: ly-items ( idx n xt ly -- outcome )
  dup ly-tier tier-tuples tuple-start dup ok? 0= if nip nip nip nip exit then drop
  rot 0 ?do
    i 3 pick 2 pick ly-item over 3 pick execute 0= if 2drop 2drop outcome-invalid unloop
      exit then
    over ly-tier tier-tuples tuple-add dup ok? 0= if nip nip nip unloop exit then drop
  loop 2drop drop outcome-ok ;
\ List t: the base's as it is; the layer's built again through xt.
: ly-tuple ( t xt ly -- t' outcome )
  >r over lp-lists r@ ly-first u< if drop r> drop outcome-ok exit then
  swap r@ ly-list 0= if drop r> drop -1 outcome-invalid exit then
  rot r@ ly-items dup ok? 0= if r> drop no-result exit then drop
  r> ly-tier tier-tuples tuple-end ;
: ly-levels ( t ly -- t' outcome ) ['] ly-level swap ly-tuple ;
: ly-names ( t ly -- t' outcome ) ['] ly-name swap ly-tuple ;
: ly-tnames ( t ly -- t' flag ) ly-names ok? ;

\ ---- Expressions (a letE spans two numbers).
: ly-two ( a b ly -- a' b' flag ) tuck ly-e >r -rot ly-e r> and -rot swap rot ;
: ly-a-level ( a b ly -- a' b' flag ) >r swap r> ly-level rot swap ;
: ly-a-expr ( a b ly -- a' b' flag ) >r swap r> ly-e rot swap ;
: ly-a-text ( a b ly -- a' b' flag ) >r swap r> ly-text rot swap ;
: ly-const ( a b ly -- a' b' flag ) tuck ly-levels ok? >r -rot ly-name r> and rot swap ;
: ly-ab ( a b tag ly -- a' b' flag )
  swap case
    tag-bvar of drop true endof  tag-sort of ly-a-level endof
    tag-const of ly-const endof  tag-app of ly-two endof
    tag-proj of ly-a-expr endof  tag-nat of ly-a-text endof  tag-str of ly-a-text endof
    tag-mdata of ly-a-expr endof
    >r r@ binder-tag? if ly-two else drop false then r> endcase ;
\ The payload: a binder's, a letE's or a projection's name; else 0.
: ly-payload ( payload tag ly -- payload' flag )
  over binder-tag? 2 pick let-tag? or 2 pick tag-proj = or
  if nip ly-name else 2drop dup 0= then ;
\ Record j + 1: a letE's body record; the body.
: ly-body ( j ly -- body' flag )
  >r 1+ dup lp-exprs r@ ly-units u< 0= if drop r> drop 0 false exit then
  lp-exprs r@ ly-rec dup ly-head drop tag-let-body <> if drop r> drop 0 false exit then
  quad-a u32@ r> ly-e ;
: ly-let ( head addr j ly -- e outcome )
  tuck ly-body 0= if 2drop 2drop -1 outcome-invalid exit then >r >r
  dup quad-a u32@ swap quad-b u32@ r@ ly-two
  0= if 2drop drop r> r> 2drop -1 outcome-invalid exit then
  r> r> swap ly-tier expr-let ;
\ The record at addr's operands made this tier's, as its tag says.
: ly-operands ( addr ly -- a' b' flag )
  >r dup quad-a u32@ over quad-b u32@ rot ly-head drop r> ly-ab ;
: ly-plain ( j ly addr head -- e outcome )
  >r over ly-operands 0= if r> drop 2drop 2drop -1 outcome-invalid exit then
  r> -rot 3 roll ly-tier expr-make rot drop ;
: ly-expr-of ( j ly -- e outcome )
  2dup lp-exprs swap ly-rec dup ly-head over 4 pick ly-payload
  0= if 2drop 2drop drop -1 outcome-invalid exit then
  over swap pack-head swap let-tag? if 2swap >r >r swap r> r> ly-let exit then ly-plain ;
: ly-mdata ( j ly -- )
  tuck lp-exprs swap ly-rec ly-head drop tag-mdata =
  if 1 swap ly-stage @ stage-mdata +! else drop then ;
: ly-span ( j ly -- n ) lp-exprs swap ly-rec ly-head drop let-tag? if 2 else 1 then ;
: ly-expr-step ( j ly -- j' outcome )
  2dup ly-expr-of dup ok? 0= if nip nip nip -1 swap exit then drop
  -rot 2dup ly-mdata 2dup 2>r lp-exprs swap ly-keep 2r> over swap ly-span + swap ;
: ly-exprs ( ly -- outcome )
  lp-exprs over ly-begin
  0 begin dup lp-exprs 3 pick ly-units u< while
    dup 2 pick ly-expr-step dup ok? 0= if nip -rot swap lp-exprs swap ly-note exit then
    drop nip
  repeat 2drop outcome-ok ;

\ ---- Every family in order.
: ly-each ( i xt ly -- at outcome )
  rot over ly-units 0 ?do
    i over 3 pick execute dup ok? 0= if nip nip i swap unloop exit then drop
  loop 2drop 0 outcome-ok ;
: ly-family ( i xt ly -- outcome )
  2 pick over ly-begin 2 pick >r dup >r ly-each swap r> r> swap ly-note ;
: ly-name-step ( j ly -- outcome )
  2dup lp-names swap ly-rec over ly-name-of dup ok? 0= if nip nip nip exit then drop
  -rot lp-names swap ly-keep ;
: ly-level-step ( j ly -- outcome )
  2dup lp-levels swap ly-rec over ly-level-of dup ok? 0= if nip nip nip exit then drop
  -rot lp-levels swap ly-keep ;
: ly-text-at ( j ly -- addr ) lp-texts swap ly-block swap 2 u32s * + ;
: ly-text-step ( j ly -- outcome )
  2dup ly-text-at over ly-text-of dup ok? 0= if nip nip nip exit then drop
  -rot lp-texts swap ly-keep ;
: ly-records ( ly -- outcome )
  lp-names ['] ly-name-step 2 pick ly-family dup ok? 0= if nip exit then drop
  lp-levels ['] ly-level-step 2 pick ly-family dup ok? 0= if nip exit then drop
  lp-texts ['] ly-text-step 2 pick ly-family dup ok? 0= if nip exit then drop
  dup ly-starts dup ok? 0= if 0 lp-lists 3 roll ly-note exit then drop ly-exprs ;

\ ---- Declarations: each translated in place, its chain cleared.
: ly-decls# ( ly -- n ) lp-decls swap ly-units ;
: ly-decl ( i ly -- addr ) lp-decls swap ly-block swap /staged * + ;
: ly-line ( i ly -- u ) lp-lines swap ly-block ly@ ;
: ly-kind ( addr -- kind ) staged-head u32@ head-tag ;
\ A field: none stays none; else through xt ( u ly -- u' flag ).
: ly-field ( addr xt ly -- flag )
  2 pick u32@ dup none? if drop 2drop drop true exit then
  -rot swap execute dup if drop swap u32! true else nip nip then ;
\ Item k of list t: an own list's, or a tuple of the base's; 0 false past
\ its end.
: ly-own-at ( k idx n ly -- u flag )
  >r rot tuck u> if swap r> ly-item true else 2drop r> drop 0 false then ;
: ly-base-at ( k t ly -- u flag )
  >r 2dup + 1+ lp-lists r@ ly-first u< 0= if 2drop r> drop 0 false exit then
  r> ly-tier tier-tuples 2dup tuple-length 3 pick u>
  if tuple-item true else 2drop drop 0 false then ;
: ly-at ( k t ly -- u flag )
  2dup ly-list if rot >r rot drop r> ly-own-at exit then ly-base-at ;
\ A recursor's rules, [ctor nfields rhs] each, as a new tuple.
: ly-rule-item ( u k ly -- u' flag )
  swap 3 mod case 0 of ly-name endof 1 of drop true endof >r ly-e r> endcase ;
: ly-rules ( t ly -- t' flag )
  over lp-lists 2 pick ly-first u< if drop true exit then
  tuck ly-list 0= if drop 0 false exit then
  dup /rule-items mod if 2drop drop 0 false exit then
  2 pick ly-tier tier-tuples tuple-start ok? 0= if 2drop drop 0 false exit then
  0 ?do
    i over 3 pick ly-item i 3 pick ly-rule-item 0= if 2drop drop 0 false unloop exit then
    2 pick ly-tier tier-tuples tuple-add ok? 0= if 2drop 0 false unloop exit then
  loop drop ly-tier tier-tuples tuple-end ok? ;
\ Kind data: n items of t, each through its xt in table, as a new tuple
\ of the stage's items (import/stage-records.fs).
: ly-more ( t table n ly -- t' flag )
  dup ly-stage @ items-clear swap 0 ?do
    i 3 pick 2 pick ly-at 0= if 2drop 2drop 0 false unloop exit then
    over 3 pick i cells + @ execute 0= if 2drop 2drop 0 false unloop exit then
    over ly-stage @ item,
  loop nip nip ly-stage @ items>tuple ok? ;
create ly-block-data ' ly-number , ' ly-number , ' ly-number ,
create ly-type-data ' ly-number , ' ly-number , ' ly-tnames , ' ly-tnames , ' ly-number ,
create ly-ctor-data ' ly-name , ' ly-number , ' ly-number , ' ly-number ,
create ly-rec-data
  ' ly-tnames , ' ly-number , ' ly-number , ' ly-number , ' ly-number , ' ly-rules ,
: ly-data ( t kind ly -- t' flag )
  swap case
    kind-def of ly-tnames endof  kind-thm of ly-tnames endof
    kind-opaque of ly-tnames endof
    kind-inductive of ly-block-data 3 rot ly-more endof
    kind-type of ly-type-data 5 rot ly-more endof
    kind-ctor of ly-ctor-data 4 rot ly-more endof
    kind-recursor of ly-rec-data 6 rot ly-more endof
    >r drop false r> endcase ;
: ly-more-field ( addr ly -- flag )
  over staged-more u32@ dup none? if drop 2drop true exit then
  2 pick ly-kind rot ly-data dup if drop swap staged-more u32! true else nip nip then ;
: ly-xlate-decl ( addr ly -- flag )
  over staged-name ['] ly-name 2 pick ly-field >r
  over staged-params ['] ly-tnames 2 pick ly-field r> and >r
  over staged-type ['] ly-e 2 pick ly-field r> and >r
  over staged-value ['] ly-e 2 pick ly-field r> and >r
  over 0 swap staged-prev u32! ly-more-field r> and ;
: ly-decls ( ly -- outcome )
  dup ly-decls# 0 ?do
    i over ly-decl over ly-xlate-decl 0= if
      outcome-invalid i lp-decls 3 pick ly-note nip unloop exit then
  loop drop outcome-ok ;

\ Read a layer's sections and enter its records, then translate its
\ declarations (see the header): ok, invalid or full.
: ly-load ( ly -- outcome )
  dup ly-sections dup ok? 0= if nip exit then drop
  dup ly-records dup ok? 0= if nip exit then drop ly-decls ;
\ Enter translated declaration i into the stage, checked as the stage
\ checks a draft (import/snapshot-tier.fs decl-ok?, stage-records.fs
\ draft-close), linked to its name, with its line: ok, invalid or full.
: ly-enter ( i ly -- outcome )
  dup ly-stage @ >r 1 r@ stage-decl-records slab-room
  dup ok? 0= if nip nip r> drop exit then
  drop 2dup ly-line r@ stage-lines fields-push dup ok? 0= if nip nip r> drop exit then
  drop ly-decl r@ draft /staged move r@ decl-ok? 0= if r> drop outcome-invalid exit then
  r> draft-close ;

base !   \ the BASE this file was loaded with

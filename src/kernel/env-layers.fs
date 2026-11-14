\ Layered snapshots loaded on a base (ADR 0020 amendment 1, F5; plan task
\ 6.2.5, step SN4). [kernel][format] code: not through the review gate
\ (AGENTS.md); LeanForth-specific.
\
\ After a base's tier is read into a stage and its environment's sections
\ read into the base record (env-snapshot.fs snap-tier, snap-read), each
\ layer given is loaded on it in order (lay-load): opened as a layer of
\ that base (snap-layer-open: header fields 7-15 name the base's identity,
\ the first numbers are the base's counts), its records entered into the
\ stage (import/snapshot-layer.fs), its environment's sections read and
\ checked as a base's are (its slots numbered on from the base's), and
\ then merged into the base record. Each of its declarations, an
\ inductive block whole, is
\ - the same declaration as one loaded before (the same content as
\   numbers of the one tier, and the same outcome, axiom set, warnings,
\   recipe, shape, fuel and lookups): not entered again, and what refers
\   to it refers to the one loaded (two layers written on one base share
\   what their exports share); with other lookups, when an import pass
\   follows (lay-twins, which the caller sets after lay-init; review rvSS
\   1), it is entered as below, beside the loaded one;
\ - of a name loaded before but of none's content: refused (invalid), as
\   Lean refuses an import that declares a name twice;
\ - else entered into the stage after the declarations loaded, its chain
\   set, its slot appended to the base record with its dependencies and
\   lookups (names and slots numbered as loaded, each list sorted again)
\   and its site.
\ The loaded snapshots then read as one -- the base, then the layers in
\ order, every number one of the one tier and slot numbering -- as
\ cli/check-run.fs and the import pass (env-import.fs) read a base. What
\ each file vouches for is ADR 0020 D4's.
\
\ Outcomes (ADR 0008): ok; invalid for a layer not written on this base
\ (or not a layer), malformed or damaged, or a clash (lay-error: what, and
\ the layer's record or slot); unsupported for another format or verdict
\ version; full for no heap. State: one /lay record per layer being
\ loaded, used by one task; lay-free frees its blocks.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/u32.fs
require ../lib/bytes.fs
require ../import/stage.fs
require ../import/snapshot-tier.fs
require ../import/snapshot-layer.fs
require ./env-snapshot.fs
require ./env-import.fs

begin-structure /lay
  /snap +field lay-snap        \ the layer's file and sections
  /layer +field lay-ly         \ its tier, entered
  field: lay-base              \ the base record it is merged into
  field: lay-stage             \ the stage
  field: lay-sn                \ the base's own slots: the layer's start there
  field: lay-names             \ the base's names
  field: lay-firsts            \ the base's tier counts (8 cells)
  field: lay-n                 \ the layer's slots
  field: lay-map               \ per layer slot: its slot as loaded
  field: lay-new               \ per layer slot: 1 when appended
  field: lay-slots             \ per declaration loaded before: its slot + 1
  field: lay-old               \ declarations loaded before
  field: lay-cur               \ slots loaded so far
  field: lay-why               \ counted string: what was refused, or 0
  field: lay-at                \ the layer's record or slot refused
  field: lay-ui                \ the unit decided: its first record,
  field: lay-ud                \ its records,
  field: lay-uj                \ its first slot
  field: lay-us                \ and its slots
  field: lay-site0             \ the base's site texts before the layer's
  field: lay-at-j              \ appending: the layer's slot,
  field: lay-at-s              \ and its slot as loaded
  field: lay-twins             \ true: keep twins of other lookups (an import follows)
end-structure
: lay-free ( lay -- )
  dup lay-snap snap-close dup lay-snap snap-free dup lay-ly ly-free
  dup lay-map heap-release dup lay-new heap-release lay-slots heap-release ;
\ Start: the stage and base record, the base's slots, names and tier
\ counts (8 cells, valid while the layer loads).
: lay-init ( stage base sn names firsts lay -- )
  dup /lay erase dup lay-snap snap-init >r r@ lay-firsts ! r@ lay-names ! r@ lay-sn !
  r@ lay-base ! r> lay-stage ! ;
: lay-note ( outcome c-addr at lay -- outcome )
  dup lay-why @ if 2drop drop exit then tuck lay-at ! lay-why ! ;
: lay-error ( lay -- c-addr u at )
  dup lay-why @ ?dup if count rot lay-at @ exit then
  dup lay-snap snap-why @ if lay-snap snap-error exit then
  lay-ly dup ly-why @ counted-or-empty rot ly-where @ ;

\ ---- Opening, the tier, the environment's sections.
: lay-ly-start ( lay -- )
  dup lay-snap snap-tf over lay-stage @ 2 pick lay-firsts @ 3 roll lay-ly ly-init ;
: lay-tier ( lay -- outcome )
  dup lay-snap snap-tf tf-start dup ok? 0= if nip exit then drop
  dup lay-ly-start lay-ly ly-load snap-damaged ;
\ The layer's slots: its declarations but block records.
: lay-count ( lay -- n )
  lay-ly 0 over ly-decls# 0 ?do
    i 2 pick ly-decl 2 pick ly-stage @ slot-record? 1 and +
  loop nip ;
: lay-sections ( lay -- outcome )
  dup lay-sn @ over lay-snap snap-first !
  dup lay-names @ lp-names 2 pick lay-ly ly-units + over lay-snap snap-names !
  dup lay-count dup 2 pick lay-n ! swap lay-snap snap-read ;
: lay-open ( c-addr u fuel lay -- outcome )
  >r r@ lay-base @ snap-sum r@ lay-firsts @ r@ lay-snap snap-layer-open
  dup ok? if drop r@ lay-tier then dup ok? if drop r@ lay-sections then r> drop ;

\ ---- The arrays: per layer slot its slot as loaded and whether it is
\ new; per declaration loaded before, its slot + 1.
: lay-map-room ( lay -- outcome ) dup lay-n @ swap lay-map ua-new ;
: lay-new-room ( lay -- outcome ) dup lay-n @ swap lay-new ua-new ;
: lay-old-room ( lay -- outcome )
  dup lay-stage @ stage-decls 2dup swap lay-old ! swap lay-slots ua-new ;
: lay-arrays ( lay -- outcome )
  outcome-ok ['] lay-map-room ok-with ['] lay-new-room ok-with ['] lay-old-room ok-with
  nip ;
: lay-slot-of ( sd lay -- s ) lay-slots @ ly@ 1- ;
: lay-slots-fill ( lay -- )
  0 over lay-old @ 0 ?do
    i 2 pick lay-stage @ staged-at 2 pick lay-stage @ slot-record? if
      1+ dup i 3 pick lay-slots @ ly! then
  loop drop drop ;

\ ---- Numbering as loaded: a layer slot s (from the base's own on), a
\ lookup's key (a name of the layer's tier) and answer (its slot); where
\ layer slot j's lists start; entry j of the layer's lookups so.
: lay-slot# ( s lay -- s' )
  2dup lay-sn @ u< if drop exit then tuck lay-sn @ - swap lay-map @ ly@ ;
: lay-key ( key lay -- key' )
  over lf-look-outside = if drop exit then
  over lf-look-name over lay-names @ u< if drop exit then
  >r dup lf-look-name r> lay-ly ly-name
  ok? if lf-look-renumber else 2drop lf-look-outside then ;
: lay-answer ( answer lay -- answer' )
  over lf-look-slot+1 ?dup 0= if drop exit then
  1- swap lay-slot# 1+ lf-look-reslot ;
: lay-from ( j lay -- dk lk ) lay-snap snap-starts @ swap 2* cells + 2@ swap ;
: lay-entry ( j lay -- key answer )
  2dup lay-snap look-key over lay-key >r
  tuck lay-snap look-answer swap lay-answer r> swap ;

\ ---- Deciding a unit of the layer: one declaration, or an inductive
\ block whole (its record and members), with its slots; kept in the
\ record while it is decided (lay-ui: its first record, lay-ud records,
\ lay-uj: its first slot, lay-us slots).
: lay-decl ( i lay -- addr ) lay-ly ly-decl ;
: lay-staged ( sd lay -- addr ) lay-stage @ staged-at ;
: lay-slot ( j lay -- addr ) lay-snap snap-slot ;
: base-slot ( s lay -- addr ) lay-base @ snap-slot ;
\ Layer slot j and loaded slot s: the same outcome, axiom set, warnings,
\ recipe, shape and fuel (fields 0 and 3-8).
: verdict-same? ( j s lay -- flag )
  tuck base-slot >r lay-slot r>
  2dup 1 u32s tuck compare 0= >r
  sl-axioms u32s + swap sl-axioms u32s + swap sl-deps sl-axioms - u32s tuck compare 0=
  r> and ;
: decls-same? ( i sd n lay -- flag )
  swap >r true r> 0 ?do
    3 pick i + 2 pick lay-decl 3 pick i + 3 pick lay-staged decl-same? and
  loop nip nip nip ;
: verdicts-same? ( j s n lay -- flag )
  swap >r true r> 0 ?do 3 pick i + 3 pick i + 3 pick verdict-same? and loop nip nip nip ;
: lay-block? ( i lay -- flag ) tuck lay-decl swap lay-stage @ slot-record? 0= ;
: unit-members ( i lay -- m )
  tuck lay-decl staged-more u32@ swap lay-stage @ stage-tuples
  0 3 0 do i 3 pick 3 pick tuple-item + loop nip nip ;
: lay-unit-size ( i lay -- decls slots )
  2dup lay-block? if unit-members dup 1+ swap else 2drop 1 1 then ;
: lay-unit-set ( i j lay -- )
  >r r@ lay-uj ! dup r@ lay-ui ! r@ lay-unit-size r@ lay-us ! r> lay-ud ! ;
: lay-fits? ( lay -- flag )
  dup lay-ui @ over lay-ud @ + over lay-ly ly-decls# > 0=
  over lay-uj @ 2 pick lay-us @ + rot lay-n @ > 0= and ;
\ Candidates: the declarations loaded before of the unit's name (a
\ block's first member's), newest first.
: lay-head ( i lay -- h ) over swap lay-block? if 1+ then ;
: lay-name-of ( i lay -- name ) tuck lay-head swap lay-decl staged-name u32@ ;
: lay-newest ( name lay -- sd|-1 )
  >r dup r@ lay-stage @ stage-tier tier-names cons-numbers u<
  if r@ lay-stage @ stage-find 0= if -1 then else drop -1 then r> drop ;
: lay-older ( sd lay -- sd' ) lay-stage @ staged-prev@ 1- ;
: lay-old-of ( sd lay -- sd' )
  begin over 0< 0= 2 pick 2 pick lay-old @ < 0= and while
    dup >r lay-older r>
  repeat drop ;
\ The unit's first staged declaration around candidate sd.
: lay-start ( sd decls -- sd' ) 1 > if 1- then ;
: lay-match? ( i decls sd lay -- flag )
  >r over lay-start dup 0< if 2drop drop r> drop false exit then swap r> decls-same? ;
\ The first candidate of the unit's content, as its first staged
\ declaration, or -1; and whether there was any candidate.
: lay-found ( i decls lay -- first|-1 any? )
  >r over r@ lay-name-of r@ lay-newest r@ lay-old-of
  dup 0< if 2drop drop -1 false r> drop exit then
  begin dup 0< 0= while
    2 pick 2 pick 2 pick r@ lay-match? if swap lay-start nip true r> drop exit then
    r@ lay-older
  repeat 2drop drop -1 true r> drop ;
: lay-refuse ( c-addr lay -- outcome ) >r outcome-invalid swap r@ lay-ui @ r> lay-note ;
\ The same for a failure with its own outcome (full stays full).
: lay-blame ( outcome c-addr lay -- outcome ) dup lay-ui @ swap lay-note ;
\ Loaded before: the slots refer to the loaded ones, of the same verdicts.
: lay-first-slot ( first lay -- s ) dup lay-ud @ 1 > if swap 1+ swap then lay-slot-of ;
: lay-take ( j s n lay -- )
  swap 0 ?do over i + 3 pick i + 2 pick lay-map @ ly! loop 2drop drop ;
\ New: its declarations entered, its slots after those loaded; a
\ declaration the stage refuses keeps its outcome (full when the heap or
\ the stage's limit refuses; review FRI F1).
: lay-enter-all ( lay -- outcome )
  dup lay-ud @ 0 ?do
    dup lay-ui @ i + over lay-ly ly-enter dup ok? 0= if
      swap c" declarations" swap lay-blame unloop exit then drop
  loop drop outcome-ok ;
: lay-new! ( k lay -- )
  >r r@ lay-cur @ over + over r@ lay-uj @ + r@ lay-map @ ly!
  1 swap r@ lay-uj @ + r> lay-new @ ly! ;
: lay-enter ( lay -- outcome )
  dup lay-enter-all dup ok? 0= if nip exit then drop
  dup lay-us @ 0 ?do i over lay-new! loop dup lay-us @ swap lay-cur +! outcome-ok ;
\ For an import pass (lay-twins set: an export follows), a unit of the
\ same verdicts is the loaded one only if each of its slots has the
\ lookups of its twin (review rvSS 1): layer slot j's, numbered as loaded
\ (lay-entry), as many as loaded slot s's, each found in s's list with
\ its answer; the pair is kept in the record's cursor (lay-pair!). Where
\ they differ (a nested block's scratch names asked in a tier that held
\ other names), the unit is entered as new, beside its twin, so that the
\ import can replay its slots too (env-import.fs tries the declarations
\ of a name newest first and tells them apart by their lookups). Loaded
\ alone, the snapshots publish every slot as one environment, which holds
\ a name once: there the unit is the loaded one, as before.
: lay-pair! ( j s lay -- ) tuck lay-at-s ! lay-at-j ! ;
: look-in? ( key answer addr n -- flag )
  >r -rot r> 0 ?do 2 pick i entry@ 2over d= if 2drop drop true unloop exit then loop
  2drop drop false ;
: lay-own-count ( lay -- n ) sl-looks swap dup lay-at-j @ swap lay-slot fld@ ;
: lay-twin-count ( lay -- n ) sl-looks swap dup lay-at-s @ swap base-slot fld@ ;
: lay-twin-list ( lay -- addr )
  dup lay-at-s @ 2* cells over lay-base @ snap-starts @ + cell+ @ 8 *
  swap lay-base @ ss-looks swap snap-block + ;
: lay-entry-j ( i lay -- key answer )
  dup lay-at-j @ over lay-from nip rot + swap lay-entry ;
: lay-has? ( key answer lay -- flag ) dup lay-twin-list swap lay-twin-count look-in? ;
: lay-own-in? ( i lay -- flag ) tuck lay-entry-j rot lay-has? ;
: lay-own-in-at? ( lay i -- lay flag ) over lay-own-in? ;
: lay-looks-same? ( lay -- flag )
  dup lay-twin-count over lay-own-count <> if drop false exit then
  dup lay-own-count ['] lay-own-in-at? all? nip ;
: lay-twin-same? ( s i lay -- flag )
  >r tuck + swap r@ lay-uj @ + swap r@ lay-pair! r> lay-looks-same? ;
: unit-looks-same? ( s lay -- flag )
  true over lay-us @ 0 ?do 2 pick i 3 pick lay-twin-same? and loop nip nip ;
: lay-twin? ( s lay -- flag )
  dup lay-twins @ if unit-looks-same? 0= else 2drop false then ;
: lay-same ( first lay -- outcome )
  tuck lay-first-slot over lay-uj @ over 3 pick lay-us @ 4 pick verdicts-same?
  0= if drop c" a declaration of two snapshots with other verdicts" swap lay-refuse exit
  then
  2dup swap lay-twin? if drop lay-enter exit then
  over lay-uj @ swap rot dup lay-us @ swap lay-take outcome-ok ;
\ A new unit clashes when any of its declarations (a block's every member,
\ not only its first; review rvSN4 M2) has the name of one loaded before:
\ Lean refuses an import that declares a name twice.
: lay-loaded? ( i lay -- flag )
  tuck lay-decl staged-name u32@ ?dup 0= if drop false exit then
  over lay-newest swap lay-old-of 0< 0= ;
: lay-clash? ( lay -- flag )
  false over lay-ud @ 0 ?do over lay-ui @ i + 2 pick lay-loaded? or loop nip ;
: lay-decide ( lay -- outcome )
  dup lay-fits? 0= if c" declarations" swap lay-refuse exit then
  dup lay-ui @ over lay-ud @ 2 pick lay-found
  over 0< 0= if drop swap lay-same exit then 2drop
  dup lay-clash? 0= if lay-enter exit then
  c" a name of two snapshots with other content" swap lay-refuse ;
: lay-units ( lay -- outcome )
  0 0 begin 2 pick lay-ly ly-decls# 2 pick > while
    2dup 4 pick lay-unit-set 2 pick lay-decide dup ok? 0= if nip nip nip exit then drop
    2 pick lay-us @ + swap 2 pick lay-ud @ + swap
  repeat 2drop drop outcome-ok ;

\ ---- The new slots appended to the base record: each slot record, its
\ site, where its lists start, its dependencies and lookups numbered as
\ loaded and sorted again (the numbering: lay-slot#, lay-key, lay-answer,
\ lay-entry, above).
\ (entry@, entry! and look-sort, which sorts a list again: env-snapshot.fs.)
\ Growing the base record's section i by u bytes, and its starts to n slots
\ (never RESIZE to 0 bytes, which Gforth 0.7.3 takes as freeing the block).
: base-grow ( u i lay -- outcome )
  lay-base @ >r dup r@ snap-block over r@ snap-size 3 pick + dup >r 1 max resize
  if drop 2drop r> drop r> drop outcome-full exit then
  r> rot r> snap-block! drop outcome-ok ;
: starts-grow ( n lay -- outcome )
  swap 2* cells swap lay-base @ snap-starts block-resize ;
\ The counts the new slots add, from their records in the layer.
: lay-adds ( k lay -- n )
  0 over lay-n @ 0 ?do
    i 2 pick lay-new @ ly@ if over i swap lay-slot 3 pick swap fld@ + then
  loop nip nip ;
: lay-slots-grow ( lay -- outcome )
  dup lay-cur @ sl-fields# u32s * over lay-base @ ss-slots swap snap-size - ss-slots
  rot base-grow ;
: lay-deps-grow ( lay -- outcome )
  sl-deps over lay-adds /snap-dep * ss-deps rot base-grow ;
: lay-looks-grow ( lay -- outcome )
  sl-looks over lay-adds /snap-look * ss-looks rot base-grow ;
: lay-sites-grow ( lay -- outcome )
  ss-sites over lay-snap snap-size ss-sites rot base-grow ;
: lay-starts-room ( lay -- outcome ) dup lay-cur @ swap starts-grow ;
: lay-room ( lay -- outcome )
  outcome-ok ['] lay-slots-grow ok-with ['] lay-deps-grow ok-with
  ['] lay-looks-grow ok-with ['] lay-sites-grow ok-with ['] lay-starts-room ok-with
  nip ;
\ The slot being appended (review rvSN4 m4: a cursor in the record): the
\ layer's slot j and its slot s as loaded; where the layer's lists of j
\ start; how many field k (sl-deps, sl-looks) of s counts; where the base
\ record's lists end, which s's are appended to.
: lay-j ( lay -- j ) lay-at-j @ ;
: lay-s ( lay -- s ) lay-at-s @ ;
: lay-cursor! ( j lay -- ) 2dup lay-at-j ! tuck lay-map @ ly@ swap lay-at-s ! ;
: lay-count-of ( k lay -- n ) dup lay-s swap base-slot fld@ ;
: lay-dep-at ( lay -- addr )
  lay-base @ dup ss-deps swap snap-block swap snap-dk @ u32s + ;
: lay-look-at ( lay -- addr )
  lay-base @ dup ss-looks swap snap-block swap snap-lk @ /snap-look * + ;
\ The layer's own sorter (its snapshot record's; review reuse-k1 M2).
: lay-sorter ( lay -- sorter ) lay-snap snap-sorter ;
\ Dependency i and lookup i of j, numbered as loaded, into s's list.
: lay-dep! ( i lay -- )
  2dup dup lay-j swap lay-from drop + over lay-snap dep@ over lay-slot#
  -rot lay-dep-at swap u32s + u32-le! ;
: lay-look! ( i lay -- )
  2dup dup lay-j swap lay-from nip + over lay-entry 2swap lay-look-at swap entry! ;
\ Each list sorted again in the base record, then passed (ok, or full:
\ env-snapshot.fs).
: lay-deps ( lay -- outcome )
  sl-deps over lay-count-of dup >r 0 ?do i over lay-dep! loop
  dup lay-dep-at over lay-sorter rot r@ swap lay-base @ snap-dk +! r> swap dep-sort ;
: lay-looks ( lay -- outcome )
  sl-looks over lay-count-of dup >r 0 ?do i over lay-look! loop
  dup lay-look-at over lay-sorter rot r@ swap lay-base @ snap-lk +! r> swap look-sort ;
: lay-site ( s lay -- )
  tuck base-slot sl-site over fld@ ?dup
  if rot lay-site0 @ + sl-site rot fld! else 2drop then ;
: lay-append ( j lay -- outcome )
  tuck lay-cursor! dup lay-j over lay-slot over lay-s 2 pick base-slot
  sl-fields# u32s move
  dup lay-s over lay-site dup lay-s over lay-base @ start!
  dup lay-deps swap lay-looks outcome-and ;
: lay-append-new ( i lay -- outcome )
  2dup lay-new @ ly@ if lay-append else 2drop outcome-ok then ;
\ Every new slot appended (each list sorted again: ok, or full, the first
\ failure kept), then the base's slots counted (only when all are ok).
: lay-count! ( lay -- ) dup lay-cur @ swap lay-base @ snap-n ! ;
: lay-all-new ( lay -- outcome )
  outcome-ok over lay-n @ 0 ?do over i swap lay-append-new outcome-and loop nip ;
: lay-appends ( lay -- outcome )
  dup lay-room dup ok? 0= if nip exit then drop
  dup lay-all-new dup ok? if over lay-count! then nip ;
\ The site texts appended after the base's.
: lay-sites ( lay -- )
  dup lay-snap ss-sites swap snap-block over lay-base @ ss-sites swap snap-block
  2 pick lay-site0 @ + rot lay-snap ss-sites swap snap-size move ;

\ Load the layer named c-addr u (fuel per declaration as the base's) on
\ the base (lay-init): ok, or why not (lay-error).
\ The slots filled, the cursor and the sites' start at the base's ends,
\ then the units entered.
: lay-ends ( lay -- )
  dup lay-slots-fill dup lay-base @ snap-n @ over lay-cur !
  dup lay-base @ ss-sites swap snap-size swap lay-site0 ! ;
: lay-filled ( lay -- outcome ) dup lay-ends lay-units ;
: lay-merge ( lay -- outcome )
  outcome-ok ['] lay-arrays ok-with ['] lay-filled ok-with ['] lay-appends ok-with
  dup ok? if over lay-sites then nip ;
: lay-load ( c-addr u fuel lay -- outcome )
  dup >r lay-open dup ok? if drop r@ lay-merge then r> drop ;

base !   \ the BASE this file was loaded with

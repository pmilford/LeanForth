\ The checked environment saved and loaded (ADR 0020 D1-D6; plan task
\ 6.2.5, step SN3). [kernel][format] code: not through the review gate
\ (AGENTS.md); LeanForth-specific. A snapshot is one sectioned file
\ (lib/sections.fs): the input tier's ten sections (import/snapshot-tier.fs,
\ kinds 1-10), then seven of the environment's, in this order (kind =
\ position + 1; unit size in bytes; every field 32-bit little-endian):
\   10 identity (4)     32 fields: the export's SHA-256 (0-7, its bytes in
\                       order), the manifest's SHA-256 (8-15; 0 without one),
\                       the export's bytes (16-17) and lines (18-19), flags
\                       (20: 1 manifest enforced, 2 any Lean version, 4 the
\                       metadata names another version), the first number of
\                       each tier section 1-8 (21-28; all 0 in a base
\                       snapshot), the slots (29), dependencies (30) and
\                       lookups (31)
\   11 slots (72)       one per declaration, 18 fields: outcome; marks (1
\                       skipped, 2 added, 4 published with the slot before,
\                       one span); provenance (1 rests on saved results, 2
\                       taken from a snapshot); axiom bits; warnings; recipe;
\                       shape; fuel used (7-8, 64-bit, -1 not known); its
\                       dependencies and lookups (counts); its diagnostic:
\                       code, first (12-13) and second (14-15) numbers, the
\                       check step, the site (an offset + 1 into the site
\                       texts, 0 for none)
\   12 dependencies (4) each slot's slot numbers, in slot order
\   13 lookups (8)      each slot's (key, answer) pairs (environment.fs,
\                       "Lookups"), in slot order
\   14 site texts (1)   the diagnostics' sites, counted strings, once each
\   15 manifest (1)     the export's manifest, byte for byte (or empty)
\   16 information (1)  a JSON text: LeanForth's version, commit, host,
\                       engine and cell width; information only
\ The header's caller fields: 0 the mark "LFSN" (snap-mark), 1 this format
\ (snap-version), 2 the verdict version (kernel/verdict-version.fs), 3-4
\ the fuel per declaration, 5 the allowlist's version, 6 its bits, 7 the
\ layers below this one (0: a base snapshot), 8-15 the base's identity (its
\ header's SHA-256, 0 for none). A layer (plan step SN4; snap-layer-base!,
\ snap-layer-slots!, snap-layer-decls!) holds only its own records and
\ slots, numbered on from its base's counts (identity 21-28 and the slots'
\ first number), field 7 1 (a layer on a base alone); it is opened with
\ snap-layer-open on the base it names and merged into it by
\ env-layers.fs. A layer given where a base is expected is refused as
\ unsupported. Nothing a build derives is written: no hash table,
\ address or hash value (ADR 0020 F1: lookup tables are rebuilt on load).
\
\ Writing (snap-save): after a run in which every slot became final, the
\ tier's sections, then the environment's, from the current environment
\ and the caller's facts xt ( d -- fuel step ), step a run-record.fs
\ /rr-step with the diagnostic its check left; to FILE.partial, renamed
\ when complete. Two runs of one export with one build, in any order of
\ checking (--jobs), write the same bytes: lists are written in slot
\ order, never in the order of publication. The names checks made beyond
\ the input (the environment's own tier, environment.fs lf-env-outer; plan
\ step SN5) are written after the tier's names, as names of the tier, in a
\ content order ("Names beyond the input" below), their keys as those.
\
\ Loading, each step refusing before anything is published: snap-open (the
\ header: mark, format and verdict versions, fuel, allowlist; the table;
\ the identity), snap-tier (the tier into a fresh stage, every record
\ checked as SN2 says), snap-read (the environment's sections, every field
\ in range: outcomes, marks, axiom bits within the allowlist's, counts
\ adding up to their sections, dependencies ascending and below their
\ span's first slot, lookups ascending with their answers below it, sites
\ inside their section); then the caller seals and feeds the stage, makes
\ an environment in development mode (lf-env-develop) and runs the
\ publisher's serial steps with snap-fill as the check word: it fills the
\ candidate from the saved slot (lf-env-saved!), so the publisher re-checks
\ it as a check's (dependencies, axiom set, provenance, names, kind) and
\ publishes it final with provenance saved; last snap-same? compares every
\ published slot with its saved fields. A slot the publisher would publish
\ otherwise is refused (invalid). What a loaded snapshot vouches for is
\ ADR 0020 D4's: not that the checker is right, not that the file was not
\ forged (its SHA-256s catch damage only).
\
\ Outcomes (ADR 0008): ok; invalid for a malformed, damaged or altered file
\ (snap-error names the section, or the slot), other settings (fuel,
\ allowlist) than the run's, a stage or environment that does not fit;
\ unsupported for another format or verdict version (a base of one of the
\ two older verdict versions of the window loads marked snap-carry, for
\ the caller's carry pass, plan step 6.2.5c3; any older one loads marked
\ stale when snap-stale-allowed is true: --snapshot-stale-ok), or a
\ layered snapshot; full for no heap. A damaged section the container
\ reports as rejected is invalid here. The file is closed by snap-close;
\ the heap blocks are freed by snap-free.
\ State: one /snap record per file being written or read, used by one task;
\ snap-loading, the record snap-fill reads (one load at a time);
\ snap-stale-allowed, the flag, set by the caller before loading;
\ snap-outers and the site tables, the writer's (one save at a time).

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/u32.fs
require ../lib/sections.fs
require ../lib/sha256.fs
require ../core/axiom-allowlist.fs
require ../import/stage.fs
require ../import/snapshot-tier.fs
require ../import/run-record.fs
require ./environment.fs
require ./env-publish.fs
require ./verdict-version.fs

1 constant snap-version
$4E53464C constant snap-mark          \ "LFSN" as little-endian bytes
\ The caller's header fields.
0 constant sh-mark  1 constant sh-version  2 constant sh-verdict  3 constant sh-fuel
5 constant sh-allow-version  6 constant sh-allow-bits
7 constant sh-layers  8 constant sh-base
\ The sections after the tier's, by position.
10 constant ss-identity  11 constant ss-slots  12 constant ss-deps  13 constant ss-looks
14 constant ss-sites  15 constant ss-manifest  16 constant ss-info
17 constant snap-sections#
create snap-unit-table 4 , 72 , 4 , 8 , 1 , 1 , 1 ,
: snap-unit ( i -- au ) tier-sections# - cells snap-unit-table + @ ;
\ The identity's fields.
0 constant si-export  8 constant si-manifest  16 constant si-bytes  18 constant si-lines
20 constant si-flags  21 constant si-firsts  29 constant si-slots  30 constant si-deps
31 constant si-looks  32 constant si-fields#
1 constant snap-enforced  2 constant snap-any-lean  4 constant snap-other
\ A slot's fields.
0 constant sl-outcome  1 constant sl-marks  2 constant sl-provenance  3 constant sl-axioms
4 constant sl-warnings  5 constant sl-recipe  6 constant sl-shape  7 constant sl-fuel
9 constant sl-deps  10 constant sl-looks  11 constant sl-code  12 constant sl-first
14 constant sl-second  16 constant sl-step  17 constant sl-site  18 constant sl-fields#
1 constant mark-skipped  2 constant mark-added  4 constant mark-with
2 constant prov-taken
lf-allowlist-bits lf-axiom-unlisted or constant snap-axiom-bits

\ Blocks a record owns, freed by snap-free: the identity, slots,
\ dependencies, lookups, site texts, manifest and information (read, or
\ built; the manifest and information the caller's while writing), and
\ the starts (loading: per slot its first dependency and lookup).
7 constant snap-blocks#
begin-structure /snap
  /tier-file +field snap-tf             \ the tier part and the sectioned file
  snap-blocks# cells +field snap-blocks \ the sections' bytes, by position - 10
  snap-blocks# cells +field snap-sizes  \ and their lengths in bytes
  field: snap-owned                     \ bits: the blocks this record frees
  field: snap-starts                    \ loading: 2 cells per slot
  field: snap-n                         \ slots
  field: snap-asked                     \ loading: the run's fuel, or -1 for the file's
  32 +field snap-sum                    \ the file's identity: its header's SHA-256
  field: snap-facts                     \ writing: xt ( d -- fuel step )
  field: snap-why                       \ counted string: what was refused, or 0
  field: snap-at                        \ the slot refused, or -1
  field: snap-dk                        \ reading: dependencies passed so far
  field: snap-lk                        \ and lookups
  field: snap-head                      \ the first slot of the span being read
  field: snap-names                     \ reading: the tier's names (snap-tier)
  field: snap-first                     \ reading: the first slot's number (a layer's)
  field: snap-wn                        \ writing: the slots written
  field: snap-which                     \ writing a layer: xt ( j -- d ), slot j's, or 0
  field: snap-renum                     \ and xt ( d -- s ), d's number in the layer
  32 +field snap-base-sha               \ writing a layer: its base's identity
  field: snap-layered                   \ writing: true for a layer
  field: snap-expect                    \ reading a layer: its base's identity, or 0
  field: snap-expect-firsts             \ and the base's tier counts (8 cells)
  field: snap-stale                     \ reading: true for an older verdict version
  field: snap-carry                     \ reading a base: older, in the window
end-structure
variable snap-loading   \ the record snap-fill reads
\ A development flag (owner, 2026-11-11; ADR 0020 amendment 3): true lets
\ a snapshot of an older verdict version load, marked stale (snap-stale),
\ every result taken from it reported as stale, never as this build's
\ verdict. False (the default): such a snapshot is refused as unsupported.
variable snap-stale-allowed  false snap-stale-allowed !
: snap-sf ( snap -- sf ) snap-tf tf-sf ;
: snap-cell ( i snap field -- addr ) >r swap tier-sections# - cells swap r> execute + ;
: snap-block ( i snap -- addr ) ['] snap-blocks snap-cell @ ;
: snap-size ( i snap -- u ) ['] snap-sizes snap-cell @ ;
: snap-block! ( addr u i snap -- )
  2dup ['] snap-sizes snap-cell >r ['] snap-blocks snap-cell r> rot swap ! ! ;
: snap-own ( i snap -- ) swap tier-sections# - 1 swap lshift swap snap-owned dup @ rot or
  swap ! ;
: snap-owns? ( k snap -- flag ) snap-owned @ 1 rot lshift and 0<> ;
\ A refusal's reason, the first only (the tier's own, when it refused).
: snap-note ( c-addr d snap -- ) dup snap-why @ if drop 2drop exit then tuck snap-at !
  snap-why ! ;
: snap-refuse ( outcome c-addr snap -- outcome ) -1 swap snap-note ;
: snap-error ( snap -- c-addr u d )
  dup snap-why @ ?dup if count rot snap-at @ else snap-tf tier-file-error then ;
: snap-init ( snap -- ) dup /snap erase dup snap-tf tier-file-init -1 swap snap-at ! ;
: snap-free ( snap -- )
  dup snap-tf tier-sections-free
  snap-blocks# 0 do i over snap-owns? if dup snap-blocks i cells + @ free drop then loop
  dup snap-starts @ ?dup if free drop then snap-init ;
: snap-close ( snap -- ) snap-sf sections-close drop ;
\ The container's rejected (a SHA-256 that differs) is a damaged file.
: snap-damaged ( outcome -- outcome' ) dup outcome-rejected = if drop outcome-invalid then
  ;

\ ---- Fields, little-endian at addr: 32-bit, and 64-bit as lo, hi.
: fld@ ( k addr -- u ) swap u32s + u32-le@ ;
: fld! ( u k addr -- ) swap u32s + u32-le! ;
1 cells 4 > constant snap-wide?
: cell-hi ( n -- hi ) snap-wide? if 32 rshift u32-mask and else 0< u32-mask and then ;
: hi-cell ( lo hi -- n ) snap-wide? if 32 lshift or else drop then ;
: fld2@ ( k addr -- n ) 2dup fld@ -rot swap 1+ swap fld@ hi-cell ;
: fld2! ( n k addr -- ) 2>r dup u32-mask and 2r@ fld! cell-hi 2r> swap 1+ swap fld! ;
\ The identity's fields, in its block.
: snap-id ( snap -- addr ) ss-identity swap snap-block ;
: id@ ( k snap -- u ) snap-id fld@ ;
: id! ( u k snap -- ) snap-id fld! ;
: id-sha ( k snap -- c-addr ) snap-id swap u32s + ;
: id-sha! ( c-addr k snap -- ) id-sha 32 move ;
: snap-slot ( d snap -- addr ) ss-slots swap snap-block swap sl-fields# u32s * + ;
: slot-env ( d -- slot ) lf-env lf-env-slot ;
\ A lookup's key: its name and kind (environment.fs, "Lookups").
: key-name ( key -- name ) 4 rshift ;
: key-kind ( key -- kind ) lf-look-kinds 1- and ;
\ The (key, answer) pairs of a list as written, little-endian; a list
\ sorted by key again (ascending, unsigned), by insertion.
: entry@ ( addr k -- key answer ) 8 * + dup u32-le@ swap 4 + u32-le@ ;
: entry! ( key answer addr k -- ) 8 * + tuck 4 + u32-le! u32-le! ;
: u32-swap ( a1 a2 -- ) 2dup u32-le@ swap u32-le@ rot u32-le! swap u32-le! ;
: entry-swap ( addr -- ) dup dup 8 + u32-swap 4 + dup 8 + u32-swap ;
\ Entry k sunk below every earlier entry of a greater key.
: entry-sink ( addr k -- )
  begin dup while
    2dup 1- 8 * + dup u32-le@ over 8 + u32-le@ u> 0= if drop 2drop exit then
    entry-swap 1-
  repeat 2drop ;
: look-sort ( addr n -- ) 1 max 1 ?do dup i entry-sink loop drop ;

\ ---- Writing.
\ A zeroed block of u bytes for section i, owned: ok or full.
: snap-alloc ( u i snap -- outcome )
  >r over 1 max allocate if drop 2drop r> drop outcome-full exit then
  dup 3 pick erase -rot dup r@ snap-own r> snap-block! outcome-ok ;
\ Start writing: a blank record with its identity block.
: snap-begin ( snap -- outcome ) dup snap-init si-fields# u32s ss-identity rot snap-alloc
  ;
\ The export: its SHA-256, bytes, lines and flags (snap-enforced ...).
: snap-export! ( sha-addr bytes lines flags snap -- )
  >r si-flags r@ id! si-lines r@ snap-id fld2! si-bytes r@ snap-id fld2! si-export r>
  id-sha! ;
: snap-manifest-sha! ( sha-addr snap -- ) si-manifest swap id-sha! ;
\ The manifest's bytes and the information text, which the caller keeps
\ until snap-save has written them.
: snap-manifest! ( c-addr u snap -- ) ss-manifest swap snap-block! ;
: snap-info! ( c-addr u snap -- ) ss-info swap snap-block! ;
: snap-facts! ( xt snap -- ) snap-facts ! ;

\ The slots written: every slot of the environment, or a layer's (plan
\ step SN4; snap-layer!): its slot j is the environment's slot d (the
\ caller's xt), and a slot d it refers to is numbered s in the base and the
\ layer (the caller's xt; a base numbers as the environment).
: snap-e ( j snap -- d ) snap-which @ ?dup if execute then ;
: snap-s ( d snap -- s ) snap-renum @ ?dup if execute then ;
: snap-wn@ ( snap -- n ) snap-wn @ ;
\ Every slot's lists counted, then the blocks for them.
: d-deps ( d -- n ) slot-env lf-slot-count @ ;
: d-looks ( d -- n ) slot-env lf-slot-looked @ ;
: snap-totals ( snap -- deps looks )
  0 0 rot dup snap-wn@ 0 ?do
    i over snap-e >r rot r@ d-deps + rot r> d-looks + rot
  loop drop ;
: snap-lists ( snap -- outcome )
  >r r@ snap-totals 2dup si-looks r@ id! si-deps r@ id!
  8 * ss-looks r@ snap-alloc dup ok? 0= if nip r> drop exit then drop
  4 * ss-deps r@ snap-alloc dup ok? 0= if r> drop exit then drop
  r@ snap-wn@ dup si-slots r@ id! sl-fields# u32s * ss-slots r> snap-alloc ;
\ A slot's marks and provenance as written.
: slot-marks ( slot -- u )
  dup lf-slot-skipped @ 0<> mark-skipped and over lf-slot-added @ 0<> mark-added and or
  swap lf-slot-member @ 0<> mark-with and or ;
: slot-prov ( slot -- u )
  dup lf-slot-provenance @ lf-provenance-saved and 0<> 1 and
  swap lf-slot-saved @ 0<> prov-taken and or ;
: put-env ( addr slot -- addr )
  dup lf-slot-outcome @ sl-outcome 3 pick fld! dup slot-marks sl-marks 3 pick fld!
  dup slot-prov sl-provenance 3 pick fld! dup lf-slot-axioms @ sl-axioms 3 pick fld!
  dup lf-slot-warnings @ sl-warnings 3 pick fld! dup lf-slot-recipe @ sl-recipe 3 pick
  fld!
  dup lf-slot-shape @ sl-shape 3 pick fld! dup lf-slot-count @ sl-deps 3 pick fld!
  lf-slot-looked @ sl-looks 2 pick fld! ;
: put-step ( addr step -- addr )
  dup kept-code @ sl-code 3 pick fld! dup kept-first @ sl-first 3 pick fld2!
  dup kept-second @ sl-second 3 pick fld2! kept-step @ sl-step 2 pick fld! ;

\ The site texts, once each, in slot order: a slab of counted strings and
\ one of (site, its offset + 1) pairs seen so far. Shared, one save at a
\ time (as the driving task's).
begin-structure /sites
  /slab +field sites-bytes
  /slab +field sites-seen
end-structure
create snap-site-tables /sites allot  snap-site-tables /sites erase
: site-bytes ( -- slab ) snap-site-tables sites-bytes ;
: site-pairs ( -- slab ) snap-site-tables sites-seen ;
: sites-init ( -- outcome )
  1 1 slab-limit-max site-bytes slab-init ok-then? 0= if exit then
  2 cells dup slab-limit-max site-pairs slab-init ;
: sites-free ( -- ) site-bytes slab-free site-pairs slab-free ;
: seen-at ( k -- addr ) site-pairs slab-at ;
: site-seen ( site -- n|0 )
  site-pairs slab-count 0 ?do
    dup i seen-at @ = if drop i seen-at cell+ @ unloop exit then
  loop drop 0 ;
: site-text ( site -- c-addr u ) dup count nip 1+ ;
: site-copied ( site -- outcome )
  dup site-text nip site-bytes slab-claim ok-then? 0= if nip exit then
  site-bytes slab-at swap site-text rot swap move outcome-ok ;
: site-paired ( site n -- outcome )
  1 site-pairs slab-claim ok-then? 0= if nip nip exit then
  seen-at tuck cell+ ! ! outcome-ok ;
: site-add ( site -- n outcome )
  site-bytes slab-count 1+ >r dup site-copied dup ok? 0= if nip r> drop 0 swap exit then
  drop r@ site-paired r> swap ;
: site-of ( site -- n outcome )
  ?dup 0= if 0 outcome-ok exit then dup site-seen ?dup if nip outcome-ok else site-add
  then ;
: put-site ( addr step -- addr outcome ) kept-site @ site-of >r sl-site 2 pick fld! r> ;
\ One slot's record, from its environment slot and the caller's facts.
: put-slot ( j snap -- outcome )
  2dup snap-slot -rot tuck snap-e swap >r tuck slot-env put-env swap
  r> snap-facts @ execute >r sl-fuel 2 pick fld2! r@ put-step r> put-site nip ;
: put-slots ( snap -- outcome )
  dup snap-wn@ 0 ?do
    i over put-slot dup ok? 0= if nip unloop exit then drop
  loop drop outcome-ok ;
\ The dependencies and lookups, each slot's in turn, slots numbered as
\ written (snap-s): an answer's slot + 1 field.
: answer-renum ( answer snap -- answer' )
  over lf-look-slot+1 ?dup 0= if drop exit then
  1- swap snap-s 1+ 4 lshift swap 15 and or ;
\ n slot numbers as little-endian fields at addr sorted ascending (a
\ layer's are numbered again, so their order may change).
: dep-sort ( addr n -- )
  dup 2 < if 2drop exit then 1 ?do
    dup i 4 * + u32-le@ i
    begin dup 0> if 2 pick over 1- 4 * + u32-le@ 2 pick u> else false then while
      2 pick over 1- 4 * + u32-le@ 3 pick 2 pick 4 * + u32-le! 1-
    repeat 4 * 2 pick + u32-le!
  loop drop ;
: put-deps ( addr d snap -- addr' )
  over slot-env lf-slot-count @ 3 pick 2>r
  swap slot-env dup lf-slot-count @ 0 ?do
    i over lf-dep-at 2 pick snap-s 3 pick u32-le! rot 4 + -rot
  loop 2drop 2r> swap dep-sort ;
\ Names beyond the input (environment.fs, the seal; plan step SN5): the
\ names a check made that its input tier does not hold, kept in the
\ environment's own tier (lf-env-outer), are written after the tier's
\ names, as names of the tier: canon, a scratch tier over the stage's,
\ holds them in the file's order, numbered on from the stage's names. The
\ order is the written slots' in turn, each slot's names by their content
\ (the root's number, then each component from the top: tag, then number
\ or bytes; then the depth), never the order in which the publisher met
\ them (that depends on the timing of --jobs), and a name's prefix before
\ it; so a run writes the same bytes with any --jobs. A key of such a
\ name is written as the canon name's, each such list sorted again. State
\ (one save at a time, as the driving task's): snap-outers.
begin-structure /outers
  field: outers-in      \ the stage's names: a key's name beyond them is the environment's
  field: outers-canon   \ the canon tier, or 0
  field: outers-list    \ one slot's names beyond, sorted (outers-room cells)
  field: outers-room
  field: outers-names   \ the names section joined with canon's (a block), or 0
  field: outers-bytes   \ and the name bytes section
  field: outers-unit    \ joining: a unit's bytes
end-structure
create snap-outers /outers allot  snap-outers /outers erase
: outers-in# ( -- n ) snap-outers outers-in @ ;
: canon ( -- tier ) snap-outers outers-canon @ ;
: outer ( -- tier ) lf-env-outer ;
: block-free ( addr -- ) @ ?dup if free drop then ;
: outers-free ( -- )
  canon ?dup if dup tier-free free drop then snap-outers outers-list block-free
  snap-outers outers-names block-free snap-outers outers-bytes block-free
  snap-outers /outers erase ;
: key-beyond? ( key -- flag ) key-name outers-in# u< 0= ;
\ Whether slot's list ends with a name beyond (such keys are its last).
: slot-outer? ( slot -- flag )
  canon 0= if drop false exit then
  dup lf-slot-looked @ ?dup 0= if drop false exit then
  1- swap lf-slot-look drop key-beyond? ;
\ The content order of two names of the environment's tier: -1, 0 or 1.
: u-order ( u1 u2 -- n ) 2dup u> >r u< r> - ;
: part-order ( a b -- n )
  over outer name-tag@ over outer name-tag@ 2dup <> if u-order nip nip exit then 2drop
  over outer name-tag@ tag-name-str =
  if swap outer name-text@ rot outer name-text@ compare
  else swap outer name-number@ swap outer name-number@ u-order then ;
: o-level ( n d i -- part ) - outer name-up ;
: o-order ( a b -- n )
  over outer name-depth over outer name-depth 2dup min 1+ 0 ?do
    3 pick 2 pick i o-level 3 pick 2 pick i o-level
    i if part-order else u-order then ?dup if >r 2drop 2drop r> unloop exit then
  loop u-order nip nip ;
\ Cells at addr: sorted by o-order, by insertion.
: cell-swap ( addr -- ) dup 2@ swap rot 2! ;
: o-sink ( addr j -- )
  begin dup while
    2dup 1- cells + dup 2@ swap o-order 0> 0= if drop 2drop exit then cell-swap 1-
  repeat 2drop ;
: o-sort ( addr n -- ) 1 max 1 ?do dup i o-sink loop drop ;
\ Slot's names beyond into the list (room for its every lookup), sorted,
\ and made in canon: ok or full.
: outers-hold ( n -- outcome )
  dup snap-outers outers-room @ > 0= if drop outcome-ok exit then
  snap-outers outers-list block-free 0 snap-outers outers-list !
  dup cells allocate if 2drop outcome-full exit then
  snap-outers outers-list ! snap-outers outers-room ! outcome-ok ;
: outer-put ( addr n name -- addr n' ) >r 2dup cells + r> swap ! 1+ ;
: outer-key ( addr n slot key -- addr n' slot )
  dup key-beyond? if key-name swap >r outer-put r> else drop then ;
: outers-of ( addr slot -- addr n )
  0 swap dup lf-slot-looked @ 0 ?do i over lf-slot-look drop outer-key loop drop ;
\ Name n of the environment's tier made canon's: n' and ok; or -1 and
\ invalid without the two tiers or for a number the environment's tier
\ does not hold, such as lf-look-outside's (review FRK F4: name-copy would
\ read past them), else name-copy's full or invalid.
: canon-name? ( name -- flag )
  outer 0<> canon 0<> and if outer tier-names cons-numbers u< else drop false then ;
: canon-copy ( name -- name' outcome )
  dup canon-name? if outer canon name-copy else drop -1 outcome-invalid then ;
: canon-made ( name -- outcome ) canon-copy nip ;
: canon-slot ( slot -- outcome )
  dup lf-slot-looked @ outers-hold ok-then? 0= if exit then
  snap-outers outers-list @ swap outers-of 2dup o-sort
  cells bounds ?do i @ canon-made dup ok? 0= if unloop exit then drop 1 cells +loop
  outcome-ok ;
: canon-slots ( snap -- outcome )
  dup snap-wn@ 0 ?do
    i over snap-e slot-env dup slot-outer? if canon-slot else drop outcome-ok then
    dup ok? 0= if nip unloop exit then drop
  loop drop outcome-ok ;
\ The canon tier over the stage's (when the environment has names of its
\ own, over that same tier), its names made: ok, full or invalid.
: canon-tier ( stage -- outcome )
  stage-tier /tier allocate if 2drop outcome-full exit then
  dup snap-outers outers-canon ! tier-extend ;
: outer-same? ( stage -- flag )
  stage-tier tier-names cons-numbers outer tier-names cons-first @ = ;
: canon-build ( snap stage -- outcome )
  dup stage-tier tier-names cons-numbers snap-outers outers-in !
  outer 0= if 2drop outcome-ok exit then
  dup outer-same? 0= if 2drop outcome-invalid exit then
  canon-tier dup ok? if drop canon-slots else nip then ;
\ The names and name bytes sections joined with canon's (tier-joined!):
\ blocks of the section's units (outers-unit bytes each), then canon's,
\ its strings' offsets moved past the stage's bytes.
: au ( -- au ) snap-outers outers-unit @ ;
: join-units ( a0 n0 a1 n1 -- blk n outcome )
  2 pick over + dup au * 1 max allocate if 2drop 2drop 2drop 0 0 outcome-full exit then
  2>r 2swap au * 2r@ nip swap dup >r move
  au * r> 2r@ nip + swap move 2r> swap outcome-ok ;
: canon# ( -- n ) canon tier-names cons-records slab-count ;
: canon-part ( blk n -- addr n1 ) canon# - /quad * + canon# ;
: stage-bytes# ( stage -- n ) stage-tier tier-names cons-bytes slab-count ;
: offsets-moved ( addr n by -- )
  -rot /quad * bounds ?do
    i quad-head u32@ head-tag tag-name-str = if dup i quad-b u32@ + i quad-b u32! then
  /quad +loop drop ;
: names-joined ( snap stage -- outcome )
  /quad snap-outers outers-unit ! over snap-tf 2 swap tf-data
  canon tier-names cons-records tf-slab-data join-units ok-then2? 0= if nip nip exit then
  over snap-outers outers-names ! 2dup canon-part 4 pick stage-bytes# offsets-moved
  2 4 pick snap-tf tier-joined! 2drop outcome-ok ;
: bytes-joined ( snap -- outcome )
  1 snap-outers outers-unit ! dup snap-tf 1 swap tf-data
  canon tier-names cons-bytes tf-slab-data join-units ok-then2? 0= if nip exit then
  over snap-outers outers-bytes ! 1 3 pick snap-tf tier-joined! drop outcome-ok ;
: outers-joined ( snap stage -- outcome )
  canon 0= if 2drop outcome-ok exit then canon# 0= if 2drop outcome-ok exit then
  over swap names-joined dup ok? if drop bytes-joined else nip then ;
\ Both, before the tier's sections are added.
: snap-outers! ( snap stage -- outcome )
  2dup swap snap-tf tf-stage ! 2dup canon-build dup ok? 0= if nip nip exit then drop
  outers-joined ;
\ A key as written: a name beyond the input made canon's (key' ok), or -1
\ and canon-copy's failure; the outcome is passed up to snap-save.
: canon-key ( key -- key' outcome )
  dup key-kind swap key-name canon-copy ok-then? 0= if nip no-result exit then
  lf-look-kinds * + outcome-ok ;
: key-written ( key -- key' outcome ) dup key-beyond? if canon-key else outcome-ok then ;
\ The key at addr as written: ok, or the failure with nothing written.
: look-written ( addr key -- outcome )
  key-written ok-then? if swap u32-le! outcome-ok else nip then ;
: put-look ( addr snap slot k -- addr' snap slot outcome )
  over lf-slot-look 3 pick answer-renum 4 pick 4 + u32-le! 3 pick swap look-written
  >r rot 8 + -rot r> ;
\ A slot's lookups from addr on: the end and ok, or the first failure.
: looks-put ( addr snap slot -- addr' snap slot outcome )
  outcome-ok over lf-slot-looked @ 0 ?do
    drop i put-look dup ok? 0= if unloop exit then
  loop ;
: put-looks ( addr d snap -- addr' outcome )
  over slot-env dup slot-outer? >r lf-slot-looked @ >r 2 pick >r
  swap slot-env looks-put nip nip r> r> r> if look-sort else 2drop then ;
\ Slot d's dependencies and lookups, after the lists' ends so far.
: put-pair ( dblk snap lblk d -- dblk' snap lblk' outcome )
  >r rot r@ 3 pick put-deps -rot r> 2 pick put-looks ;
: put-lists ( snap -- outcome )
  dup ss-deps swap snap-block swap dup ss-looks swap snap-block
  over snap-wn@ outcome-ok swap 0 ?do
    drop i 2 pick snap-e put-pair dup ok? 0= if nip nip nip unloop exit then
  loop nip nip nip ;
: put-sites ( snap -- outcome )
  >r site-bytes dup slab-count dup 1 max allocate
  if drop 2drop r> drop outcome-full exit then
  rot slab-base over 3 pick move swap ss-sites r@ snap-block! ss-sites r> snap-own
  outcome-ok ;
: put-rest ( snap -- outcome ) dup put-lists dup ok? if drop put-sites else nip then ;

\ The header fields, then every section, then the file.
: head! ( u k snap -- ) snap-sf sections-field! drop ;
\ A SHA-256 as eight fields from k on, its bytes in order.
: sum-heads! ( c-addr k snap -- )
  8 0 do 2 pick i u32s + u32-le@ 2 pick i + 2 pick head! loop 2drop drop ;
\ A layer (ADR 0020 amendment 1, F5; plan step SN4), set after
\ snap-begin: its base's identity (the base's header SHA-256) and the
\ first number of each tier section 1-8 in the base (8 cells), written to
\ the header and the identity; the n slots written, slot j the
\ environment's slot which ( j -- d ), the slots they refer to numbered
\ by renum ( d -- s ) in the base and the layer; the declarations and
\ their lines written (decls n lines; import/snapshot-tier.fs tier-given!).
: snap-layer-base! ( sha-addr firsts snap -- )
  true over snap-layered ! rot over snap-base-sha 32 move
  8 0 do over i cells + @ si-firsts i + 2 pick id! loop
  over swap snap-tf tf-from cell+ 7 cells move drop ;
: snap-layer-slots! ( n which renum snap -- )
  tuck snap-renum ! tuck snap-which ! snap-wn ! ;
: snap-layer-decls! ( decls n lines snap -- ) snap-tf tier-given! ;
: snap-head! ( fuel snap -- )
  >r snap-mark sh-mark r@ head! snap-version sh-version r@ head!
  lf-verdict-version sh-verdict r@ head!
  dup u32-mask and sh-fuel r@ head! cell-hi sh-fuel 1+ r@ head!
  lf-allowlist-version sh-allow-version r@ head! lf-allowlist-bits sh-allow-bits r@ head!
  r@ snap-layered @ if 1 sh-layers r@ head! r@ snap-base-sha sh-base r@ sum-heads! then
  r> drop ;
: snap-count ( i snap -- n ) over snap-unit >r snap-size r> / ;
: snap-shape ( i snap -- addr unit count )
  2dup snap-block >r 2dup snap-count >r drop snap-unit r> r> -rot ;
: snap-add ( i snap -- outcome )
  2dup snap-shape 2>r >r over 1+ swap snap-sf r> -rot 2r> 2swap sections-add nip ;
: snap-adds ( snap -- outcome )
  snap-sections# tier-sections# do
    i over snap-add dup ok? 0= if nip unloop exit then drop
  loop drop outcome-ok ;
\ A sealed stage, and the current environment valid over this context's
\ input (which the caller fed from that stage: one slot per input
\ declaration, in the feed's order), every slot final.
: snap-ready? ( stage -- flag )
  stage-sealed? lf-env-current if lf-slots-final? else false then and ;
: snap-build ( fuel stage snap -- outcome )
  over snap-ready? 0= if drop 2drop outcome-invalid exit then
  >r r@ snap-which @ 0= if lf-env lf-env-length r@ snap-wn ! then
  r@ over snap-outers! dup ok? 0= if nip nip r> drop exit then drop
  r@ snap-tf tier-sections dup ok? 0= if nip r> drop exit then drop
  r@ snap-head! r@ snap-lists dup ok? 0= if r> drop exit then drop
  r@ put-slots dup ok? 0= if r> drop exit then drop
  r@ put-rest dup ok? 0= if r> drop exit then drop r> snap-adds ;
\ Write the snapshot of the current environment over the sealed stage
\ to the file named c-addr u, after snap-begin and the caller's
\ snap-export!, snap-manifest-sha!, snap-manifest!, snap-info! and
\ snap-facts!: ok, invalid when a slot is not final, the stage is not
\ the environment's or a lookup's name beyond the input is none of the
\ environment's tier (canon-copy), full for no heap, or the container's
\ outcome; the file is untouched unless ok. snap-free frees the record's
\ blocks.
: snap-save ( c-addr u fuel stage snap -- outcome )
  sites-init dup ok? 0= if >r 2drop 2drop drop r> sites-free exit then drop
  snap-outers /outers erase dup >r snap-build r> swap sites-free
  dup ok? if drop snap-sf sections-write else nip nip nip then outers-free ;

\ ---- Loading: the header, the table, the identity.
: head@ ( k snap -- u ) snap-sf sections-field@ 0= if 0 then ;
\ The snapshot's fuel per declaration.
: snap-fuel ( snap -- n ) sh-fuel over head@ swap sh-fuel 1+ swap head@ hi-cell ;
: snap-marked? ( snap -- flag ) sh-mark swap head@ snap-mark = ;
: snap-current? ( snap -- flag ) sh-version swap head@ snap-version = ;
: snap-verdict ( snap -- n ) sh-verdict swap head@ ;
\ This build's verdict version; for a base, an older one inside the
\ window (verdict-version.fs lf-verdict-carried?), which marks the record
\ (snap-carry): the caller carries its results where the steps since cannot
\ reach and checks the rest (kernel/env-import.fs, plan step 6.2.5c3);
\ or (snap-stale-allowed) any older one, which marks the record stale. A
\ layer of an older version is stale or refused until plan step 6.2.5c7.
: snap-older? ( snap -- flag ) snap-verdict 1 lf-verdict-version within ;
: snap-carried? ( snap -- flag )
  dup snap-expect @ 0= swap snap-verdict lf-verdict-carried? and ;
: snap-beyond? ( snap -- flag )
  dup snap-older? snap-stale-allowed @ and dup rot snap-stale ! ;
: snap-fresh? ( snap -- flag )
  dup snap-verdict lf-verdict-version = if drop true exit then
  dup snap-carried? if true swap snap-carry ! true exit then snap-beyond? ;
: snap-allowed? ( snap -- flag )
  dup sh-allow-version swap head@ lf-allowlist-version =
  swap sh-allow-bits swap head@ lf-allowlist-bits = and ;
: snap-fuel? ( snap -- flag ) dup snap-asked @ dup 0< if 2drop true else swap snap-fuel =
  then ;
\ A base (snap-expect 0): no layer field (7-15) set. A layer loaded on a
\ base (snap-expect, the base's identity; plan step SN4): field 7 is 1 (a
\ layer on a base alone) and 8-15 the base's header SHA-256.
: snap-base? ( snap -- flag ) false 16 sh-layers do over i swap head@ or loop nip 0<> ;
: sum-head? ( c-addr k snap -- flag )
  true 8 0 do 3 pick i u32s + u32-le@ 3 pick i + 3 pick head@ = and loop nip nip nip ;
: snap-layer-of? ( snap -- flag )
  sh-layers over head@ 1 = swap dup snap-expect @ sh-base rot sum-head? and ;
: snap-header ( snap -- outcome )
  dup snap-marked? 0= if outcome-invalid c" not a LeanForth snapshot" rot snap-refuse exit
  then
  dup snap-current? 0= if outcome-unsupported c" format version" rot snap-refuse exit then
  dup snap-fresh? 0= if outcome-unsupported c" verdict version" rot snap-refuse exit then
  dup snap-fuel? 0= if outcome-invalid c" fuel" rot snap-refuse exit then
  dup snap-allowed? 0= if outcome-invalid c" axiom allowlist" rot snap-refuse exit then
  dup snap-expect @ if
    dup snap-layer-of? 0= if
      outcome-invalid c" base snapshot of the layer" rot snap-refuse exit then
  else dup snap-base? if outcome-unsupported c" layer" rot snap-refuse exit then then
  drop outcome-ok ;
\ The table: the tier's ten sections (tier-read checks them) and these.
: snap-shaped? ( i snap -- flag )
  over swap snap-sf sections-info 2drop rot dup snap-unit rot = -rot 1+ = and ;
: snap-table? ( snap -- flag )
  dup snap-sf sections-count snap-sections# <> if drop false exit then
  true snap-sections# tier-sections# do over i swap snap-shaped? and loop nip ;
\ Section i read whole into a new block the record owns: ok, full, or
\ invalid (damaged).
: snap-length ( i snap -- u ) snap-sf sections-info nip nip nip ;
: snap-load ( i snap -- outcome )
  2dup snap-length dup 1 max allocate if drop 2drop drop outcome-full exit then
  swap 2over snap-block! 2dup snap-own
  2dup snap-block >r 2dup snap-length >r snap-sf r> r> 2swap >r >r swap r> r>
  sections-read snap-damaged ;
: snap-identity ( snap -- outcome )
  ss-identity over snap-length si-fields# u32s <> if drop outcome-invalid exit then
  ss-identity swap snap-load ;
\ The header's SHA-256, the file's identity, read from the file.
: sum-read ( fid snap -- outcome )
  >r dup sections-align 32 - 0 rot reposition-file if drop r> drop outcome-invalid exit
  then
  r> snap-sum 32 rot read-file swap 32 <> or if outcome-invalid else outcome-ok then ;
: snap-sum-read ( c-addr u snap -- outcome )
  >r r/o bin open-file if drop r> drop outcome-invalid exit then
  dup r> sum-read swap close-file drop ;
\ The first number of each tier section 1-8 (identity 21-28): 0 in a
\ base; in a layer, the base's counts (snap-expect-firsts, 8 cells).
: firsts-zero? ( snap -- flag ) false 29 si-firsts do over i swap id@ or loop nip 0= ;
: firsts-same? ( snap -- flag )
  true 8 0 do
    over si-firsts i + swap id@ 2 pick snap-expect-firsts @ i cells + @ = and
  loop nip ;
: snap-checks ( snap -- outcome )
  dup snap-header dup ok? 0= if nip exit then drop
  dup snap-table? 0= if outcome-invalid c" section table" rot snap-refuse exit then
  dup snap-identity dup ok? 0= if c" identity" rot snap-refuse exit then drop
  dup snap-expect @ if
    dup firsts-same? 0= if outcome-invalid c" base snapshot of the layer" rot snap-refuse
      exit then
  else dup firsts-zero? 0= if outcome-unsupported c" layer" rot snap-refuse exit then then
  drop outcome-ok ;
\ Open the snapshot file c-addr u for a run with fuel per declaration
\ (-1: the snapshot's): its header, table and identity checked.
: snap-opened ( c-addr u fuel snap -- outcome )
  tuck snap-asked ! >r 2dup r@ snap-sf sections-open snap-damaged
  dup ok? 0= if nip nip c" header or section table" r> snap-refuse exit then drop
  r@ snap-sum-read dup ok? 0= if c" header" r> snap-refuse exit then drop r> snap-checks ;
: snap-open ( c-addr u fuel snap -- outcome ) dup snap-init snap-opened ;
\ Open a layer (plan step SN4) for the base whose identity (its header's
\ SHA-256) is at sha and whose tier counts are firsts (8 cells): a layer
\ written on that base alone, or refused (invalid).
: snap-layer-open ( c-addr u fuel sha firsts snap -- outcome )
  dup snap-init tuck snap-expect-firsts ! tuck snap-expect ! snap-opened ;
\ The tier into a fresh stage (stage-init's), as import/snapshot-tier.fs
\ reads it.
: snap-tier ( stage snap -- outcome )
  2dup snap-tf tier-read snap-damaged
  >r swap stage-tier tier-names cons-numbers swap snap-names ! r> ;

\ ---- Loading: the environment's sections, every field in range.
: sec-units ( i snap -- n ) snap-sf sections-info drop nip nip ;
: snap-loads ( snap -- outcome )
  snap-sections# ss-slots do
    i over snap-load dup ok? 0= if nip unloop exit then drop
  loop drop outcome-ok ;
\ The identity's counts against the sections, and the slots against n.
: id-units? ( snap k i -- flag ) rot tuck sec-units >r id@ r> = ;
: snap-counts? ( n snap -- flag )
  >r r@ si-slots ss-slots id-units? swap si-slots r@ id@ = and
  r@ si-deps ss-deps id-units? and r> si-looks ss-looks id-units? and ;
: dep@ ( j snap -- d ) ss-deps swap snap-block swap u32s + u32-le@ ;
: look-key ( j snap -- key ) ss-looks swap snap-block swap 8 * + u32-le@ ;
: look-answer ( j snap -- answer ) ss-looks swap snap-block swap 8 * + 4 + u32-le@ ;
\ A slot's own fields: an outcome, marks, axiom bits within the
\ allowlist's; B4 warning bits, a recipe and a shape as the checker makes
\ them (review FRK F5); fuel used -1 (not known) or at most the fuel per
\ declaration; provenance at most 1 (rests on saved results) in a layer
\ (review rvSN3 m2, m3), and in a base 0 (written by a final run) or, in
\ a base written again by a run of an older one (plan step 6.2.5c5, R8),
\ also 1, 2 (taken from it) and 3; ADR 0020 Amendment 5's lineage
\ section (plan step 6.2.5c6) will tell such a base apart.
: sl-at ( addr k -- u ) swap fld@ ;
: outcome-in? ( u -- flag ) outcome-full u> 0= ;
\ The warning bits: inductive-block.fs's lf-warn-* (1-16) and quot.fs's
\ lf-warn-quot-record (32), all below this.
64 constant snap-warn-limit
\ A recipe (generated-recursor.fs lf-genrec-recipe): 0, raw, or raw and
\ large; or a nested block's count of auxiliary types shifted, with
\ neither bit. A shape: 0, or one the block check computed.
: recipe-low? ( bits -- flag )
  dup lf-recipe-large <> swap lf-recipe-raw lf-recipe-large or u> 0= and ;
: recipe-ok? ( u -- flag )
  dup lf-recipe-aux-shift rshift if 1 lf-recipe-aux-shift lshift 1- and 0= exit then
  recipe-low? ;
: shape-ok? ( u -- flag ) dup 0= swap lf-shape-known and 0<> or ;
: sl-made? ( addr -- flag )
  dup sl-warnings sl-at snap-warn-limit u< over sl-recipe sl-at recipe-ok? and
  swap sl-shape sl-at shape-ok? and ;
: sl-sane? ( addr -- flag )
  dup sl-outcome sl-at outcome-in? over sl-marks sl-at 8 u< and
  over sl-axioms sl-at snap-axiom-bits invert and 0= and swap sl-made? and ;
: fuel-ok? ( addr snap -- flag )
  snap-fuel swap sl-fuel swap fld2@ tuck < 0= swap -1 < 0= and ;
: snap-layer? ( snap -- flag ) sh-layers swap head@ 0<> ;
: prov-max ( snap -- u ) snap-layer? if 1 else prov-taken 1 or then ;
: prov-ok? ( addr snap -- flag ) prov-max swap sl-provenance swap fld@ u< 0= ;
\ Its site: none, or a counted string inside the site texts.
: site-room ( snap -- base size ) ss-sites over snap-block swap ss-sites swap snap-size ;
: site-ok? ( n snap -- flag )
  over 0= if 2drop true exit then
  site-room >r swap 1- r@ over u> 0= if r> drop 2drop false exit then
  tuck + count nip + 1+ r> u> 0= ;
\ Its lists inside their sections, by the counts so far and the
\ identity's totals, before any entry is read (review rvSN3 M1).
: lists-inside? ( addr snap -- flag )
  over sl-deps swap fld@ over si-deps swap id@ 2 pick snap-dk @ - u> 0=
  >r swap sl-looks swap fld@ over si-looks swap id@ rot snap-lk @ - u> 0= r> and ;
\ Its dependencies ascending, each below the first slot of its span; its
\ lookups' keys the one key of names beyond the input, or a name of the
\ tier with a known kind, the quotient's under the anonymous name only
\ (rvSN3 m5); each answer an outcome and a slot below that first slot.
\ (Their order and distinctness are compared after publishing:
\ snap-same?.)
: dep-ok? ( prev dep snap -- dep flag ) snap-head @ over > >r tuck < r> and ;
: dep-step ( prev flag snap j -- dep flag' snap )
  over dep@ swap rot >r dup >r dep-ok? r> swap r> and swap ;
: deps-ok? ( c snap -- flag )
  swap >r -1 true rot r> 0 ?do dup snap-dk @ i + dep-step loop drop nip ;
: key-quot-ok? ( key -- flag ) dup key-kind lf-look-quot <> swap key-name 0= or ;
: key-ok? ( key snap -- flag )
  over lf-look-outside = if 2drop true exit then
  over key-name swap snap-names @ u< over key-kind lf-look-quot u> 0= and
  swap key-quot-ok? and ;
\ An answer's low bits: an outcome, or the holder bit with ok (a
\ generated recursor's holder: environment.fs lf-look-holder-answer).
: answer-low? ( answer -- flag )
  lf-look-kinds 1- and dup outcome-in? swap lf-look-holder = or ;
: answer-ok? ( answer snap -- flag )
  snap-head @ swap dup answer-low? >r lf-look-slot+1 < 0= r> and ;
: looks-ok? ( c snap -- flag )
  true rot 0 ?do
    over dup snap-lk @ i + swap 2dup look-key over key-ok? >r look-answer
    2 pick answer-ok?
    r> and and
  loop nip ;
: slot-lists? ( addr snap -- flag )
  2dup lists-inside? 0= if 2drop false exit then
  over sl-deps swap fld@ over deps-ok? >r swap sl-looks swap fld@ swap looks-ok? r> and ;
: slot-fields? ( addr snap -- flag )
  over sl-sane? >r 2dup fuel-ok? >r 2dup prov-ok? >r
  swap sl-site swap fld@ swap site-ok? r> r> r> and and and ;
: slot-fine? ( addr snap -- flag )
  2dup slot-fields? if slot-lists? else 2drop false then ;
\ The slot's place: its span's first slot, where its lists start.
\ (A layer's slots are numbered on from its base's: snap-first.)
: span-head! ( d snap -- )
  2dup snap-slot sl-marks swap fld@ mark-with and if 2drop exit then
  tuck snap-first @ + swap snap-head ! ;
: start! ( d snap -- )
  dup snap-starts @ rot 2* cells + >r dup snap-dk @ r@ ! snap-lk @ r> cell+ ! ;
: slot-pass ( addr snap -- )
  over sl-deps swap fld@ over snap-dk +! swap sl-looks swap fld@ swap snap-lk +! ;
: slot-read ( d snap -- flag )
  2dup span-head! 2dup start! tuck snap-slot swap 2dup slot-fine? >r slot-pass r> ;
: snap-slot-bad ( d snap -- outcome ) c" slots" -rot snap-note outcome-invalid ;
: slots-read ( snap -- outcome )
  dup snap-n @ 0 ?do i over slot-read 0= if i swap snap-slot-bad unloop exit then loop
  dup snap-dk @ over si-deps swap id@ = swap dup snap-lk @ swap si-looks swap id@ = and
  flag>outcome ;
: starts-alloc ( n snap -- outcome )
  swap 2* cells 1 max allocate if 2drop outcome-full exit then
  swap snap-starts ! outcome-ok ;
\ Read the environment's sections of an opened snapshot whose tier was
\ read (snap-tier), n the stage's declarations.
: snap-read ( n snap -- outcome )
  2dup snap-n ! 2dup starts-alloc dup ok? 0= if nip nip exit then drop
  dup snap-loads dup ok? 0= if c" sections" rot snap-refuse nip exit then drop
  tuck snap-counts? 0= if outcome-invalid c" counts" rot snap-refuse exit then
  slots-read ;

\ ---- Publishing what was read: snap-fill is the check word of the
\ publisher's serial steps (env-publish.fs lf-env-step), run in a
\ development environment (lf-env-develop) with snap-loading the record.
: snap@ ( -- snap ) snap-loading @ ;
: saved ( k d -- u ) snap@ snap-slot fld@ ;
: saved2 ( k d -- n ) snap@ snap-slot fld2@ ;
: start@ ( d -- dk lk ) 2* cells snap@ snap-starts @ + 2@ swap ;
: fill-looks ( d -- )
  dup start@ nip swap sl-looks swap saved 0 ?do
    dup i + snap@ look-answer over i + snap@ look-key lf-env-look!
  loop drop ;
: fill-deps ( d -- flag )
  dup start@ drop swap sl-deps swap saved true swap 0 ?do
    over i + snap@ dep@ lf-env-depend ok? and
  loop nip ;
\ The span: the slot and every next one of the snapshot published with it.
: with-next? ( d -- flag )
  dup snap@ snap-n @ < if sl-marks swap saved mark-with and 0<> else drop false then ;
: fill-span ( d -- n ) 1 begin 2dup + with-next? while 1+ repeat nip ;
: fill-shapes ( d n -- ) 0 ?do sl-shape over i + saved i lf-env-shape! drop loop drop ;
: fill-marks ( d -- )
  sl-marks over saved dup mark-skipped and 0<> lf-env-skipped! mark-added and 0<>
  lf-env-added!
  sl-warnings over saved lf-env-warnings! sl-recipe over saved lf-env-recipe!
  sl-axioms swap saved lf-env-axiom! ;
: snap-fill ( -- )
  lf-env-limit dup fill-looks lf-env-saved!
  dup fill-deps 0= if drop outcome-invalid lf-env-finish exit then
  dup fill-marks dup fill-span dup lf-env-span! over swap fill-shapes
  sl-outcome swap saved lf-env-finish ;
\ After the run, every slot as saved: the outcome, axiom bits, warnings,
\ recipe, shape, marks (skipped, added, its span), its lists in order,
\ and published from the snapshot. Else invalid, the slot noted.
create same-fields
  sl-outcome , ' lf-slot-outcome ,  sl-axioms , ' lf-slot-axioms ,
  sl-warnings , ' lf-slot-warnings ,  sl-recipe , ' lf-slot-recipe ,
  sl-shape , ' lf-slot-shape ,  sl-deps , ' lf-slot-count ,  sl-looks , ' lf-slot-looked ,
here same-fields - 2 cells / constant same-fields#
: field-same? ( d slot entry -- flag ) dup cell+ @ rot swap execute @ >r @ swap saved r> =
  ;
\ The first n of them (the first five: a check's answer fields, I3).
: fields-upto? ( d slot n -- flag )
  true swap 0 ?do same-fields i 2* cells + 2over rot field-same? and loop nip nip ;
: fields-same? ( d slot -- flag ) same-fields# fields-upto? ;
: deps-same? ( d slot -- flag )
  swap start@ drop swap dup lf-slot-count @ true swap 0 ?do
    2 pick i + snap@ dep@ i 3 pick lf-dep-at = and
  loop nip nip ;
: looks-same? ( d slot -- flag )
  swap start@ nip swap dup lf-slot-looked @ true swap 0 ?do
    2 pick i + snap@ 2dup look-answer >r look-key r> i 4 pick lf-slot-look d= and
  loop nip nip ;
: marks-same? ( d slot -- flag ) slot-marks swap sl-marks swap saved = ;
\ What a user's check can read of a slot (plan step 6.2.5c4, I3): outcome,
\ axiom set, warnings, recipe, shape (the first five) and marks.
: alike? ( d slot -- flag ) 2dup 5 fields-upto? if marks-same? else 2drop false then ;
: slot-same? ( d -- flag )
  dup slot-env 2dup fields-same? >r 2dup deps-same? >r 2dup looks-same? >r
  dup lf-slot-saved @ 0<> >r marks-same? r> and r> and r> and r> and ;
: snap-same? ( snap -- outcome )
  dup snap-n @ 0 ?do
    i slot-same? 0= if c" slot published otherwise" i rot snap-note
      outcome-invalid unloop exit then
  loop drop outcome-ok ;

\ ---- What reports read of a loaded snapshot.
\ Declaration d's saved diagnostic into step (a run-record.fs /rr-step,
\ its site a counted string in the site texts, valid until snap-free),
\ and its fuel used.
: snap-site ( n -- c-addr|0 ) ?dup if 1- ss-sites snap@ snap-block + else 0 then ;
: snap-fact ( d step -- fuel )
  >r sl-code over saved r@ kept-code ! sl-first over saved2 r@ kept-first !
  sl-second over saved2 r@ kept-second ! sl-step over saved r@ kept-step !
  sl-site over saved snap-site r@ kept-site ! sl-outcome over saved r> kept-outcome !
  sl-fuel swap saved2 ;
: snap-export-sha ( snap -- c-addr ) si-export swap id-sha ;
: snap-manifest-sha ( snap -- c-addr ) si-manifest swap id-sha ;
: snap-export-bytes ( snap -- n ) si-bytes swap snap-id fld2@ ;
: snap-export-lines ( snap -- n ) si-lines swap snap-id fld2@ ;
: snap-flags ( snap -- u ) dup snap-id if si-flags swap id@ else drop 0 then ;
: snap-info ( snap -- c-addr u ) ss-info over snap-block swap ss-info swap snap-size ;

base !   \ the BASE this file was loaded with

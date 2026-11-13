\ Unit tests of the input tier saved and loaded (src/import/snapshot-tier.fs;
\ ADR 0020, plan step SN2): every pinned reference export (manifest
\ checked) and the other fixture exports staged, sealed and saved, the
\ file loaded into a second stage at other heap addresses (an allocation
\ in between), sealed and saved again: every section's slab, the
\ name-to-declaration array and the marks equal record by record, the two
\ files byte for byte; both stages fed to the checker (cli/check-run.fs)
\ give the same verdict and fuel for every declaration. The planted
\ faults, each a file whose SHA-256s are made again so that only the
\ record checks can refuse it, refused with its outcome, the stage rolled
\ back to empty: a child pointing forward, a wrong data word, a tag out
\ of range, a list longer than its section, a text's or name's byte
\ offset other than the next one of its pool or past it, a declaration
\ missing its value, a chain pointing forward, a constant's payload kept
\ non-zero, a mark kept, a family's count other than its section's, a
\ record equal to an earlier one, a letE's body record changed, another
\ first name, lines going back, another format version, a section's
\ byte changed (rejected), a cut file, a heap that refuses (full), a
\ table that may not grow (full), and the misuses: saving a stage not
\ sealed, loading into a stage read before. Every heap block is given
\ back (heap-watch.fs). tests/core/test_stage.py covers loading in
\ another process and stage-continue. Scratch files go to LF_TEST_SCRATCH's
\ folder, else /tmp (tests/support/scratch.fs).
include ../support/tester.fs
include ../support/scratch.fs
include ../support/heap-watch.fs
require ../../src/main.fs
decimal

: must ( flag -- ) 0= abort" snapshot-tier test: refused" ;
live-blocks @ constant blocks-at-start
create sa /stage allot  sa /stage erase
create sb /stage allot  sb /stage erase
create tf /tier-file allot  tf tier-file-init
s" lf-snapshot-tier-a.bin" scratch-file 2constant file-a
s" lf-snapshot-tier-b.bin" scratch-file 2constant file-b
s" lf-snapshot-tier-c.bin" scratch-file 2constant file-c
: composition ( -- c-addr u ) s" tests/reference/composition.ndjson" ;
: fixture ( -- c-addr u ) s" tests/reference/constant-fixture.ndjson" ;
: poly ( -- c-addr u ) s" tests/reference/poly-identity.ndjson" ;
: kinds ( -- c-addr u ) s" tests/core/reexport/kinds.ndjson" ;
: let-lambda ( -- c-addr u ) s" tests/core/check-declaration-cases/let-lambda.ndjson" ;

\ ---- Whole files (the blocks are freed by the caller).
: slurp ( c-addr u -- addr n )
  r/o bin open-file throw >r r@ file-size throw drop dup allocate throw swap
  2dup r@ read-file throw drop r> close-file throw ;
: spit ( addr n c-addr u -- ) w/o bin create-file throw >r r@ write-file throw r> close-file throw ;
: files= ( -- flag )
  file-a slurp file-b slurp 2over 2over compare 0= >r drop free throw drop free throw r> ;

\ ---- Two stages compared: every section's slab, the array, the marks.
: slab= ( s1 s2 -- flag )
  over slab-count over slab-count <> if 2drop false exit then
  over slab-used-bytes >r 0 rot slab-at 0 rot slab-at r> tuck compare 0= ;
: section= ( i -- flag ) dup sa tier-slab swap sb tier-slab slab= ;
: stages= ( -- flag )
  true tier-sections# 1 do i section= and loop
  sa stage-by-name sb stage-by-name slab= and sa stage-marks @ sb stage-marks @ = and ;

\ ---- A round trip: A staged and saved; B loaded from the file elsewhere
\ in the heap, sealed and saved again.
variable gap
: stage-a ( c-addr u checked? -- outcome )
  >r 16 sa stage-init ok? must r> if sa stage-load else sa stage-load-unchecked then ;
: save-a ( -- outcome ) file-a sa tf tier-save ;
: fresh-b ( -- ) 4000 allocate throw gap !  16 sb stage-init ok? must ;
: load-b ( -- outcome ) fresh-b file-a sb tf tier-load ;
: both-free ( -- ) sa stage-free sb stage-free gap @ free throw ;
: round ( c-addr u checked? -- a save load seal save same? files? )
  stage-a save-a load-b sb stage-seal file-b sb tf tier-save stages= files= both-free ;
T{ composition true round -> 0 0 0 0 0 true true }T
T{ fixture true round -> 0 0 0 0 0 true true }T
T{ s" tests/reference/identity.ndjson" true round -> 0 0 0 0 0 true true }T
T{ poly true round -> 0 0 0 0 0 true true }T
T{ s" tests/reference/type-identity.ndjson" true round -> 0 0 0 0 0 true true }T
T{ s" tests/core/ndjson-block.ndjson" false round -> 0 0 0 0 0 true true }T
T{ kinds false round -> 0 0 0 0 0 true true }T
T{ s" tests/core/stage-cases/marks.ndjson" false round -> 0 0 0 0 0 true true }T
T{ s" tests/core/stage-cases/unref.ndjson" false round -> 0 0 0 0 0 true true }T
T{ s" tests/core/check-declaration-cases/composition-literal.ndjson" false round
   -> 0 0 0 0 0 true true }T
T{ let-lambda false round -> 0 0 0 0 0 true true }T
T{ s" tests/core/check-declaration-cases/let-nondep.ndjson" false round
   -> 0 0 0 0 0 true true }T
T{ s" tests/core/check-declaration-cases/swap-max-far.ndjson" false round
   -> 0 0 0 0 0 true true }T
\ The marks of mdata declarations are made again when the loaded stage is
\ sealed (the file holds none).
T{ s" tests/core/stage-cases/marks.ndjson" false stage-a sa stage-marks @ 0> sa stage-free
   -> 0 true }T
\ Metadata naming other versions (read after stage-any-version!): its five
\ texts saved and given back by the loaded stage.
s" lf-snapshot-tier-other.ndjson" scratch-file 2constant other-file
: meta-start ( -- c-addr u )
  s\" {\"meta\":{\"exporter\":{\"name\":\"otherexport\",\"version\":\"9.9.9\"}," ;
: meta-end ( -- c-addr u )
  s\" \"format\":{\"version\":\"3.1.0\"},\"lean\":{\"githash\":\"abc\",\"version\":\"4.99.0\"}}}\n" ;
: skip-line ( addr n -- addr' n' )
  begin dup while over c@ 10 <> while 1 /string repeat 1 /string then ;
: write-other ( -- )
  s" tests/reference/identity.ndjson" slurp over >r skip-line
  other-file w/o bin create-file throw >r meta-start r@ write-file throw
  meta-end r@ write-file throw r@ write-file throw r> close-file throw r> free throw ;
write-other
: stage-another ( -- outcome )
  16 sa stage-init ok? must true sa stage-any-version! other-file sa stage-load-unchecked ;
: meta-is? ( k c-addr u -- flag ) rot sb stage-meta-text compare 0= ;
\ Loaded only into a stage that reads any version, as the reader takes
\ such an export (review rvSN2 m2); else unsupported.
: load-b-any ( -- outcome ) fresh-b true sb stage-any-version! file-a sb tf tier-load ;
T{ stage-another save-a load-b both-free -> 0 0 outcome-unsupported }T
T{ stage-another save-a load-b-any sb stage-seal file-b sb tf tier-save stages= files=
   sb stage-other? 0 s" otherexport" meta-is? 3 s" 4.99.0" meta-is? both-free
   -> 0 0 0 0 0 true true true true true }T
T{ live-blocks @ blocks-at-start - -> 0 }T

\ ---- Both ways: the verdict and fuel of every declaration, the stage fed
\ as staged and as loaded from its file (cli/check-run.fs, one context).
20000000 constant fuel
2048 constant most-decls
create res-a most-decls 2* cells allot   create res-b most-decls 2* cells allot
: results-of ( addr -- n )
  ck-verdicts? must lf-input-count most-decls < must lf-input-count 0 ?do
    i lf-env-outcome over i 2* cells + !  i ck-fuel-of over i 2* 1+ cells + !
  loop drop lf-input-count ;
: tl-staged ( c-addr u -- outcome )
  12 ck-stage stage-init ok? must ck-stage tf tier-load
  dup ok? if drop ck-stage stage-seal then ;
: tl-load ( c-addr u -- outcome )
  tl-staged dup ok? if drop ck-stage-facts ck-feed-phase dup ok? if ck-input-facts then then
  dup ck-state ck-loaded ! ;
: same-results ( n1 n2 -- flag )
  over = if 2* cells >r res-a r@ res-b r> compare 0= else drop false then ;
: both-ways ( c-addr u checked? -- equal? n )
  fuel ck-start ck-load ok? must file-a ck-stage tf tier-save ok? must
  ck-check res-a results-of ck-release
  fuel ck-start file-a tl-load ok? must ck-check res-b results-of ck-release
  dup >r same-results r> ;
T{ composition true both-ways 0> -> true true }T
T{ fixture true both-ways 0> -> true true }T
T{ poly true both-ways 0> -> true true }T
T{ s" tests/core/ndjson-block.ndjson" false both-ways 0> -> true true }T
T{ kinds false both-ways 0> -> true true }T
T{ let-lambda false both-ways 0> -> true true }T
T{ s" tests/core/check-declaration-cases/composition-wrong-argument.ndjson" false
   both-ways 0> -> true true }T

\ ---- The planted faults, in a copy of kinds' file: a record changed,
\ its section's SHA-256 and the header's made again.
live-blocks @ constant blocks-before-faults
kinds false stage-a ok? must save-a ok? must
file-a slurp 2constant good
good nip allocate throw constant img
: fresh-img ( -- ) good img swap move ;
: slot ( i -- addr ) 64 * 96 + img + ;
: sec-off ( i -- u ) slot 16 + u32-le@ ;
: sec-len ( i -- u ) slot 24 + u32-le@ ;
: rec ( k i -- addr ) dup tier-unit rot * swap sec-off + img + ;
: poke ( u k i field -- ) >r rec r> + u32-le! ;
: peek ( k i field -- u ) >r rec r> + u32-le@ ;
sha256: hasher
: digest ( addr u dest -- ) >r hasher sha256-init hasher sha256-update r> hasher sha256-final ;
: resum ( i -- ) dup sec-off img + over sec-len rot slot 32 + digest ;
: reseal ( -- ) img 4064 img 4064 + digest ;
: forged ( i -- ) resum reseal ;
\ The stage after a refusal: empty, as fresh.
: fresh? ( stage -- flag )
  dup stage-state @ staging-empty = over stage-decls 0= and
  swap stage-tier dup tier-names cons-numbers 1 = swap tier-exprs cons-numbers 0= and and ;
: attempt ( -- outcome flag )
  img good nip file-c spit fresh-b file-c sb tf tier-load sb fresh? ;
: attempted ( -- outcome flag ) attempt sb stage-free gap @ free throw ;
\ Records of A to plant faults in: an application, a constant, a letE, a
\ definition, a max level.
: first-of ( tag -- e )
  sa stage-tier tier-exprs cons-numbers 0 ?do
    i sa stage-tier expr-tag@ over = if drop i unloop exit then
  loop drop -1 ;
tag-app first-of constant an-app
tag-const first-of constant a-const
tag-let first-of tag-let-nondep first-of max constant a-let
: first-def ( -- d )
  sa stage-decls 0 ?do i sa staged-kind@ kind-def = if i unloop exit then loop -1 ;
first-def constant a-def
: first-max ( -- l )
  sa stage-tier tier-levels cons-numbers 0 ?do
    i sa stage-tier level-tag@ tag-level-max = if i unloop exit then loop -1 ;
first-max constant a-max
T{ an-app 0> a-const 0> a-let 0> a-def 0< 0= a-max 0> -> true true true true true }T
\ Sections: 0 information, 2 names, 3 levels, 4 lists, 6 texts, 7
\ expressions, 8 declarations, 9 lines. Fields of a 16-byte record: 0 head,
\ 4 a, 8 b, 12 data; of a declaration: 0 head, 16 value, 28 chain; of a
\ text: 0 offset, 4 length.
T{ fresh-img attempted -> outcome-ok false }T          \ the copy itself loads
T{ fresh-img an-app an-app 7 4 poke 7 forged attempted -> outcome-invalid true }T
T{ fresh-img an-app 5 + an-app 7 8 poke 7 forged attempted -> outcome-invalid true }T
T{ fresh-img an-app 7 12 peek 1 xor an-app 7 12 poke 7 forged attempted
   -> outcome-invalid true }T
T{ fresh-img 31 an-app 7 0 poke 7 forged attempted -> outcome-invalid true }T
T{ fresh-img 7 a-max 3 0 poke 3 forged attempted -> outcome-invalid true }T
T{ fresh-img 4 sec-len 0 4 0 poke 4 forged attempted -> outcome-invalid true }T
T{ fresh-img 0 6 0 peek 1+ 0 6 0 poke 6 forged attempted -> outcome-invalid true }T
T{ fresh-img 5 sec-len 1+ 0 6 4 poke 6 forged attempted -> outcome-invalid true }T
T{ fresh-img 1 2 8 peek 1+ 1 2 8 poke 2 forged attempted -> outcome-invalid true }T
T{ fresh-img staged-none a-def 8 16 poke 8 forged attempted -> outcome-invalid true }T
T{ fresh-img a-def 3 + a-def 8 28 poke 8 forged attempted -> outcome-invalid true }T
T{ fresh-img tag-const 1 pack-head a-const 7 0 poke 7 forged attempted
   -> outcome-invalid true }T
T{ fresh-img a-def 8 0 peek staged-marked-bit or a-def 8 0 poke 8 forged attempted
   -> outcome-invalid true }T
T{ fresh-img 7 0 0 peek 1+ 7 0 0 poke 0 forged attempted -> outcome-invalid true }T
T{ fresh-img 2 0 0 peek 1+ 2 0 0 poke 0 forged attempted -> outcome-invalid true }T
T{ fresh-img 2 0 0 peek 1- 2 0 0 poke 0 forged attempted -> outcome-invalid true }T
T{ fresh-img 2 0 0 0 poke 0 forged attempted -> outcome-unsupported true }T
\ A level equal to an earlier one; a letE's body record; the first name;
\ the first line after the last.
: level-copy ( from to -- ) swap 3 rec swap 3 rec 16 move ;
T{ fresh-img a-max 1- a-max level-copy 3 forged attempted -> outcome-invalid true }T
T{ fresh-img tag-app a-let 1+ 7 0 poke 7 forged attempted -> outcome-invalid true }T
T{ fresh-img 1 0 2 12 poke 2 forged attempted -> outcome-invalid true }T
T{ fresh-img sa stage-decls 1- 9 0 peek 1+ 0 9 0 poke 9 forged attempted
   -> outcome-invalid true }T
\ Review rvSN2's findings, each a record the reader would refuse: a
\ natural literal's text not canonical decimal (m1: a leading zero); a
\ name's text not UTF-8 (m3: a byte $FF, its data word made again); a
\ declaration on the line of the one before that is not a member of its
\ block (m4); a constant's universe list holding no level; a
\ declaration's type the body record of a letE.
tag-nat first-of constant a-nat
: nat-text ( -- t ) a-nat 7 4 peek ;
: text-at ( t -- addr ) 6 0 peek 5 sec-off + img + ;
T{ a-nat 0> fresh-img nat-text text-at c@ char 3 = -> true true }T
T{ fresh-img char 0 nat-text text-at c! 5 forged attempted -> outcome-invalid true }T
: name-word ( k -- h )   \ the data word name-hash! gives name k as it is now
  dup 2 0 peek head-tag hash-fmix over 2 4 peek hash-step
  over 2 8 peek 1 sec-off + img + rot 2 0 peek head-payload hash-bytes hash-step ;
: name-at ( k -- addr ) 2 8 peek 1 sec-off + img + ;
T{ fresh-img 1 2 0 peek head-tag tag-name-str = -> true }T
T{ fresh-img $FF 1 name-at c! 1 name-word 1 2 12 poke 1 forged 2 forged attempted
   -> outcome-invalid true }T
T{ fresh-img a-def 1- 9 0 peek a-def 9 0 poke 9 forged attempted -> outcome-invalid true }T
\ A line that is none, first or later; a line going back (review FRI B7).
T{ fresh-img staged-none 0 9 0 poke 9 forged attempted -> outcome-invalid true }T
T{ fresh-img staged-none a-def 9 0 poke 9 forged attempted -> outcome-invalid true }T
T{ fresh-img staged-none sa stage-decls 1- 9 0 poke 9 forged attempted -> outcome-invalid true }T
T{ fresh-img a-def 1- 9 0 peek 1- a-def 9 0 poke 9 forged attempted -> outcome-invalid true }T
: levelled-const ( -- e )
  sa stage-tier tier-exprs cons-numbers 0 ?do
    i sa stage-tier expr-tag@ tag-const =
    if i sa stage-tier expr-b@ sa stage-tuples tuple-length if i unloop exit then then
  loop -1 ;
levelled-const constant a-levelled
T{ a-levelled 0> -> true }T
T{ fresh-img 1000000 a-levelled 7 8 peek 1+ 4 0 poke 4 forged attempted
   -> outcome-invalid true }T
T{ fresh-img a-let 1+ a-def 8 12 poke 8 forged attempted -> outcome-invalid true }T
\ A byte changed, the SHA-256s left: rejected; the file cut: invalid.
T{ fresh-img an-app 7 rec dup c@ 1 xor swap c! attempted -> outcome-rejected true }T
T{ fresh-img img good nip 1- file-c spit fresh-b file-c sb tf tier-load sb fresh?
   sb stage-free gap @ free throw -> outcome-invalid true }T
\ The failing record's section and number.
: why? ( -- flag record ) tf tier-file-error >r s" expressions" compare 0= r> ;
T{ fresh-img an-app an-app 7 4 poke 7 forged attempt 2drop why?
   sb stage-free gap @ free throw -> true an-app }T
\ No heap for a block while loading: full, rolled back, nothing kept.
: refused-at ( k -- outcome flag )
  fresh-b heap-refusals ! file-a sb tf tier-load sb fresh?
  0 heap-refusals ! sb stage-free gap @ free throw ;
T{ 3 refused-at -> outcome-full true }T
T{ 9 refused-at -> outcome-full true }T
\ A table that may not grow to its loaded size: full, not a hang.
: tiny-exprs ( -- )
  sb stage-tier tier-exprs cons-table dup htab-free 4 expr-class rot htab-init ok? must
  4 sb stage-tier tier-exprs cons-table htab-limit ;
: capped ( -- outcome flag )
  fresh-b tiny-exprs file-a sb tf tier-load sb fresh? sb stage-free gap @ free throw ;
T{ capped -> outcome-full true }T
\ A table that must grow: built once, at the size sealing gives the
\ records loaded (the smallest power of two at least twice as many, 16 at
\ least), so that sealing does not build it again.
: pow2 ( u -- p ) 1 begin 2dup u> while 2* repeat nip ;
: exprs-table ( stage -- cons ) stage-tier tier-exprs ;
: sized? ( -- flag )
  sb exprs-table dup cons-table htab-slots swap cons-numbers 2* 16 max pow2 = ;
: grown ( -- outcome flag )
  fresh-b sb exprs-table cons-table dup htab-free 4 expr-class rot htab-init ok? must
  file-a sb tf tier-load sized? sb stage-free gap @ free throw ;
T{ grown -> outcome-ok true }T
\ Misuse: saving a stage not sealed; loading into a stage read before.
T{ 16 sb stage-init s" tests/reference/identity.ndjson" sb stage-read file-b sb tf tier-save
   sb stage-free -> outcome-ok outcome-ok outcome-invalid }T
T{ 16 sb stage-init file-a sb tf tier-load file-a sb tf tier-load sb stage-state @
   sb stage-free -> outcome-ok outcome-ok outcome-invalid staging-filled }T
\ A tier of one declaration whose line is none (review of refactor-fri
\ L1): no later line is compared with it, so only the first line's check
\ refuses it. identity.ndjson's tier, saved, is copied into img.
sa stage-free
s" tests/reference/identity.ndjson" true stage-a ok? must save-a ok? must
T{ sa stage-decls -> 1 }T
file-a slurp 2constant one-good
: one-img ( -- ) one-good img swap move ;
: attempted-one ( -- outcome flag )
  img one-good nip file-c spit fresh-b file-c sb tf tier-load sb fresh?
  sb stage-free gap @ free throw ;
T{ one-img attempted-one -> outcome-ok false }T
T{ one-img staged-none 0 9 0 poke 9 forged attempted-one -> outcome-invalid true }T
one-good drop free throw
img free throw  good drop free throw  sa stage-free
T{ live-blocks @ blocks-before-faults - -> 0 }T

bye

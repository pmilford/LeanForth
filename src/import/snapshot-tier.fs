\ The input tier saved and loaded (ADR 0020 D1, D2, D4, D6; plan task
\ 6.2.5, step SN2). Untrusted [format][import] code, fail-closed;
\ LeanForth-specific (a stage's records). A sealed stage's five families
\ (import/stage.fs, core/compact*.fs), its declarations (32-byte records,
\ import/stage-records.fs) and their export lines become the first ten
\ sections of a sectioned file (lib/sections.fs), in this order (kind =
\ position + 1; unit size in bytes):
\   0 information (4)  1 name bytes (1)   2 names (16)   3 levels (16)
\   4 lists (4)        5 text bytes (1)   6 texts (8)    7 expressions (16)
\   8 declarations (32)                   9 lines (4)
\ The information section holds 15 32-bit fields: this format's version
\ (1), the unit count of sections 1 to 8 (the lines have one per
\ declaration), whether the metadata names other versions, and its five
\ texts (stage-other?, stage-meta-text), else 0. Every 32-bit field is
\ little-endian (lib/u32.fs; a section is one block where the host keeps
\ fields so, converted elsewhere). What a build derives is not written: a
\ constant's payload is written as 0 and a declaration's mdata mark as
\ clear, both computed again when the loaded stage is sealed; no hash
\ table, address or hash value is written except a name's stored hash,
\ its record's data word.
\
\ Loading (tier-read, or tier-load from a file) fills a stage that
\ stage-init made and nothing was read into. Each family's records are
\ read into its slab in one block, then entered in number order, each
\ checked as its builder checks it (ADR 0016 C8, the builders' own checks
\ in core/compact*.fs): tags and payloads in range; every child, prefix,
\ parameter name, list or text a smaller number of its family or of one
\ loaded before; the data word computed again and compared; a list
\ inside its section; a name's or text's bytes exactly the next ones of
\ its pool (so none lies past it and none is left over); no record equal
\ to an earlier one. The tables are built once, at their sealed size
\ (lib/cons.fs cons-load-room, cons-adopt). Each declaration is checked
\ as the stage checks a draft (fields present exactly for its kind and
\ records of the tier), its flags only its kind's, its codes and hint as
\ the reader gives them, its kind data as the handlers gather it (names,
\ numbers, recursor rules), its chain pointing back exactly to the newest
\ earlier declaration of its name; the name-to-declaration array is
\ built again from the chains. Lines never decrease. The stage is then
\ filled: stage-seal resolves the constants and marks the declarations,
\ or stage-continue reads another export into the tier. As for a read,
\ the feed checks that block members follow their block.
\
\ Outcomes (ADR 0008): ok; invalid for a malformed, damaged or forged
\ file (tier-file-error names the section and the record), a stage that
\ is not fresh (loading) or not sealed (saving); unsupported for another
\ format version (the container's or this one's); rejected for a section
\ whose SHA-256 differs; full for no heap or the stage's memory limit
\ (stage-limit!). A failed load, or a THROW (passed on), rolls the stage
\ back to empty. A matching SHA-256 shows the bytes are those written,
\ not who wrote them (ADR 0020 D4).
\
\ Example:
\   create lib /stage allot   create tf /tier-file allot
\   16 lib stage-init drop
\   s" tests/reference/constant-fixture.ndjson" lib stage-load drop
\   s" /tmp/fixture.tier" lib tf tier-save .      \ 0
\   lib stage-free  16 lib stage-init drop
\   s" /tmp/fixture.tier" lib tf tier-load .      \ 0
\   lib stage-seal . lib stage-decls .             \ 0 3
\   lib stage-free
\
\ Interface: /tier-file tier-file-init tier-sections tier-sections-free
\ tier-save tier-read tier-load tier-file-error tier-version
\ tier-sections#. tier-sections adds the ten sections to the record's
\ sectioned file (tf-sf) for a caller that writes more sections after
\ them; tier-read reads them from an opened one.
\ State: none of its own; a /tier-file record holds one file being written
\ or read (its sectioned-file record, the heap blocks it owns meanwhile,
\ the reason of a refusal), used by one task at a time. Loads in decimal
\ whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/outcome.fs
require ../lib/u32.fs
require ../lib/slab.fs
require ../lib/cons.fs
require ../lib/hash32.fs
require ../lib/sections.fs
require ../lib/bytes.fs
require ../lib/json.fs
require ../core/compact.fs
require ./stage.fs

1 constant tier-version
10 constant tier-sections#
\ Section positions the record checks name.
4 constant tp-lists  6 constant tp-texts  7 constant tp-exprs  8 constant tp-decls
9 constant tp-lines
\ The information fields.
0 constant ti-version  8 constant ti-decls  9 constant ti-other  10 constant ti-meta
15 constant ti-fields#
\ Each section's unit size, by position.
create tier-units 4 , 1 , 16 , 16 , 4 , 1 , 8 , 16 , /staged , 4 ,
: tier-unit ( i -- au ) cells tier-units + @ ;
\ 32-bit fields per unit (0 for a byte pool).
: tier-per-unit ( i -- n ) tier-unit 1 u32s / ;
\ The slab each section after the information comes from, or goes to.
: tf-name-bytes ( stage -- slab ) stage-tier tier-names cons-bytes ;
: tf-names ( stage -- slab ) stage-tier tier-names cons-records ;
: tf-levels ( stage -- slab ) stage-tier tier-levels cons-records ;
: tf-tuples ( stage -- slab ) stage-tier tier-tuples cons-records ;
: tf-text-bytes ( stage -- slab ) stage-tier tier-texts cons-bytes ;
: tf-texts ( stage -- slab ) stage-tier tier-texts cons-records ;
: tf-exprs ( stage -- slab ) stage-tier tier-exprs cons-records ;
create tier-slab-xts ' tf-name-bytes , ' tf-names , ' tf-levels , ' tf-tuples ,
  ' tf-text-bytes , ' tf-texts , ' tf-exprs , ' stage-decl-records , ' stage-lines ,
: tier-slab ( i stage -- slab ) swap 1- cells tier-slab-xts + @ execute ;
: tf-slab-data ( slab -- addr n ) 0 over slab-at swap slab-count ;
\ A family's set from its records slab (the table comes first in a set).
: records>cons ( slab -- cons ) 0 cons-records - ;
\ The section's name, for a refusal.
create tier-titles   \ counted strings, each aligned (lib/bytes.fs counted,)
  s" information" counted,  s" name bytes" counted,  s" names" counted,
  s" levels" counted,  s" lists" counted,  s" text bytes" counted,  s" texts" counted,
  s" expressions" counted,  s" declarations" counted,  s" lines" counted,
: tier-title ( i -- c-addr )
  dup tier-sections# u< 0= if drop c" section table" exit then
  tier-titles swap 0 ?do count + aligned loop ;

12 constant tf-blocks#   \ heap blocks one record may own: at most 7 are used
begin-structure /tier-file
  /sections +field tf-sf               \ the sectioned file
  field: tf-owned                      \ blocks owned (writing)
  tf-blocks# cells +field tf-blocks
  ti-fields# u32s +field tf-info       \ the information fields
  ti-fields# u32s +field tf-info-bytes \ and as little-endian bytes
  /quad +field tf-first                \ a family's first record (reading)
  field: tf-pos                        \ bytes of a pool used so far (reading)
  field: tf-why                        \ counted string: the section refused, or 0
  field: tf-at                         \ the number of the record refused, or -1
  field: tf-stage                      \ the stage written or read
  tier-sections# cells +field tf-from  \ writing: each section's first unit (a layer)
  2 cells +field tf-given              \ writing: the declarations given, addr n, or 0 0
  field: tf-given-lines                \ and their lines (n fields)
  tier-sections# 2* cells +field tf-joins  \ writing: a section's units given whole, or 0 0
end-structure
: tf-stage@ ( tf -- stage ) tf-stage @ ;
\ Section i's slab in the record's stage.
: tf-slab ( i tf -- slab ) tf-stage@ tier-slab ;
: ti@ ( k tf -- u ) tf-info swap u32s + u32@ ;
: ti! ( u k tf -- ) tf-info swap u32s + u32! ;
: tf-unnote ( tf -- ) 0 over tf-why ! -1 swap tf-at ! ;
\ A blank record, its sectioned file reset (free its blocks first).
: tier-file-init ( tf -- ) dup /tier-file erase dup tf-sf sections-init tf-unnote ;
\ The section, and the record in it, that loading refused.
: tier-file-error ( tf -- c-addr u record )
  dup tf-why @ ?dup if count else s" " then rot tf-at @ ;
\ Units in section i of the file read, as its table says.
: tf-units ( i tf -- n ) tf-sf sections-info drop nip nip ;
: tf-length ( i tf -- u ) tf-sf sections-info nip nip nip ;

\ ---- Writing. Heap blocks the record owns until tier-sections-free.
: tf-own ( addr tf -- ) dup tf-owned @ cells over tf-blocks + >r 1 swap tf-owned +! r> ! ;
: tf-block ( u tf -- addr outcome )
  dup tf-owned @ tf-blocks# = if 2drop outcome-full no-result exit then
  swap 1 max allocate if 2drop outcome-full no-result exit then
  tuck swap tf-own outcome-ok ;
: tier-sections-free ( tf -- )
  dup tf-owned @ 0 ?do dup tf-blocks i cells + @ free drop loop 0 swap tf-owned ! ;
\ n 32-bit fields at addr as little-endian bytes: a copy the record owns,
\ or addr itself where packed memory already is so (tf-le).
: tf-copy ( addr n tf -- addr' outcome )
  over u32s swap tf-block dup ok? 0= if 2swap 2drop exit then drop
  dup >r swap u32s>le r> outcome-ok ;
: tf-le ( addr n tf -- addr' outcome ) u32-block? if 2drop outcome-ok else tf-copy then ;
\ The bytes as written: a constant's payload 0, a declaration's mark clear.
: expr-unresolve ( c-addr -- )
  dup u32-le@ dup head-tag tag-const = if head-tag swap u32-le! else 2drop then ;
: exprs-unresolve ( c-addr units -- ) 0 ?do dup expr-unresolve /quad + loop drop ;
: decl-unmark ( c-addr -- ) dup u32-le@ staged-marked-bit invert and swap u32-le! ;
: decls-unmark ( c-addr n -- ) 0 ?do dup decl-unmark /staged + loop drop ;
\ Section i's bytes, ( addr units i tf -- addr' units outcome ) by kind:
\ a pool as it is, fields little-endian, the expressions and declarations
\ always copied and cleaned.
: tf-span ( addr units i -- addr n units ) tier-per-unit over * swap ;
: tf-raw-out ( addr units i tf -- addr units outcome ) 2drop outcome-ok ;
: tf-le-out ( addr units i tf -- addr' units outcome )
  >r tf-span r> swap >r tf-le r> swap ;
: tf-copy-out ( addr units i tf -- addr' units outcome )
  >r tf-span r> swap >r tf-copy r> swap ;
: tf-exprs-out ( addr units i tf -- addr' units outcome )
  tf-copy-out dup ok? if >r 2dup exprs-unresolve r> then ;
: tf-decls-out ( addr units i tf -- addr' units outcome )
  tf-copy-out dup ok? if >r 2dup decls-unmark r> then ;
create tf-outs ' tf-raw-out , ' tf-le-out , ' tf-le-out , ' tf-le-out , ' tf-raw-out ,
  ' tf-le-out , ' tf-exprs-out , ' tf-decls-out , ' tf-le-out ,
\ A layer (ADR 0020 amendment 1, F5; plan step SN4) writes each family's
\ records from a first unit on (tier-from!), and declarations and lines
\ the caller gives (tier-given!); a base writes every record.
: tf-from@ ( i tf -- u ) tf-from swap cells + @ ;
: tf-given? ( i tf -- flag ) tf-given cell+ @ 0<> swap tp-decls < 0= and ;
: tf-given@ ( i tf -- addr n )
  swap tp-decls = if tf-given 2@ else dup tf-given-lines @ swap tf-given @ then ;
\ A caller may also give a section's units whole (tier-joined!: the
\ environment's snapshot appends the names a check made beyond the input
\ to the names and their bytes; the caller keeps the block until the file
\ is written).
: tf-join ( i tf -- addr ) tf-joins swap 2* cells + ;
: tf-data ( i tf -- addr n )
  2dup tf-join 2@ over if 2swap 2drop exit then 2drop
  2dup tf-given? if tf-given@ exit then
  2dup tf-from@ >r tf-slab dup slab-count r@ - swap r> swap slab-at swap ;
: tier-from! ( addr tf -- ) tf-from tier-sections# cells move ;
: tier-given! ( decls n lines tf -- ) tuck tf-given-lines ! tf-given 2! ;
: tier-joined! ( addr n i tf -- ) tf-join 2! ;
: tf-out ( i tf -- addr units outcome )
  2dup tf-data 2swap over 1- cells tf-outs + @ execute ;
: tf-add ( i tf -- outcome )
  2dup tf-out ok-then2? 0= if nip nip exit then
  2swap tf-sf >r dup tier-unit rot rot 1+ r> sections-add ;
\ Sections 1 and on (section 0 is the information).
: tf-add-next ( tf k -- tf outcome ) 1+ over tf-add ;
: tf-adds ( tf -- outcome ) tier-sections# 1- ['] tf-add-next ok-each nip ;
\ The information fields.
: tf-count! ( i tf -- ) 2dup tf-data nip -rot swap ti-decls min swap ti! ;
: tf-counts! ( stage tf -- ) nip ti-decls 1+ 1 do i over tf-count! loop drop ;
: tf-meta-slot! ( k stage tf -- ) >r over swap meta-slot @ swap ti-meta + r> ti! ;
: tf-metas! ( stage tf -- )
  over stage-other? 0= if 2drop exit then dup >r 1 ti-other r> ti!
  #meta 0 do 2dup i -rot tf-meta-slot! loop 2drop ;
: tf-info-fill ( stage tf -- )
  dup tf-info ti-fields# u32s erase dup >r tier-version ti-version r> ti!
  2dup tf-counts! tf-metas! ;
: tf-info-add ( tf -- outcome )
  dup tf-info over tf-info-bytes ti-fields# u32s>le
  >r r@ tf-info-bytes 1 u32s ti-fields# 1 r> tf-sf sections-add ;
\ Add the ten sections of a sealed stage to tf's sectioned file (after
\ tier-file-init and any header fields of the caller's); the blocks they
\ point at stay valid until tier-sections-free, after the file is written.
: tier-sections ( stage tf -- outcome )
  over stage-sealed? 0= if 2drop outcome-invalid exit then 2dup tf-stage !
  2dup tf-info-fill dup tf-info-add ok-then? 0= if nip exit then nip tf-adds ;
: tf-saving ( c-addr u stage tf -- outcome )
  dup >r tier-sections dup ok? if drop r@ tf-sf sections-write else nip nip then
  r> drop ;
\ Write a sealed stage's tier to the file named c-addr u, atomically.
: tier-save ( c-addr u stage tf -- outcome )
  dup tier-file-init dup >r ['] tf-saving catch r> tier-sections-free throw ;

\ ---- Reading: sections into slabs, then records entered one by one.
\ After reading 32-bit fields as bytes: n fields at addr packed, in place
\ (nothing to do where packed memory is little-endian).
: le-packed ( addr n -- ) over swap le>u32s ;
: tf-read ( addr i tf -- outcome ) 2dup tf-length -rot tf-sf sections-read ;
: tf-fields-read ( addr i tf -- outcome )
  >r 2dup r@ tf-read ok-then2? 0= if r> drop exit then
  r> tf-length 1 u32s / le-packed outcome-ok ;
\ Section i read into slab from unit 0.
: tf-into ( i slab tf -- outcome ) >r 0 swap slab-at swap r> tf-fields-read ;
\ The units a slab holds before loading (a set's first record, made by
\ tier-init) are replaced by the file's, which must equal them: kept
\ aside, compared, put back.
: tf-first-bytes ( slab -- addr u ) 0 over slab-at swap dup slab-count swap slab-unit * ;
: tf-save-first ( slab tf -- ) >r tf-first-bytes r> tf-first swap move ;
: tf-same-first? ( slab tf -- flag ) >r tf-first-bytes r> tf-first over compare 0= ;
: tf-restore-first ( slab tf -- ) >r tf-first-bytes r> tf-first -rot move ;
: tf-first-checked ( outcome flag -- outcome )
  0= over ok? and if drop outcome-invalid then ;
: tf-records ( i slab tf -- outcome )
  2dup tf-save-first 2dup 2>r tf-into 2r@ tf-same-first? tf-first-checked
  2r> tf-restore-first ;
\ Room for section i's records in their set, its table at its final size.
: tf-room ( i slab tf -- outcome )
  rot swap tf-units over slab-count - dup 0< if 2drop outcome-invalid exit then
  swap records>cons cons-load-room ;
: tf-fill ( i tf -- outcome )
  2dup tf-slab swap >r 2dup r@ tf-room ok-then2? 0= if r> drop exit then r> tf-records ;
\ Room for section i's units in a plain slab, then the units read in.
: tf-room-only ( i slab tf -- outcome ) rot swap tf-units swap slab-room ;
: tf-plain ( i tf -- outcome )
  2dup tf-slab swap >r 2dup r@ tf-room-only ok-then2? 0= if r> drop exit then r> tf-into ;
\ A byte pool: claimed whole, then read.
: tf-pool ( i tf -- outcome )
  2dup tf-slab swap >r over r@ tf-units over slab-claim nip
  ok-then2? 0= if r> drop exit then 0 swap slab-at swap r> tf-read ;

\ Names: a string's bytes are the next ones of the pool; its prefix is an
\ earlier name; its data word, the hash name-hash! computes, is compared.
: tf-names-of ( stage -- names ) stage-tier tier-names ;
: pool-left ( pool tf -- u ) tf-pos @ swap slab-count swap - ;
: pool-next? ( offset len pool tf -- flag )
  tuck pool-left >r tf-pos @ rot = swap r> u> 0= and ;
: pool-advance ( len tf -- ) tf-pos +! ;
: name-span@ ( names -- offset len ) dup cand-b swap cand-head head-payload ;
: name-text ( names -- c-addr u ) dup name-span@ >r swap cons-bytes slab-at r> ;
: name-keyed ( names -- x ) dup name-text rot >r 2dup r> cons-key! hash-bytes ;
: name-hash-same? ( x stage -- flag )
  stage-tier dup tier-names cand-data >r tuck name-hash! tier-names cand-data r> = ;
: name-prefix-ok? ( stage -- flag ) tf-names-of dup cand-a swap cons-in? ;
: name-str-ok? ( tf -- flag )
  dup tf-stage@ name-prefix-ok? 0= if drop false exit then
  >r r@ tf-stage@ tf-names-of dup name-span@ rot cons-bytes r> pool-next? ;
: name-utf8? ( stage -- flag ) tf-names-of name-text utf8-valid? ;
: name-str-check ( stage tf -- flag )
  name-str-ok? 0= if drop false exit then
  dup name-utf8? 0= if drop false exit then dup tf-names-of name-keyed swap name-hash-same? ;
: name-adopt ( stage -- outcome ) tf-names-of 1 swap cons-adopt nip ;
: name-str-step ( stage tf -- outcome )
  2dup name-str-check 0= if 2drop outcome-invalid exit then
  over tf-names-of cand-payload swap pool-advance name-adopt ;
: name-num-ok? ( stage -- flag )
  dup tf-names-of cand-payload 0= over name-prefix-ok? and
  if dup tf-names-of cand-b swap name-hash-same? else drop false then ;
: name-num-step ( stage tf -- outcome )
  drop dup name-num-ok? if name-adopt else drop outcome-invalid then ;
\ The anonymous name is record 0 only (compared with tier-init's).
: name-step ( stage tf -- outcome )
  over tf-names-of cand-head head-tag
  case tag-name-str of name-str-step endof tag-name-num of name-num-step endof
    >r 2drop outcome-invalid r> endcase ;

\ Levels, expressions: the builder's check on the candidate, after its
\ data word is set to 0 as the builder's candidate starts (a check that
\ computes one writes it), and the word read compared.
: tf-levels-of ( stage -- levels ) stage-tier tier-levels ;
: level-checked? ( levels -- flag )
  dup cand-data >r 0 over cand-data! dup check-level nip swap cand-data r> = and ;
: level-step ( stage tf -- outcome )
  drop tf-levels-of dup level-checked?
  if 1 swap cons-adopt nip else drop outcome-invalid then ;
: tf-exprs-of ( stage -- exprs ) stage-tier tier-exprs ;
: expr-let-top? ( exprs -- flag ) cand-head head-tag let-tag? ;
: expr-run-check ( exprs -- outcome )
  dup cons-top swap over quad-head u32@ head-tag let-tag?
  if check-let else expr-check then nip ;
: expr-checked? ( exprs -- flag )
  dup cand-data >r 0 over cand-data! dup expr-run-check ok? swap cand-data r> = and ;
\ A letE's second record, inside the section: the body record as
\ let-body! writes it (the body itself is checked by check-let).
: exprs-left ( exprs tf -- u ) tp-exprs swap tf-units swap cons-records slab-count - ;
: body-record-ok? ( addr -- flag )
  dup quad-head u32@ tag-let-body = over quad-b u32@ 0= and swap quad-data u32@ 0= and ;
: let-shape? ( exprs tf -- flag )
  over swap exprs-left 2 u< 0= if cons-top /quad + body-record-ok? else drop false then ;
: expr-shape? ( exprs tf -- flag ) over expr-let-top? if let-shape? else 2drop true then ;
: expr-units ( exprs -- units ) expr-let-top? if 2 else 1 then ;
: mdata-count ( stage -- )
  dup tf-exprs-of cand-head head-tag tag-mdata = if 1 swap stage-mdata +! else drop then ;
: text-bytes ( t stage -- c-addr u )
  stage-tier tier-texts tuck cons-at dup u32@ swap 1 u32s + u32@ >r swap cons-bytes
  slab-at r> ;
: nat-ok? ( stage -- flag )
  dup tf-exprs-of cand-head head-tag tag-nat <> if drop true exit then
  dup tf-exprs-of cons-top quad-a u32@ swap text-bytes canonical-natural? ;
: expr-step ( stage tf -- outcome )
  over tf-exprs-of swap expr-shape? 0= if drop outcome-invalid exit then
  dup tf-exprs-of expr-checked? 0= if drop outcome-invalid exit then
  dup nat-ok? 0= if drop outcome-invalid exit then
  dup mdata-count tf-exprs-of dup expr-units swap cons-adopt nip ;

\ Lists: a length and that many items, inside the section (what the
\ items are, their users check). Texts: the next bytes of their pool.
: tf-tuples-of ( stage -- tuples ) stage-tier tier-tuples ;
: tuple-room ( tuples tf -- u ) tp-lists swap tf-units swap cons-records slab-count - ;
: tuple-step ( stage tf -- outcome )
  >r tf-tuples-of dup r> tuple-room over cons-top u32@ u>
  if dup cons-top u32@ 1+ swap cons-adopt nip else drop outcome-invalid then ;
: tf-texts-of ( stage -- texts ) stage-tier tier-texts ;
: text-span@ ( texts -- offset len ) cons-top dup u32@ swap 1 u32s + u32@ ;
: text-ok? ( texts tf -- flag ) >r dup text-span@ rot cons-bytes r> pool-next? ;
: text-keyed ( texts -- ) dup text-span@ >r over cons-bytes slab-at r> rot cons-key! ;
: text-step ( stage tf -- outcome )
  swap tf-texts-of 2dup swap text-ok? 0= if 2drop outcome-invalid exit then
  dup text-keyed dup text-span@ nip rot pool-advance 1 swap cons-adopt nip ;

\ Declarations, the draft at the declaration slab's free end being the
\ record read (numbered stage-decls, so the staged-*@ words read it).
\ The head bits each kind may have, from kind-axiom on.
create kind-flags
  staged-unsafe-bit ,  3 safety-shift lshift 3 hints-shift lshift or ,  0 ,
  staged-unsafe-bit ,  3 quot-shift lshift ,  0 ,
  staged-unsafe-bit staged-rec-bit or staged-reflexive-bit or ,
  staged-unsafe-bit ,  staged-unsafe-bit staged-k-bit or ,
: known-kind? ( kind -- flag ) kind-axiom kind-recursor 1+ within ;
: head-bits-ok? ( head -- flag )
  dup head-tag dup known-kind? 0= if 2drop false exit then
  kind-axiom - cells kind-flags + @ head-tag-mask or invert and 0= ;
\ A definition's safety and hints are 0 .. 2, as the reader gives them;
\ its hint is the height only when the hints are regular (2), else 0.
: code-ok? ( head shift -- flag ) rshift 3 and 3 <> ;
: codes-ok? ( head -- flag ) dup safety-shift code-ok? swap hints-shift code-ok? and ;
: hint-ok? ( head hint -- flag )
  swap dup head-tag kind-def = swap hints-shift rshift 3 and 2 = and
  if drop true else 0= then ;
: draft-head-ok? ( stage -- flag )
  draft dup staged-head u32@ dup head-bits-ok? over codes-ok? and
  swap rot staged-hint u32@ hint-ok? and ;
\ Kind data, as the handlers gather it.
: draft-d ( stage -- d stage ) dup stage-decls swap ;
: more-length? ( n stage -- flag ) draft-d staged-items = ;
: more-item ( i stage -- u ) draft-d staged-item ;
: item-name? ( i t stage -- flag )
  dup >r stage-tuples tuple-item r> stage-tier name-valid? ;
: name-at? ( t stage k -- t stage flag ) >r 2dup r> -rot item-name? ;
: names-tuple? ( t stage -- flag )
  2dup tuple-ok? 0= if 2drop false exit then
  2dup stage-tuples tuple-length ['] name-at? all? nip nip ;
: more-names? ( i stage -- flag ) tuck more-item swap names-tuple? ;
: all-data? ( stage -- flag ) dup draft staged-more u32@ swap names-tuple? ;
: block-data? ( stage -- flag ) 3 swap more-length? ;
: type-data? ( stage -- flag )
  5 over more-length? 0= if drop false exit then
  more-type-all over more-names? more-type-ctors rot more-names? and ;
: ctor-data? ( stage -- flag )
  4 over more-length? 0= if drop false exit then
  more-ctor-induct over more-item swap stage-tier name-valid? ;
\ A recursor's rules: [ctor nfields rhs] each, a name, a number, a term.
: tuple-at ( i t stage -- u ) stage-tuples tuple-item ;
: rule-ctor? ( k t stage -- flag ) dup >r tuple-at r> stage-tier name-valid? ;
: rule-rhs? ( k t stage -- flag )
  >r swap rule-rhs-item + swap r@ tuple-at r> stage-tier expr-valid? ;
: rule? ( k t stage -- flag ) >r 2dup r@ rule-ctor? -rot r> rule-rhs? and ;
: rule-at? ( t stage k -- t stage flag ) /rule-items * >r 2dup r> -rot rule? ;
\ Unchecked: the tuple's length is a multiple of /rule-items (rules?).
: rules-each? ( t stage -- flag )
  2dup stage-tuples tuple-length /rule-items / ['] rule-at? all? nip nip ;
: rules? ( t stage -- flag )
  2dup tuple-ok? 0= if 2drop false exit then
  2dup stage-tuples tuple-length /rule-items mod if 2drop false exit then rules-each? ;
: rec-data? ( stage -- flag )
  6 over more-length? 0= if drop false exit then
  more-rec-all over more-names? swap more-rec-rules over more-item swap rules? and ;
: kind-data? ( stage -- flag )
  dup draft-kind case
    kind-def of all-data? endof  kind-thm of all-data? endof
    kind-opaque of all-data? endof  kind-inductive of block-data? endof
    kind-type of type-data? endof  kind-ctor of ctor-data? endof
    kind-recursor of rec-data? endof  >r drop true r> endcase ;
: params-data? ( stage -- flag )
  dup draft-kind kind-inductive = if drop true exit then
  dup draft staged-params u32@ swap names-tuple? ;
: decl-ok? ( stage -- flag )
  dup draft-head-ok? 0= if drop false exit then
  dup draft-valid? 0= if drop false exit then
  dup params-data? 0= if drop false exit then kind-data? ;
\ The chain: the newest earlier declaration of the name, plus one, or 0
\ (always 0 for a block, which has no name).
: draft-prev ( stage -- u ) draft staged-prev u32@ ;
: chain-expected ( n stage -- u outcome )
  2dup by-name-cover dup ok? 0= if nip nip no-result exit then drop
  stage-by-name fields@ outcome-ok ;
: draft-chained ( stage -- outcome )
  dup draft staged-name u32@ ?dup 0= if draft-prev 0= flag>outcome exit then
  over chain-expected ok-then? 0= if nip exit then swap draft-prev = flag>outcome ;
: decl-keep ( stage -- outcome )
  dup draft staged-name u32@ ?dup 0= if draft-keep drop outcome-ok exit then
  over draft-keep swap rot newest! outcome-ok ;
: decl-step ( stage tf -- outcome )
  drop dup decl-ok? 0= if drop outcome-invalid exit then
  dup draft-chained ok-then? 0= if exit then decl-keep ;

\ Lines: below staged-none, each above the one before, except that the
\ members of a block (its types, constructors and recursors) are on its
\ block's line, as the reader keeps them.
: member-kind? ( kind -- flag ) kind-type kind-recursor 1+ within ;
\ Line i of the lines at addr, and line i - 1 before it.
: tier-line-pair ( addr i -- prev line ) u32s + dup 1 u32s - u32@ swap u32@ ;
\ Line i after line i - 1 (i > 0), declaration i of stage.
: line-ok? ( addr i stage -- flag )
  >r tuck tier-line-pair dup staged-none = if 2drop r> 2drop false exit then
  2dup = if 2drop r> staged-kind@ member-kind? exit then u< nip r> drop ;
: line-after? ( addr stage k -- addr stage flag ) 1+ >r 2dup r> swap line-ok? ;
: lines-ok? ( addr n stage -- flag )
  swap dup 0= if 2drop drop true exit then
  2 pick u32@ staged-none = if 2drop drop false exit then
  1- ['] line-after? all? nip nip ;
: lines-commit ( n slab stage -- outcome )
  >r 0 over slab-at 2 pick r> lines-ok?
  if slab-commit outcome-ok else 2drop outcome-invalid then ;

\ ---- The sections in order.
create tf-steps   \ the step ( stage tf -- outcome ) entering one record
  0 , 0 , ' name-step , ' level-step , ' tuple-step , 0 , ' text-step , ' expr-step ,
  ' decl-step , 0 ,
: tf-step ( i tf -- outcome ) dup tf-stage@ swap rot cells tf-steps + @ execute ;
: tf-left? ( i tf -- flag ) 2dup tf-slab slab-count -rot tf-units u< ;
: tf-adopt-all ( i tf -- outcome )
  begin 2dup tf-left? while 2dup tf-step dup ok? 0= if nip nip exit then drop repeat
  2drop outcome-ok ;
: tf-family ( i tf -- outcome )
  2dup tf-fill dup ok? 0= if nip nip exit then drop tf-adopt-all ;
\ A family whose records point into the pool before it: every byte used.
: pool-used? ( pool tf -- flag ) tf-pos @ swap slab-count = ;
: tf-pooled ( i tf -- outcome )
  0 over tf-pos ! 2dup tf-family dup ok? 0= if nip nip exit then drop
  swap 1- over tf-slab swap pool-used? flag>outcome ;
: tf-decls ( i tf -- outcome )
  2dup tf-plain dup ok? 0= if nip nip exit then drop tf-adopt-all ;
: tf-lines ( i tf -- outcome )
  2dup tf-plain dup ok? 0= if nip nip exit then drop
  tuck tf-units over tf-stage@ stage-lines rot tf-stage@ lines-commit ;
create tf-loads   \ by position, from 1
  ' tf-pool , ' tf-pooled , ' tf-family , ' tf-family , ' tf-pool , ' tf-pooled ,
  ' tf-family , ' tf-decls , ' tf-lines ,
: tf-limited ( outcome tf -- outcome )
  over ok? if tf-stage@ stage-over? if drop outcome-full then else drop then ;
: tf-load ( i tf -- outcome ) dup >r over 1- cells tf-loads + @ execute r> tf-limited ;
: tf-note ( i tf -- ) 2dup tf-slab slab-count over tf-at ! swap tier-title swap tf-why ! ;
: tf-load-noted ( i tf -- outcome ) 2dup tf-load dup ok? if nip nip exit then -rot tf-note ;
: tf-load-next ( tf k -- tf outcome ) 1+ over tf-load-noted ;
: tf-loads-all ( tf -- outcome ) tier-sections# 1- ['] tf-load-next ok-each nip ;

\ The metadata: none (every field 0), or five texts of the tier.
: tf-meta@ ( k tf -- u ) swap ti-meta + swap ti@ ;
: metas-zero? ( tf -- flag ) true #meta 0 do over i swap tf-meta@ 0= and loop nip ;
: meta-take ( k tf -- flag )
  2dup tf-meta@ swap tf-stage@ 2dup stage-tier tier-texts cons-entry?
  if rot swap meta-slot ! true else 2drop drop false then ;
: metas-take ( tf -- flag ) true #meta 0 do over i swap meta-take and loop nip ;
\ Other versions (other 1) as the reader takes them (ndjson.fs
\ header-taken?): only into a stage that reads any version
\ (stage-any-version!), with the pinned format, and not all five pinned
\ (a file that says other for the pinned versions is malformed).
: meta-pinned? ( k stage -- flag )
  over >r stage-meta-text r> cells pinned-meta + @ execute compare 0= ;
: metas-pinned? ( stage -- flag ) true #meta 0 do over i swap meta-pinned? and loop nip ;
: metas-taken ( stage -- outcome )
  dup metas-pinned? if drop outcome-invalid exit then
  dup stage-export export-any-version? 0= if drop outcome-unsupported exit then
  2 swap meta-pinned? if outcome-ok else outcome-unsupported then ;
: tf-other ( tf -- outcome )
  dup metas-take 0= if drop outcome-invalid exit then tf-stage@
  true over stage-other ! dup metas-taken dup ok? if nip exit then
  false rot stage-other ! ;
: tf-metas ( tf -- outcome )
  ti-other over ti@ case
    0 of metas-zero? flag>outcome endof
    1 of tf-other endof
    >r drop outcome-invalid r> endcase ;

\ The start: a fresh stage, this format's ten sections, the information
\ with this version and every section's count.
: tf-fresh? ( stage -- flag )
  dup staging-empty stage-in? 0= if drop false exit then
  dup stage-continued @ if drop false exit then
  stage-tier dup tier-names cons-numbers 1 = over tier-levels cons-numbers 1 = and
  over tier-tuples cons-numbers 0= and over tier-texts cons-numbers 0= and
  swap tier-exprs cons-numbers 0= and ;
: tf-section-ok? ( i tf -- flag )
  over swap tf-sf sections-info 2drop rot tuck tier-unit = >r 1+ = r> and ;
: tf-kinds? ( tf -- flag )
  dup tf-sf sections-count tier-sections# < if drop false exit then
  true tier-sections# 0 do over i swap tf-section-ok? and loop nip ;
: tf-info-read ( tf -- outcome )
  0 over tf-units ti-fields# <> if drop outcome-invalid exit then
  >r r@ tf-info-bytes 0 r@ tf-read
  dup ok? if r@ tf-info-bytes r@ tf-info ti-fields# le>u32s then r> drop ;
: tf-count-ok? ( i tf -- flag ) 2dup tf-units -rot swap ti-decls min swap ti@ = ;
: tf-counts? ( tf -- flag )
  true tier-sections# 1 do over i swap tf-count-ok? and loop nip ;
: tf-info-check ( tf -- outcome )
  ti-version over ti@ tier-version <> if drop outcome-unsupported exit then
  tf-counts? flag>outcome ;
: tf-start ( tf -- outcome )
  dup tf-kinds? 0= if drop outcome-invalid exit then
  dup tf-info-read ok-then? 0= if exit then tf-info-check ;
: tf-info-noted ( outcome tf -- outcome )
  over ok? if drop exit then c" information" over tf-why ! 0 swap tf-at ! ;
: tf-reading ( stage tf -- outcome )
  tuck tf-stage ! dup tf-start over tf-info-noted ok-then? 0= if exit then
  dup tf-loads-all ok-then? 0= if exit then dup >r tf-metas r> tf-info-noted ;
\ Read the ten sections of tf's opened sectioned file into a stage that
\ stage-init made and nothing was read into: filled, or rolled back to
\ empty on any failure or THROW (passed on).
: tier-read ( stage tf -- outcome )
  dup tf-unnote over tf-fresh? 0= if 2drop outcome-invalid exit then
  over >r ['] tf-reading catch
  ?dup if nip nip r> stage-rollback drop throw then r> stage-after ;
: tf-open ( c-addr u tf -- outcome )
  dup >r tf-sf sections-open dup ok? 0= if c" header or section table" r@ tf-why ! then
  r> drop ;
: tf-loading ( c-addr u stage tf -- outcome )
  2>r 2r@ nip tf-open dup ok? if drop 2r@ tier-read then 2r> 2drop ;
\ Load the tier saved in the file named c-addr u into a fresh stage, as
\ tier-read; the file is closed again in every case.
: tier-load ( c-addr u stage tf -- outcome )
  dup tier-file-init dup >r ['] tf-loading catch r> tf-sf sections-close drop throw ;

base !   \ the BASE this file was loaded with

\ The importer stage (ADR 0016 C9 step 2; plan tasks 3.2.1 and 3.3.1 in
\ part): a Lean export read through the NDJSON reader (import/ndjson.fs),
\ checked against its manifest by default (import/manifest.fs), into a
\ compact input tier (core/compact.fs) with its declarations, ready for
\ every worker to read. Untrusted [import] code and fail-closed: it stores
\ what the export says and checks its shape, nothing about types or
\ proofs; a staged declaration is input for the checker, never a checked
\ one. LeanForth-specific. The records and handlers are in
\ import/stage-records.fs, whose header describes the declaration record.
\
\ What a stage holds after stage-load: every name, level, expression and
\ literal of the export, hash-consed in the input tier (ADR 0016 C1-C4);
\ every declaration as a 32-byte record (C2), and the line of the export it
\ came from (staged-line@, which a presentation reads), numbered in file order (an
\ inductive block, then its types, constructors and recursors); the
\ name-to-declaration array, the newest declaration of each name, each
\ record holding the one before it of the same name (C4, the chain ADR
\ 0012 E5 reads); and the export-index maps (loading aids, freed by
\ stage-unmap). Sealing resolves every constant (C4, P3): a constant's
\ payload becomes its declaration's number + 1 when exactly one
\ declaration has its name, and 0 when several have (the array and the
\ chain then decide); a constant whose name no declaration has is invalid,
\ unless it names a recursor Lean's kernel generates for an inductive type
\ of the file (ADR 0016 amendment 1: P.rec or P.rec_<digits>, P a type
\ declaration's name), which resolves as several do, at the check.
\ The payload is not yet read by the checker: the feed (import/feed.fs)
\ builds each reference by name, which the environment's chain resolves
\ (ADR 0016 C9 steps 4-6 will read the payload). Today its only effect is
\ the unknown-constant refusal (plan task 5.2.6), so nothing may rely on it.
\
\ Life cycle, the reading and sealing steps refused (invalid) out of order:
\   stage-init     an empty stage; the expression table starts at 2^log2
\                  slots (pre-size it from the export, about 59 bytes per
\                  expression, so that it seldom doubles), the others at 2^12
\   stage-any-version!  true: before a read, accept metadata of any exporter
\                  and Lean version, only the format pinned (stage-other?
\                  and stage-meta-text tell what it named); false: pinned
\   stage-read     read the export with its manifest, "<file>.manifest.json"
\                  or the file stage-manifest-use names (the default);
\   stage-read-unchecked   read it without one: the caller's explicit choice
\   stage-seal     resolve the constants, mark, and make the tier read-only
\   stage-load, stage-load-unchecked   read, then seal
\   stage-continue, stage-continue-unchecked   read another export into
\                  a filled tier (a loaded snapshot's, import/snapshot-tier.fs),
\                  keeping its records but not its declarations (below)
\   stage-unmap    free the export-index maps of a sealed stage once nothing
\                  needs them; on any other stage it does nothing
\   stage-free     free everything, in any state; the record is blank again
\ A read that fails, for any reason or by a THROW (which then passes on),
\ rolls the stage back to empty (stage-init's state), so nothing of a
\ partial, malformed or mismatched file stays; a stage whose rollback or
\ sealing failed is broken and only stage-free applies. Once sealed, any
\ number of tasks may read it, without locks; until then one task owns it.
\
\ Outcomes (ADR 0008): ok; invalid for malformed input, a bad reference,
\ an unknown constant (at sealing), a manifest that is missing or differs,
\ or a step out of order; unsupported for other exporter, format or Lean
\ versions (after stage-any-version!, other formats); full for a limit (an
\ export index above max-n, a C1 limit, a number beyond 32 bits, more
\ than 2^27 - 1 declarations), no heap, or the memory limit. A bound
\ variable's index of 2^32 or more is invalid, not full (no field holds it;
\ pinned Lean panics from 1048575, so both are refusals; review rvKC L2).
\ A number beyond 32 bits in a name is full where pinned Lean accepts the
\ file: a temporary gap, closed by plan task 5.2.6 (review rvKC L1). A kind not
\ yet supported is staged but marked: an mdata expression (written only
\ when the exporter is asked to) is kept without its key-value data, under
\ its own tag (core/compact-exprs.fs), and every declaration whose type,
\ value or recursor rule holds one is marked (staged-marked?), so the
\ checker refuses it as unsupported without walking it. stage-error gives
\ the line, field and reason of a failure (line 0 for the manifest and
\ for sealing; stage-culprit then names the unknown constant's name).
\
\ Memory limit (plan 3.3.1): stage-limit! sets the most bytes of heap
\ blocks the stage may hold (stage-allocated: the tier, maps and
\ declarations); the read stops as full at the first record after which
\ they exceed it. Blocks grow by doubling, so the peak may pass the limit
\ by the last block's growth. Sealing counts the marks' bitset (one bit
\ per expression, made only when an mdata record was staged) against it,
\ but not tier-seal's rebuild of each table at most half full, which for
\ a moment holds a table's old and new slots (1.07 GB new for Mathlib's
\ expressions, whose table pre-sized to 2^28 is not rebuilt). 0, the
\ default, is no limit but the heap's.
\
\ Example:
\   create lib /stage allot
\   16 lib stage-init drop
\   s" tests/reference/constant-fixture.ndjson" lib stage-load .   \ 0, ok
\   lib stage-decls .                                              \ 3
\   lib stage-free
\
\ State: none of its own; every word takes a stage record (/stage), which
\ owns its heap blocks and open file until stage-free. Loads in decimal
\ whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/outcome.fs
require ../lib/u32.fs
require ../lib/decimal.fs
require ../lib/slab.fs
require ../lib/cons.fs
require ../core/compact.fs
require ./ndjson.fs
require ./manifest.fs
require ./stage-records.fs

0 constant staging-blank      \ zeroed, or freed
1 constant staging-empty      \ made, nothing read
2 constant staging-filled     \ read whole, not sealed
3 constant staging-sealed     \ read-only
4 constant staging-broken     \ a rollback or sealing failed: only stage-free
: stage-in? ( stage state -- flag ) swap stage-state @ = ;
: stage-sealed? ( stage -- flag ) staging-sealed stage-in? ;
\ Set the state after a step: state when the outcome is ok, else broken.
: stage-state! ( stage outcome state -- outcome )
  over ok? 0= if drop staging-broken then rot stage-state ! ;
: stage-limit! ( bytes stage -- ) stage-limit ! ;
: stage-manifest-use ( c-addr u stage -- ) stage-manifest manifest-use ;
\ Read an export of any exporter and Lean version, only its format
\ pinned, when flag is true (after stage-init, which sets it false).
: stage-any-version! ( flag stage -- ) stage-export export-any-version! ;
\ Whether the staged export's metadata names other versions than the
\ pinned ones; and its text k (0 the exporter's name, 1 its version, 2
\ the format version, 3 the Lean version, 4 Lean's githash), the pinned
\ one's when it names those.
: stage-other? ( stage -- flag ) stage-other @ ;
create pinned-meta
  ' pinned-exporter , ' pinned-exporter-version , ' pinned-format-version ,
  ' pinned-lean-version , ' pinned-lean-githash ,
: stage-meta-text ( k stage -- c-addr u )
  dup stage-other? if tuck meta-slot @ swap stage-tier tier-texts text@ exit then
  drop cells pinned-meta + @ execute ;
\ The name sealing failed on, and why.
: stage-culprit@ ( stage -- n ) stage-culprit @ ;
: stage-error ( stage -- line key-addr key-u why-addr why-u )
  dup stage-why @ ?dup if nip >r 0 s" " r> count exit then stage-export export-error ;

\ ---- Making and freeing.
12 constant stage-tables-log2
: tier-start ( log2 stage -- outcome )
  stage-tier >r stage-tables-log2 r@ tier-init
  dup ok? if drop r@ tier-exprs cons-table htab-presize else nip then r> drop ;
\ The maps' first entries: the anonymous name and level zero are export
\ index 0 of their families.
: maps-start ( stage -- outcome )
  0 over stage-name-map fields-push dup ok? if drop 0 swap stage-level-map fields-push
  else nip then ;
\ The stage's own slabs; slab-init refuses only an unsound shape, and
\ these shapes are fixed, so its outcomes are not kept.
: slabs-start ( stage -- outcome )
  cons-numbers-max over stage-name-map fields-init drop
  cons-numbers-max over stage-level-map fields-init drop
  cons-numbers-max over stage-expr-map fields-init drop
  payload-limit over stage-by-name fields-init drop
  cons-numbers-max over stage-lines fields-init drop
  cons-numbers-max over stage-noted fields-init drop
  /staged payload-limit 1- 2 pick stage-decl-records slab-init drop maps-start ;
: tier-marked ( stage -- outcome ) dup stage-start swap stage-tier tier-mark ;
: export-start ( stage -- outcome )
  dup stage-export export-init dup ok? 0= if nip exit then drop
  dup handlers-set dup stage-export swap stage-manifest manifest-init ;
\ An empty stage whose expression table starts at 2^log2 slots: ok, or
\ full (stage-free then frees what was made). The record must not hold
\ memory: stage-free first.
: stage-init ( log2 stage -- outcome )
  dup /stage erase tuck tier-start ['] slabs-start ok-with ['] tier-marked ok-with
  ['] export-start ok-with staging-empty stage-state! ;
\ The export-index maps: freed by stage-free in any state, and by
\ stage-unmap only once the stage is sealed.
: maps-free ( stage -- )
  dup stage-name-map slab-free dup stage-level-map slab-free stage-expr-map slab-free ;
: reader-maps-free ( stage -- ) stage-export export-maps-free ;
: stage-unmap ( stage -- )
  dup stage-sealed? if dup reader-maps-free maps-free else drop then ;
: stage-free ( stage -- )
  dup stage-tier tier-free dup stage-export export-free dup stage-manifest manifest-free
  dup maps-free dup stage-decl-records slab-free dup stage-by-name slab-free
  dup stage-lines slab-free dup stage-noted slab-free
  dup stage-reach heap-release /stage erase ;

\ ---- Reading. A failed read rolls the stage back: the tier to the mark
\ stage-init took, the maps to their first entries, no declarations.
\ The export-index maps back to their first entries, no reason kept (also
\ stage-extend's, below).
: maps-again ( stage -- outcome )
  dup stage-name-map slab-clear dup stage-level-map slab-clear
  dup stage-expr-map slab-clear 0 over stage-why ! maps-start ;
: own-clear ( stage -- outcome )
  dup stage-decl-records slab-clear dup stage-by-name slab-clear
  dup stage-lines slab-clear dup stage-noted slab-clear
  0 over stage-mdata ! 0 over stage-marks ! 0 over stage-other ! maps-again ;
: stage-rollback ( stage -- outcome )
  dup stage-start over stage-tier tier-rollback ['] own-clear ok-with
  staging-empty stage-state! ;
\ After a read: filled, or rolled back (the read's outcome stays; a
\ rollback that fails leaves the stage broken).
: stage-after ( outcome stage -- outcome )
  over ok? if staging-filled swap stage-state ! else stage-rollback drop then ;
: checked-read ( c-addr u stage -- outcome ) stage-manifest manifest-read ;
: plain-read ( c-addr u stage -- outcome ) stage-export export-read ;
\ Read with xt ( c-addr u stage -- outcome ); a THROW rolls back, then
\ passes on.
: stage-reading ( c-addr u stage xt -- outcome )
  over staging-empty stage-in? 0= if 2drop 2drop outcome-invalid exit then
  over >r catch ?dup if nip nip nip r@ stage-rollback drop r> drop throw then
  r> stage-after ;
: stage-read ( c-addr u stage -- outcome ) ['] checked-read stage-reading ;
: stage-read-unchecked ( c-addr u stage -- outcome ) ['] plain-read stage-reading ;

\ ---- Sealing.
\ The array covers every name of the tier.
: names-covered ( stage -- outcome )
  dup stage-tier tier-names cons-numbers 1- swap by-name-cover ;
\ Every expression of the input tier in number order (a letE spans two
\ numbers): xt ( e stage -- outcome ) on each, stopping at the first
\ outcome that is not ok.
: input-exprs ( stage -- n ) stage-tier tier-exprs cons-numbers ;
: exprs-walk ( stage xt -- outcome )
  over input-exprs 0 ?do
    i 2 pick 2 pick execute dup ok? 0= if nip nip unloop exit then drop
    i 2 pick stage-tier expr-next i -
  +loop 2drop outcome-ok ;

\ Constants. What a constant of name n resolves to: its declaration + 1,
\ or 0 when several declarations have the name; false when none has.
: resolution ( n stage -- u true | false )
  tuck stage-by-name fields@ dup 0= if nip exit then
  dup 1- rot staged-prev@ if drop 0 then true ;
: unknown-constant ( n stage -- outcome )
  tuck stage-culprit ! c" unknown constant" swap stage-why ! outcome-invalid ;
\ ADR 0016 amendment 1 (2026-11-04; the owner's condition: exactly Lean's
\ verdicts): Lean's add_inductive adds the recursors it generates, T.rec
\ for each type T of a block and T.rec_1, T.rec_2, ... for a nested one,
\ whatever the file holds, so a file may use one it never declares. Such
\ a name -- last part rec or rec_<digits>, its prefix the name of a type
\ declaration of the file -- is kept, as a name several declarations
\ have: the checked environment resolves it at the check (the recursor
\ the block generated, or no constant). Any other name no declaration
\ has stays an unknown constant.
: generated-text? ( c-addr u -- flag )
  2dup s" rec" compare 0= if 2drop true exit then
  2dup 4 min s" rec_" compare if 2drop false exit then 4 /string decimal-digits? ;
: type-decl? ( d stage -- flag ) staged-kind@ kind-type = ;
: type-named? ( n stage -- flag )
  2dup stage-by-name slab-count u< 0= if 2drop false exit then
  tuck stage-by-name fields@ begin ?dup while
    1- 2dup swap type-decl? if 2drop true exit then over staged-prev@
  repeat drop false ;
: generated-name? ( n stage -- flag )
  2dup stage-tier name-tag@ tag-name-str <> if 2drop false exit then
  2dup stage-tier name-text@ generated-text? 0= if 2drop false exit then
  tuck stage-tier name-prefix@ swap type-named? ;
: resolved ( u e stage -- outcome ) stage-tier expr-resolve! outcome-ok ;
\ After a read that continues a tier (stage-continue), a constant of an
\ earlier read whose name this read never contained is no unknown
\ constant of this read: it resolves as several do (payload 0).
: earlier-name? ( n stage -- flag )
  dup stage-continued @ if noted? 0= else 2drop false then ;
: const-resolve ( e stage -- outcome )
  2dup stage-tier expr-a@ over resolution if -rot resolved exit then
  2dup stage-tier expr-a@ over generated-name? if 0 -rot resolved exit then
  2dup stage-tier expr-a@ over earlier-name? if 0 -rot resolved exit then
  tuck stage-tier expr-a@ swap unknown-constant ;
: record-resolve ( e stage -- outcome )
  2dup stage-tier expr-tag@ tag-const = if const-resolve else 2drop outcome-ok then ;
: consts-resolve ( stage -- outcome ) ['] record-resolve exprs-walk ;

\ Marks, only when an mdata record was staged. The reach bitset (heap,
\ freed after sealing, counted against the limit) holds one bit per
\ expression number, set when the expression is or holds an mdata record.
\ Children have smaller numbers than their parents, so one walk in number
\ order fills it.
: reach-bit ( e stage -- addr mask )
  stage-reach @ over 5 rshift u32s + swap 31 and 1 swap lshift ;
: reach@ ( e stage -- flag ) reach-bit swap u32@ and 0<> ;
: reach! ( e stage -- ) reach-bit over u32@ or swap u32! ;
\ Whether an expression reaches one, by its tag ( e stage -- flag ).
: reach-none ( e stage -- flag ) 2drop false ;
: reach-self ( e stage -- flag ) 2drop true ;
: a-reach? ( e stage -- flag ) tuck stage-tier expr-a@ swap reach@ ;
: b-reach? ( e stage -- flag ) tuck stage-tier expr-b@ swap reach@ ;
: body-reach? ( e stage -- flag ) tuck stage-tier expr-body@ swap reach@ ;
: pair-reach? ( e stage -- flag ) 2dup a-reach? >r b-reach? r> or ;
: let-reach? ( e stage -- flag ) 2dup pair-reach? >r body-reach? r> or ;
check-table reach-checks
' reach-none reach-checks check-fill
' reach-self tag-mdata reach-checks check!
' a-reach? tag-proj reach-checks check!
' pair-reach? tag-app reach-checks check!
' let-reach? tag-let reach-checks check!
' let-reach? tag-let-nondep reach-checks check!
: binder-reaches ( -- ) 8 0 do ['] pair-reach? tag-lam i + reach-checks check! loop ;
binder-reaches
: reach-note ( e stage -- outcome )
  2dup 2dup stage-tier expr-tag@ reach-checks check-run
  if reach! else 2drop then outcome-ok ;
\ The bitset: room under the limit, then a zeroed block.
: reach-bytes ( stage -- u ) input-exprs 31 + 5 rshift 1 max u32s ;
: reach-room? ( u stage -- flag )
  dup stage-limit @ ?dup if >r stage-allocated + r> u> 0= else 2drop true then ;
: limit-reached ( stage -- outcome )
  c" memory limit of the stage reached" swap stage-why ! outcome-full ;
: reach-make ( stage -- outcome )
  dup reach-bytes 2dup swap reach-room? 0= if drop limit-reached exit then
  dup allocate if 2drop drop outcome-full exit then
  dup rot erase swap stage-reach ! outcome-ok ;
: reach-free ( stage -- ) stage-reach heap-release ;
\ Whether a declaration's type, value or recursor rules reach one.
: field-reach? ( e stage -- flag ) over none? if 2drop false else reach@ then ;
: rules-reach? ( t stage -- flag )
  2dup stage-tuples tuple-length 0 ?do
    i rule-rhs-item + 2 pick 2 pick stage-tuples tuple-item over reach@
    if 2drop true unloop exit then
  /rule-items +loop 2drop false ;
: decl-reach? ( d stage -- flag )
  2dup staged-type@ over field-reach? >r 2dup staged-value@ over field-reach? r> or >r
  2dup staged-kind@ kind-recursor = if
    more-rec-rules 2 pick 2 pick staged-item swap rules-reach? nip
  else 2drop false then r> or ;
: staged-mark ( d stage -- )
  tuck staged-at staged-head dup u32@ staged-marked-bit or swap u32!
  1 swap stage-marks +! ;
: decls-mark ( stage -- )
  dup stage-decls 0 ?do i over decl-reach? if i over staged-mark then loop drop ;
: stage-marking ( stage -- outcome )
  dup stage-mdata @ 0= if drop outcome-ok exit then
  dup reach-make dup ok? 0= if nip exit then drop
  dup ['] reach-note exprs-walk drop dup decls-mark reach-free outcome-ok ;

\ Sealing: the array covers every name, the marks are set, every constant
\ is resolved, and the tier is sealed (its tables spread, its slabs
\ trimmed; trimming the declarations and the array only saves memory, so
\ a RESIZE that fails there is no failure). Any failure breaks the stage.
: tier-sealing ( stage -- outcome )
  dup stage-decl-records slab-trim drop dup stage-by-name slab-trim drop
  dup stage-lines slab-trim drop
  stage-tier tier-seal ;
: stage-seal ( stage -- outcome )
  dup staging-filled stage-in? 0= if drop outcome-invalid exit then
  dup names-covered ['] stage-marking ok-with ['] consts-resolve ok-with
  ['] tier-sealing ok-with staging-sealed stage-state! ;
: stage-load ( c-addr u stage -- outcome )
  dup >r stage-read dup ok? if drop r> stage-seal else r> drop then ;
: stage-load-unchecked ( c-addr u stage -- outcome )
  dup >r stage-read-unchecked dup ok? if drop r> stage-seal else r> drop then ;

\ ---- Continuing (ADR 0020 D5; plan step SN2). stage-continue reads
\ another export into a filled stage's open tier -- one loaded from a
\ snapshot (import/snapshot-tier.fs) or read and not yet sealed -- as
\ stage-read does: the earlier read's declarations, lines and maps go,
\ its records stay, so a record of the new read equal to one of them gets
\ its number; the declarations are the new read's only. Its constants'
\ names are noted (put-const-noted), and sealing refuses an unknown
\ constant only among them. A tier mark is taken first: a failed read
\ rolls back to the tier as it was, with no declarations (empty).
\ Invalid unless the stage is filled.
: continued! ( stage -- )
  true over stage-continued !
  ['] put-const-noted kind-const rot stage-export export-handler ! ;
: stage-reopen ( stage -- outcome )
  dup staging-filled stage-in? 0= if drop outcome-invalid exit then
  dup own-clear ['] tier-marked ok-with over continued! staging-empty stage-state! ;
: stage-continue ( c-addr u stage -- outcome )
  dup stage-reopen ok-then? if stage-read else nip nip then ;
: stage-continue-unchecked ( c-addr u stage -- outcome )
  dup stage-reopen ok-then? if stage-read-unchecked else nip nip then ;

\ ---- Records made in this process (plan tasks 8.2.1c-d; ADR 0017
\ Amendment 2). stage-produce ( xt stage -- outcome ) reads, as
\ stage-read-unchecked reads a file, the lines a producer hands over:
\ xt ( -- outcome ) gives each line to stage-line ( c-addr u stage --
\ outcome ) of this stage and returns its first outcome that is not ok
\ (or ok); the lines are then ended as a file's (export-end). A line is
\ decoded in place, so the producer must not need its bytes afterwards.
\ The LeanForth words' export (author/export.fs) is such a producer. With
\ the same rules as a read: an empty stage only, filled after an ok one,
\ rolled back to empty after any other outcome or a THROW.
\ stage-extend ( stage -- outcome ) readies a filled stage -- a library
\ export read and not sealed -- for one more read whose declarations join
\ the first's: the export-index maps start again and the declarations,
\ their name chains and lines stay, so the next read names the first
\ read's records only by their content, and at sealing its constants
\ resolve among every declaration of both. A tier mark is taken first; a
\ failed read then rolls back to empty, the first read's declarations
\ gone too. Invalid unless the stage is filled.
: stage-line ( c-addr u stage -- outcome ) stage-export export-line ;
\ stage-reading's reader takes ( c-addr u stage ): here the producer's xt
\ and a 0 stand in for the file's name, which a producer has none of.
: produced ( xt 0 stage -- outcome )
  nip dup stage-export export-restart swap execute
  ok-then? if stage-export export-end then ;
: stage-produce ( xt stage -- outcome ) 0 swap ['] produced stage-reading ;
: stage-extend ( stage -- outcome )
  dup staging-filled stage-in? 0= if drop outcome-invalid exit then
  dup maps-again ['] tier-marked ok-with staging-empty stage-state! ;

\ ---- Finding declarations (after sealing; unchecked numbers as above).
\ The newest declaration of name n; the one staged before d of the same
\ name; the one a constant resolved to (false when none or several have
\ its name: then stage-find and stage-previous give them all).
: +1>number ( u -- d true | false ) dup if 1- true else drop false then ;
: stage-find ( n stage -- d true | false )
  2dup stage-by-name slab-count u< 0= if 2drop false exit then
  stage-by-name fields@ +1>number ;
: stage-previous ( d stage -- d' true | false ) staged-prev@ +1>number ;
: stage-resolved ( e stage -- d true | false )
  stage-tier 2dup expr-tag@ tag-const = if expr-payload@ +1>number else 2drop false then ;

base !   \ the BASE this file was loaded with

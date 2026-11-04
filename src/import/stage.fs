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
\ every declaration as a 32-byte record (C2), numbered in file order (an
\ inductive block, then its types, constructors and recursors); the
\ name-to-declaration array, the newest declaration of each name, each
\ record holding the one before it of the same name (C4, the chain ADR
\ 0012 E5 reads); and the export-index maps (loading aids, freed by
\ stage-unmap). Sealing resolves every constant (C4, P3): a constant's
\ payload becomes its declaration's number + 1 when exactly one
\ declaration has its name, and 0 when several have (the array and the
\ chain then decide); a constant whose name no declaration has is invalid.
\
\ Life cycle, each step refused (invalid) out of order:
\   stage-init     an empty stage; the expression table starts at 2^log2
\                  slots (pre-size it from the export, about 59 bytes per
\                  expression, so that it seldom doubles), the others at 2^12
\   stage-read     read the export with its manifest, "<file>.manifest.json"
\                  or the file stage-manifest-use names (the default);
\   stage-read-unchecked   read it without one: the caller's explicit choice
\   stage-seal     resolve the constants, mark, and make the tier read-only
\   stage-load, stage-load-unchecked   read, then seal
\   stage-unmap    free the export-index maps once nothing needs them
\   stage-free     free everything; the record is blank again
\ A read that fails, for any reason or by a THROW (which then passes on),
\ rolls the stage back to empty (stage-init's state), so nothing of a
\ partial, malformed or mismatched file stays; a stage whose rollback or
\ sealing failed is broken and only stage-free applies. Once sealed, any
\ number of tasks may read it, without locks; until then one task owns it.
\
\ Outcomes (ADR 0008): ok; invalid for malformed input, a bad reference,
\ an unknown constant (at sealing), a manifest that is missing or differs,
\ or a step out of order; unsupported for other exporter, format or Lean
\ versions; full for a limit (a C1 limit, a number beyond 32 bits, more
\ than 2^27 - 1 declarations), no heap, or the memory limit. A kind not
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
\ by the last block's growth. 0, the default, is no limit but the heap's.
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
\ After an ok outcome, xt ( stage -- outcome ) on the stage.
: and-then ( stage outcome xt -- stage outcome )
  over ok? if nip over swap execute else drop then ;
: stage-limit! ( bytes stage -- ) stage-limit ! ;
: stage-manifest-use ( c-addr u stage -- ) stage-manifest manifest-use ;
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
: slabs-start ( stage -- outcome )
  cons-numbers-max over stage-name-map fields-init drop
  cons-numbers-max over stage-level-map fields-init drop
  cons-numbers-max over stage-expr-map fields-init drop
  payload-limit over stage-by-name fields-init drop
  /staged payload-limit 1- 2 pick stage-decl-records slab-init drop maps-start ;
: tier-marked ( stage -- outcome ) dup stage-start swap stage-tier tier-mark ;
: export-start ( stage -- outcome )
  dup stage-export export-init dup ok? 0= if nip exit then drop
  dup handlers-set dup stage-export swap stage-manifest manifest-init ;
\ An empty stage whose expression table starts at 2^log2 slots: ok, or
\ full (stage-free then frees what was made). The record must not hold
\ memory: stage-free first.
: stage-init ( log2 stage -- outcome )
  dup /stage erase tuck tier-start ['] slabs-start and-then ['] tier-marked and-then
  ['] export-start and-then staging-empty stage-state! ;
: stage-unmap ( stage -- )
  dup stage-name-map slab-free dup stage-level-map slab-free stage-expr-map slab-free ;
: stage-free ( stage -- )
  dup stage-tier tier-free dup stage-export export-free dup stage-manifest manifest-free
  dup stage-unmap dup stage-decl-records slab-free dup stage-by-name slab-free
  dup stage-reach heap-release /stage erase ;

\ ---- Reading. A failed read rolls the stage back: the tier to the mark
\ stage-init took, the maps to their first entries, no declarations.
: own-clear ( stage -- outcome )
  dup stage-name-map slab-clear dup stage-level-map slab-clear
  dup stage-expr-map slab-clear dup stage-decl-records slab-clear
  dup stage-by-name slab-clear 0 over stage-mdata ! 0 over stage-marks !
  0 over stage-why ! maps-start ;
: stage-rollback ( stage -- outcome )
  dup stage-start over stage-tier tier-rollback ['] own-clear and-then
  staging-empty stage-state! ;
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
\ The expression records of the input tier, walked by number: a letE
\ spans two.
: input-exprs ( stage -- slab ) stage-tier tier-exprs cons-records ;
: record-span ( addr -- units ) record-let? if 2 else 1 then ;

\ Constants. What a constant of name n resolves to: its declaration + 1,
\ or 0 when several declarations have the name; false when none has.
: resolution ( n stage -- u true | false )
  tuck stage-by-name fields@ dup 0= if nip exit then
  dup 1- rot staged-prev@ if drop 0 then true ;
: unknown-constant ( n stage -- outcome )
  tuck stage-culprit ! c" unknown constant" swap stage-why ! outcome-invalid ;
: const-resolve ( addr stage -- outcome )
  over quad-a u32@ over resolution if nip tag-const swap pack-head swap quad-head u32!
    outcome-ok exit then
  swap quad-a u32@ swap unknown-constant ;
: const-at? ( addr -- flag ) quad-head u32@ head-tag tag-const = ;
: record-resolve ( addr stage -- outcome )
  over const-at? if const-resolve else 2drop outcome-ok then ;
: consts-resolve ( stage -- outcome )
  dup input-exprs 0 begin 2dup swap slab-count < while
    2dup swap slab-at dup >r 3 pick record-resolve
    ok? 0= if r> drop 2drop drop outcome-invalid exit then r> record-span +
  repeat 2drop drop outcome-ok ;

\ Marks, only when an mdata record was staged. The reach bytes (heap,
\ freed after sealing) hold one byte per expression number: 1 when the
\ expression is or holds an mdata record. Children have smaller numbers
\ than their parents, so one pass in number order fills them.
: reach@ ( e stage -- flag ) stage-reach @ + c@ 0<> ;
: a-reach? ( addr stage -- flag ) swap quad-a u32@ swap reach@ ;
: b-reach? ( addr stage -- flag ) swap quad-b u32@ swap reach@ ;
: body-reach? ( addr stage -- flag ) swap body-of swap reach@ ;
: two-children? ( tag -- flag ) dup tag-app = over binder-tag? or swap let-tag? or ;
: one-child? ( tag -- flag ) dup tag-proj = swap tag-mdata = or ;
: reaches? ( addr stage -- flag )
  over quad-head u32@ head-tag >r r@ tag-mdata = if 2drop r> drop true exit then
  r@ two-children? r@ one-child? or 0= if 2drop r> drop false exit then
  2dup a-reach? r@ two-children? if >r 2dup b-reach? r> or then
  r> let-tag? if >r body-reach? r> or else nip nip then ;
: reach-fill ( stage -- )
  dup input-exprs 0 begin 2dup swap slab-count < while
    2dup swap slab-at dup 4 pick reaches? 1 and 2 pick 5 pick stage-reach @ + c!
    record-span +
  repeat 2drop drop ;
: reach-make ( stage -- outcome )
  dup input-exprs slab-count 1 max dup allocate if 2drop drop outcome-full exit then
  dup rot erase swap stage-reach ! outcome-ok ;
: reach-free ( stage -- ) stage-reach heap-release ;
\ Whether a declaration's type, value or recursor rules reach one.
: field-reach? ( e stage -- flag ) over none? if 2drop false else reach@ then ;
: rules-reach? ( t stage -- flag )
  2dup stage-tuples tuple-length 0 ?do
    i 2 + 2 pick 2 pick stage-tuples tuple-item over reach@ if 2drop true unloop exit then
  3 +loop 2drop false ;
: decl-reach? ( d stage -- flag )
  2dup staged-type@ over field-reach? >r 2dup staged-value@ over field-reach? r> or >r
  2dup staged-kind@ kind-recursor = if 5 2 pick 2 pick staged-item swap rules-reach? nip
  else 2drop false then r> or ;
: staged-mark ( d stage -- )
  tuck staged-at staged-head dup u32@ staged-marked-bit or swap u32!
  1 swap stage-marks +! ;
: decls-mark ( stage -- )
  dup stage-decls 0 ?do i over decl-reach? if i over staged-mark then loop drop ;
: stage-marking ( stage -- outcome )
  dup stage-mdata @ 0= if drop outcome-ok exit then
  dup reach-make dup ok? 0= if nip exit then drop
  dup reach-fill dup decls-mark reach-free outcome-ok ;

\ Sealing: the array covers every name, the marks are set, every constant
\ is resolved, and the tier is sealed (its tables spread, its slabs
\ trimmed; trimming the declarations and the array only saves memory, so
\ a RESIZE that fails there is no failure). Any failure breaks the stage.
: tier-sealing ( stage -- outcome )
  dup stage-decl-records slab-trim drop dup stage-by-name slab-trim drop
  stage-tier tier-seal ;
: stage-seal ( stage -- outcome )
  dup staging-filled stage-in? 0= if drop outcome-invalid exit then
  dup names-covered ['] stage-marking and-then ['] consts-resolve and-then
  ['] tier-sealing and-then staging-sealed stage-state! ;
: stage-load ( c-addr u stage -- outcome )
  dup >r stage-read dup ok? if drop r> stage-seal else r> drop then ;
: stage-load-unchecked ( c-addr u stage -- outcome )
  dup >r stage-read-unchecked dup ok? if drop r> stage-seal else r> drop then ;

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

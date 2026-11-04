\ Run records (plan task 2.2.5; ADR 0012 E8): the evidence of one check of
\ a Lean export by the first checker, written as one JSON text in the
\ format leanforth-run-record, version 0.1
\ (schemas/run-record-0.1.schema.json; fields, rules and use:
\ docs/programming/RUN_RECORDS.md). LeanForth-specific and untrusted: it
\ decides no verdict, and the checker never reads a record. A record
\ claims no more than the checker established: every verdict is read
\ after the run from the declaration's slot in the checked environment
\ the run made (lf-env-readable, lf-env-axioms), never from another one
\ that happens to be current (rr-ours?). Accepted only for a final slot whose
\ outcome is ok, and then labelled "experimental, not independently
\ audited", with the axiom set that slot holds; a slot that is not final
\ is invalid when its check began (it or its publication failed, and the
\ run stopped there, ADR 0012 E4) and not-checked when it never began.
\
\ One run, in this order (tests/support/run-records.fs is the driver):
\ - rr-start ( c-addr u -- outcome ) reads the export file named c-addr u
\   before it is checked: its SHA-256, bytes and lines (rr-hash); its
\   metadata, the exporter, format and Lean versions, with the NDJSON
\   reader; and its manifest (manifest.fs), whose outcome, field and
\   reason are kept whatever they are. invalid when the file cannot be
\   opened or read, full when the heap has no room for the reader.
\ - rr-settings! ( fuel deps -- ) gives every check fuel and the
\   environment room for deps dependencies, as lf-check-input takes them.
\ - The caller loads the same file into this context's input with its
\   importer (in phase 2 the test-only transport,
\   tests/support/ndjson-input.fs), gives the importer's outcome to
\   rr-read! and, when it is ok, calls rr-check.
\ - rr-check ( -- ) checks every declaration of the input in input order
\   in a new environment, which it keeps current, as lf-check-input does
\   (check-declaration.fs: lf-check-declaration, the budget, no new
\   context after a THROW), one declaration at a time with lf-env-step,
\   so that it can keep each declaration's diagnostic and step after its
\   check. The run's outcome is ok when every slot ended final.
\ - rr-finish ( c-addr u -- outcome ) reads the file again: invalid when it
\   cannot, or when its digest, bytes or lines changed during the run (the
\   record would describe another input than the one checked).
\ - rr-write ( -- outcome ) writes the record into the module's buffer,
\   rr-text ( -- c-addr u ); rr-save ( c-addr u -- outcome ) writes that
\   to the file named c-addr u, then a line feed. rr-write is full when
\   the text passes rr-text-room bytes, a name rr-name-room or a host
\   text rr-note-room; invalid when a final slot's outcome is not the one
\   its step published, when an accepted slot's axiom set is unreadable
\   or not empty (allowlist version 0 names no axiom), when the run made
\   its environment but that is freed or not the current one, when a text
\   breaks the text rule (below) or a name, host or metadata text is
\   blank, or when a number is outside I-JSON's exact range. A run that
\   could not make its environment lists no declaration. A failed text is
\   never a record: the writer never writes what the schema refuses.
\ - rr-release ( -- ) frees the run's environment; rr-start does it too.
\ rr-source! ( c-addr u flag -- outcome ) names the LeanForth commit, 40
\ lowercase hexadecimal digits (else invalid), and whether the working
\ tree differed from it; rr-no-source forgets them, and the record then
\ says null for both. The host's Forth, version and engine come from
\ Gforth's words where the host has them (rr-forth-version, rr-program),
\ else "unknown".
\
\ It reads bytes (c@) only to decode UTF-8 for the text rule.
\
\ Requires: lib/json-write.fs, lib/sha256.fs, import/ndjson.fs,
\ import/manifest.fs, present/print-names.fs (names as text) and
\ kernel/check-declaration.fs, read only through public words.
\ State: one shared record, run-record, which holds the run's facts, the
\ JSON writer, the text and, through its export and manifest records,
\ heap buffers while rr-start runs: one run at a time, in any context, as
\ with the NDJSON counter's records; not re-entrant. The tables are
\ constant after loading. The file loads in decimal whatever BASE is,
\ then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/json-write.fs
require ../lib/sha256.fs
require ../core/diagnostics.fs
require ../core/input.fs
require ../present/print-names.fs
require ../kernel/check-declaration.fs
require ./ndjson.fs
require ./manifest.fs

65536 constant rr-text-room       \ longest record text, in bytes
1024 constant rr-name-room        \ longest declaration name written
128 constant rr-note-room         \ longest metadata, manifest or source text kept
4096 constant rr-block-room       \ bytes read at a time while hashing
8 constant rr-depth               \ deepest nesting the writer allows
: rr-schema ( -- c-addr u ) s" leanforth-run-record" ;
: rr-version ( -- c-addr u ) s" 0.1" ;
: rr-label ( -- c-addr u ) s" experimental, not independently audited" ;

\ A note: a text of at most rr-note-room bytes, its length first; a
\ negative length means none (written as null). rr-note: names one.
rr-note-room cell+ aligned constant /rr-note
: rr-note: ( n "name" -- n' ) aligned /rr-note +field ;
: rr-note ( note -- c-addr u ) dup cell+ swap @ ;
: rr-note? ( note -- flag ) @ 0< 0= ;
: rr-forget ( note -- ) -1 swap ! ;
\ Keep c-addr u in the note: ok, or full, with the note unchanged, when
\ it is longer than rr-note-room.
: rr-note! ( c-addr u note -- outcome )
  over rr-note-room > if drop 2drop outcome-full exit then
  2dup ! cell+ swap move outcome-ok ;

\ The facts of a file: its SHA-256 as text, its bytes and lines (doubles)
\ and whether the bytes so far end inside a line, after no line feed.
begin-structure /rr-facts
  sha-digest-bytes 2* +field facts-hex
  aligned 2 cells +field facts-bytes
  2 cells +field facts-lines
  field: facts-open
end-structure

\ What a check left, kept after its step: the outcome lf-env-step
\ published, the diagnostic (code, numbers, site) and the step reached.
begin-structure /rr-step
  field: kept-outcome
  field: kept-code
  field: kept-first
  field: kept-second
  field: kept-site
  field: kept-step
end-structure

begin-structure /rr
  /sha256 +field rr-sha
  sha-digest-bytes +field rr-digest
  aligned /rr-facts +field rr-before        \ the file when the run starts
  /rr-facts +field rr-after                 \ the same, read again at its end
  rr-block-room +field rr-block
  rr-note: rr-exporter  rr-note: rr-exporter-version  rr-note: rr-format
  rr-note: rr-lean  rr-note: rr-githash
  field: rr-manifest-outcome
  rr-note: rr-manifest-key  rr-note: rr-manifest-reason
  rr-note: rr-commit
  field: rr-modified        \ true when the tree differed from the commit
  field: rr-fuel  field: rr-deps
  field: rr-read            \ the importer's outcome
  field: rr-checked         \ true once rr-check ran
  field: rr-stepped         \ declarations whose check began
  field: rr-env             \ the environment rr-check made, or 0
  field: rr-own             \ true once rr-check made its environment
  field: rr-run             \ the run's outcome
  field: rr-fault           \ the first failure rr-write found itself, or ok
  lf-input-capacity /rr-step * +field rr-kept
  field: rr-name-size
  rr-name-room +field rr-name-buf
  field: rr-text-size
  rr-text-room +field rr-text-buf
  aligned /export +field rr-export
  aligned /manifest +field rr-manifest
  aligned rr-depth 0 jw-size +field rr-writer
end-structure
create run-record /rr allot  run-record /rr erase
rr-depth 0 run-record rr-writer jw-init 0= [if] .( run-record.fs: writer) cr abort [then]

\ The run's data back to "nothing known": no metadata, the manifest and
\ the read not yet decided, no check. Settings and source stay.
: rr-unknown ( -- )
  run-record dup rr-exporter rr-forget dup rr-exporter-version rr-forget
  dup rr-format rr-forget dup rr-lean rr-forget rr-githash rr-forget ;
: rr-reset ( -- )
  rr-unknown outcome-invalid run-record rr-manifest-outcome !
  0 run-record rr-manifest-key ! 0 run-record rr-manifest-reason !
  outcome-invalid run-record rr-read ! false run-record rr-checked ! ;
: rr-no-source ( -- ) run-record rr-commit rr-forget false run-record rr-modified ! ;
rr-reset rr-no-source

\ Hashing a file: SHA-256, bytes and lines, read rr-block-room bytes at a
\ time. A last line without a line feed counts as a line.
: rr-lf ( -- c-addr u ) s\" \n" ;
: rr-feeds ( c-addr u -- n )   \ line feeds in c-addr u
  0 -rot begin rr-lf search while 1 /string rot 1+ -rot repeat 2drop ;
: rr-d+! ( u addr -- ) >r 0 r@ 2@ d+ r> 2! ;
: rr-ends-open? ( c-addr u -- flag ) + 1- 1 rr-lf compare 0<> ;
: rr-take ( c-addr u facts -- )
  >r 2dup run-record rr-sha sha256-update  dup r@ facts-bytes rr-d+!
  2dup rr-feeds r@ facts-lines rr-d+!  rr-ends-open? r> facts-open ! ;
\ One block of the file into the facts: the bytes read, 0 at its end, or
\ -1 after a read error.
: rr-chunk ( fid facts -- n )
  >r run-record rr-block rr-block-room rot read-file if drop r> drop -1 exit then
  dup if run-record rr-block over r@ rr-take then r> drop ;
: rr-chunks ( fid facts -- outcome )
  begin 2dup rr-chunk dup 0> while drop repeat
  nip nip 0< if outcome-invalid else outcome-ok then ;
: rr-facts-start ( facts -- ) /rr-facts erase run-record rr-sha sha256-init ;
: rr-facts-end ( facts -- )
  dup facts-open @ if 1 over facts-lines rr-d+! then
  run-record rr-digest dup run-record rr-sha sha256-final swap facts-hex digest>hex ;
: rr-hash-open ( fid facts -- outcome )
  2dup rr-chunks >r drop close-file r> swap if drop outcome-invalid then ;
\ The facts of the file named c-addr u: ok, or invalid when it cannot be
\ opened, read or closed.
: rr-hash ( c-addr u facts -- outcome )
  dup rr-facts-start >r r/o bin open-file if drop r> drop outcome-invalid exit then
  r@ rr-hash-open r> over ok? if rr-facts-end else drop then ;

\ The metadata, read with the NDJSON reader: every record kind accepted,
\ the metadata record's texts kept (a text longer than a note stays
\ none, null in the record; the reader hands over only the pinned
\ versions, which are short).
: rr-meta-one ( record xt note -- record ) >r over swap execute 2@ r> rr-note! drop ;
: rr-exporter-meta ( record -- record )
  ['] meta-exporter run-record rr-exporter rr-meta-one
  ['] meta-exporter-version run-record rr-exporter-version rr-meta-one
  ['] meta-format-version run-record rr-format rr-meta-one ;
: rr-on-meta ( record -- outcome )
  rr-exporter-meta ['] meta-lean-version run-record rr-lean rr-meta-one
  ['] meta-lean-githash run-record rr-githash rr-meta-one drop outcome-ok ;
: rr-any ( record -- outcome ) drop outcome-ok ;
: rr-handlers ( export -- )
  dup export-handlers-clear kind-count 0 do ['] rr-any i 2 pick export-handler ! loop
  ['] rr-on-meta kind-meta rot export-handler ! ;

\ The manifest's outcome and, for a failure, the field and the reason
\ export-error gives; ok when the export matches the manifest beside it.
: rr-manifest-keep ( outcome -- )
  dup run-record rr-manifest-outcome ! ok? if exit then
  run-record rr-export export-error run-record rr-manifest-reason rr-note! drop
  run-record rr-manifest-key rr-note! drop drop ;
: rr-manifest-read ( c-addr u -- outcome )
  run-record rr-manifest manifest-read rr-manifest-keep outcome-ok ;
: rr-manifest-check ( c-addr u -- outcome )
  run-record rr-export run-record rr-manifest manifest-init
  dup ok? if drop rr-manifest-read else nip nip then
  run-record rr-manifest manifest-free ;
: rr-passes ( c-addr u -- outcome )
  run-record rr-export dup rr-handlers >r 2dup r> export-read drop rr-manifest-check ;
: rr-reads ( c-addr u -- outcome )
  run-record rr-export export-init dup ok? if drop rr-passes else nip nip then
  run-record rr-export export-free ;

\ Start a run on the export file named c-addr u, as described above.
: rr-release ( -- )
  run-record rr-env dup @ ?dup if lf-env-free drop then 0 swap ! ;
: rr-start ( c-addr u -- outcome )
  rr-release rr-reset 2dup run-record rr-before rr-hash
  dup ok? if drop rr-reads else nip nip then ;
: rr-settings! ( fuel deps -- ) run-record rr-deps ! run-record rr-fuel ! ;
: rr-read! ( outcome -- ) run-record rr-read ! ;
: rr-source! ( c-addr u flag -- outcome )
  >r 2dup 40 hex-text? 0= if 2drop r> drop outcome-invalid exit then
  run-record rr-commit rr-note! r> 0<> run-record rr-modified ! ;

\ Checking, one declaration at a time (see the header).
: rr-step-of ( d -- step ) /rr-step * run-record rr-kept + ;
: rr-keep ( outcome d -- )
  rr-step-of >r r@ kept-outcome ! lf-diag@ r@ kept-code ! r@ kept-site !
  r@ kept-second ! r@ kept-first ! lf-check-step@ r> kept-step ! ;
\ Check declaration d and keep what it left: whether the run must stop,
\ after a fault or a THROW (the context is then spent).
: rr-step ( d -- stop? )
  dup 1+ run-record rr-stepped ! dup >r ['] lf-check-declaration swap lf-env-step
  swap r> rr-keep lf-env-spent? or ;
: rr-steps ( n -- ) 0 ?do i rr-step if unloop exit then loop ;
\ The run's own environment, the one rr-check made, is the current one:
\ verdicts are never read from any other (review F1).
: rr-ours? ( -- flag ) run-record rr-env @ dup if lf-env = else drop false then ;
\ A snapshot of every slot of the run's own environment.
: rr-viewed? ( -- flag )
  rr-ours? if lf-env-view ok? lf-name-storage-valid? and else false then ;
: rr-final? ( d -- flag ) lf-env-readable dup if nip then ;
: rr-all-final? ( -- flag ) true lf-input-count 0 ?do i rr-final? and loop ;
: rr-confirm ( -- outcome )
  rr-viewed? if rr-all-final? flag>outcome else outcome-invalid then ;
: rr-run-in ( env -- outcome )
  dup run-record rr-env ! true run-record rr-own ! lf-env-use
  dup ok? if drop lf-input-count rr-steps rr-confirm then ;
\ A new run: an earlier run's environment freed, no step taken, and every
\ kept outcome invalid until its step publishes one, never ok (0).
: rr-unkept ( -- )
  run-record rr-kept lf-input-capacity /rr-step * erase
  lf-input-capacity 0 do outcome-invalid i rr-step-of kept-outcome ! loop ;
: rr-begun ( -- )
  rr-release rr-unkept true run-record rr-checked ! 0 run-record rr-stepped !
  false run-record rr-own ! ;
: rr-check ( -- )
  rr-begun run-record rr-fuel @ lf-check-budget run-record rr-deps @ lf-env-new
  dup ok? if drop rr-run-in else nip then run-record rr-run ! ;

\ The end of a run: the file read again, unchanged.
: rr-same-input? ( -- flag )
  run-record dup rr-before /rr-facts rot rr-after /rr-facts compare 0= ;
: rr-finish ( c-addr u -- outcome )
  run-record rr-after rr-hash dup ok? if drop rr-same-input? flag>outcome then ;

\ The host, through Gforth's words where it has them: the version, and
\ the program that runs, its engine.
: rr-forth ( -- c-addr u )
  s" gforth" environment? if 2drop s" gforth" else s" unknown" then ;
[defined] version-string [if]
: rr-forth-version ( -- c-addr u ) version-string ;
[else]
: rr-forth-version ( -- c-addr u ) s" unknown" ;
[then]
[defined] arg [if]
: rr-program ( -- c-addr u ) 0 arg ;
[else]
: rr-program ( -- c-addr u ) s" unknown" ;
[then]
\ The engine: the program's file name, without its folder.
: rr-basename ( c-addr u -- c-addr' u' )
  begin 2dup s" /" search while 1 /string 2swap 2drop repeat 2drop ;
: rr-engine ( -- c-addr u ) rr-program rr-basename ;
: rr-cell-bits ( -- n ) 0 1 begin ?dup while 1 lshift swap 1+ swap repeat ;

\ The text rule, the owner's rule for program receipts 0.2
\ (docs/programming/PROGRAM_RECEIPTS.md): a text is valid UTF-8 and holds
\ no control character (C0, C1), no format character (Unicode Cf as of
\ 15.1: bidirectional controls, zero-width characters, tags), no line or
\ paragraph separator and no surrogate. These are the ranges of code
\ points it bans, the same as the schema's text pattern (the tests compare
\ the two at every range's ends). A shown text also has a character that
\ is not a space, so it is neither empty nor blank.
create rr-banned
  $0000 , $001f ,  $007f , $009f ,  $00ad , $00ad ,  $0600 , $0605 ,  $061c , $061c ,
  $06dd , $06dd ,  $070f , $070f ,  $0890 , $0891 ,  $08e2 , $08e2 ,  $180e , $180e ,
  $200b , $200f ,  $2028 , $202e ,  $2060 , $2064 ,  $2066 , $206f ,  $d800 , $dfff ,
  $feff , $feff ,  $fff9 , $fffb ,  $110bd , $110bd ,  $110cd , $110cd ,
  $13430 , $1343f ,  $1bca0 , $1bca3 ,  $1d173 , $1d17a ,  $e0001 , $e0001 ,
  $e0020 , $e007f ,
here rr-banned - 2 cells / constant rr-banned#
create rr-spaces   \ the space characters the rule does not ban already
  $0020 , $0020 ,  $00a0 , $00a0 ,  $1680 , $1680 ,  $2000 , $200a ,  $202f , $202f ,
  $205f , $205f ,  $3000 , $3000 ,
here rr-spaces - 2 cells / constant rr-spaces#
: rr-range ( table k -- lo hi ) 2* cells + dup @ swap cell+ @ ;
: rr-among? ( code table n -- flag )
  0 ?do 2dup i rr-range between? if 2drop true unloop exit then loop 2drop false ;
: rr-banned? ( code -- flag ) rr-banned rr-banned# rr-among? ;
: rr-blank? ( code -- flag ) rr-spaces rr-spaces# rr-among? ;
\ Decoding valid UTF-8: the code point of the n-byte character at c-addr,
\ from the lead byte's low bits and six bits of each byte after it.
: rr-mask ( n -- mask )
  case 1 of $7f endof 2 of $1f endof 3 of $0f endof $07 swap endcase ;
: rr-tail ( code c-addr -- code' ) c@ $3f and swap 6 lshift or ;
: rr-decode ( c-addr n -- code )
  over c@ over rr-mask and -rot 1 ?do dup i chars + rot swap rr-tail swap loop drop ;
: rr-next ( c-addr u -- c-addr' u' code )
  2dup utf8-length >r over r@ rr-decode -rot r> /string rot ;
\ Whether xt ( code -- flag ) holds for some character of valid UTF-8.
: rr-some? ( c-addr u xt -- flag )
  >r begin dup while rr-next r@ execute if 2drop r> drop true exit then repeat
  2drop r> drop false ;
: rr-rule? ( c-addr u -- flag )
  2dup utf8-valid? if ['] rr-banned? rr-some? 0= else 2drop false then ;
: rr-seen? ( code -- flag ) rr-blank? 0= ;
: rr-shown? ( c-addr u -- flag )
  2dup rr-rule? if ['] rr-seen? rr-some? else 2drop false then ;

\ Numbers a record holds are exact in every JSON reader: within
\ +-(2^53 - 1), I-JSON's range (RFC 7493).
: rr-power ( -- d ) 1 0 53 0 do 2dup d+ loop -1 m+ ;
rr-power 2constant rr-exact
: rr-exact? ( d -- flag ) dabs rr-exact 2swap d< 0= ;

\ Writing: the writer's sink appends to the text buffer; jw-limit keeps
\ the text within it.
: rr-text ( -- c-addr u ) run-record dup rr-text-buf swap rr-text-size @ ;
: rr-sink ( c-addr u -- ) tuck rr-text + swap move run-record rr-text-size +! ;
: rr-w ( -- writer ) run-record rr-writer ;
: rr-object ( -- ) rr-w jw-open-object ;
: rr-end-object ( -- ) rr-w jw-close-object ;
: rr-array ( -- ) rr-w jw-open-array ;
: rr-end-array ( -- ) rr-w jw-close-array ;
: rr-key ( c-addr u -- ) rr-w jw-key ;
: rr-null ( -- ) rr-w jw-null ;
\ The first failure rr-write finds itself.
: rr-fail ( outcome -- ) run-record rr-fault dup @ ok? if ! else 2drop then ;
\ Values. A string that breaks the text rule, a shown one that is blank or
\ longer than its room, and a number outside I-JSON's range fail the text
\ as invalid (full for the length): the record never holds what its
\ schema refuses.
: rr-string ( c-addr u -- )
  2dup rr-rule? 0= if outcome-invalid rr-fail then rr-w jw-string ;
: rr-shown ( c-addr u room -- )
  over < if outcome-full rr-fail then
  2dup rr-shown? 0= if outcome-invalid rr-fail then rr-string ;
: rr-int ( n -- ) dup s>d rr-exact? 0= if outcome-invalid rr-fail then rr-w jw-n ;
: rr-ud ( ud -- )
  2dup rr-exact? 0= if outcome-invalid rr-fail then decimal-text rr-w jw-digits ;
: rr-outcome ( outcome -- ) outcome-text rr-string ;
: rr-note-out ( note -- ) dup rr-note? if rr-note rr-string else drop rr-null then ;
: rr-member ( note c-addr u -- ) rr-key rr-note-out ;
\ A note that, when it is there, must be shown.
: rr-shown-out ( note c-addr u -- )
  rr-key dup rr-note? if rr-note rr-note-room rr-shown else drop rr-null then ;

\ The sections, in the record's order.
: rr-head ( -- )
  s" schema" rr-key rr-schema rr-string s" schemaVersion" rr-key rr-version rr-string ;
: rr-facts-out ( facts -- )
  s" sha256" rr-key dup facts-hex sha-digest-bytes 2* rr-string
  s" bytes" rr-key dup facts-bytes 2@ rr-ud s" lines" rr-key facts-lines 2@ rr-ud ;
\ The manifest's outcome, field and reason; a failure's reason is shown.
: rr-why-out ( -- )
  run-record dup rr-manifest-reason swap rr-manifest-outcome @ ok?
  if s" reason" rr-member else s" reason" rr-shown-out then ;
: rr-manifest-out ( -- )
  s" manifest" rr-key rr-object
  s" outcome" rr-key run-record rr-manifest-outcome @ rr-outcome
  run-record rr-manifest-key s" field" rr-member rr-why-out rr-end-object ;
: rr-input-out ( -- )
  s" input" rr-key rr-object run-record rr-before rr-facts-out rr-manifest-out
  rr-end-object ;
: rr-exporter-out ( -- )
  run-record rr-exporter s" exporter" rr-shown-out
  run-record rr-exporter-version s" exporterVersion" rr-shown-out
  run-record rr-format s" format" rr-shown-out ;
: rr-export-out ( -- )
  s" export" rr-key rr-object rr-exporter-out run-record rr-lean s" lean" rr-shown-out
  run-record rr-githash s" leanGithash" rr-shown-out rr-end-object ;
: rr-modified-out ( -- )
  run-record dup rr-commit rr-note? if rr-modified @ rr-w jw-bool else drop rr-null then ;
: rr-source-out ( -- )
  s" leanforth" rr-key rr-object run-record rr-commit s" commit" rr-member
  s" modified" rr-key rr-modified-out rr-end-object ;
: rr-host-shown ( c-addr u key-addr key-u -- ) rr-key rr-note-room rr-shown ;
: rr-host-out ( -- )
  s" host" rr-key rr-object rr-forth s" forth" rr-host-shown
  rr-forth-version s" version" rr-host-shown rr-engine s" engine" rr-host-shown
  s" cellBits" rr-key rr-cell-bits rr-int rr-end-object ;
: rr-setting ( n c-addr u -- ) rr-key rr-int ;
: rr-stores ( -- )
  lf-term-capacity s" terms" rr-setting lf-level-capacity s" levels" rr-setting
  lf-name-capacity s" names" rr-setting lf-input-capacity s" declarations" rr-setting ;
: rr-limits ( -- )
  lf-env-dep-capacity s" dependenciesPerCheck" rr-setting
  lf-param-capacity s" parameters" rr-setting
  lf-cref-argument-capacity s" referenceLevels" rr-setting ;
: rr-settings-out ( -- )
  s" settings" rr-key rr-object run-record rr-fuel @ s" fuel" rr-setting
  run-record rr-deps @ s" dependencyPool" rr-setting rr-stores rr-limits rr-end-object ;

\ The run: the importer's outcome, the run's (not-run without rr-check),
\ and the environment's run mode and allowlist version (null without one).
: rr-made ( -- env|0 ) run-record dup rr-checked @ if rr-env @ else drop 0 then ;
: rr-run-out ( -- )
  run-record dup rr-checked @ if rr-run @ rr-outcome exit then
  drop s" not-run" rr-string ;
: rr-mode-text ( mode -- c-addr u )
  lf-mode-final = if s" final" else s" development" then ;
: rr-mode-out ( -- )
  rr-made ?dup if lf-envh-mode @ rr-mode-text rr-string else rr-null then ;
: rr-allowlist-out ( -- ) rr-made ?dup if lf-envh-version @ rr-int else rr-null then ;
: rr-check-out ( -- )
  s" check" rr-key rr-object s" read" rr-key run-record rr-read @ rr-outcome
  s" run" rr-key rr-run-out s" mode" rr-key rr-mode-out
  s" allowlistVersion" rr-key rr-allowlist-out rr-end-object ;

\ A declaration's name, as the term printer writes it, collected in the
\ name buffer; a longer name fails the text as full.
: rr-name ( -- c-addr u ) run-record dup rr-name-buf swap rr-name-size @ ;
: rr-name-sink ( c-addr u -- )
  dup run-record rr-name-size @ + rr-name-room > if 2drop outcome-full rr-fail exit then
  tuck rr-name + swap move run-record rr-name-size +! ;
: rr-name-out ( d -- )
  0 run-record rr-name-size ! lf-input-name ['] rr-name-sink lf-pp-name-to
  rr-name rr-name-room rr-shown ;

\ A declaration's verdict. Accepted: the label and the axiom set read from
\ the slot, which must be empty. Any other: its name and the diagnostic its
\ check left (null when there is none).
: rr-axioms-out ( d -- )
  lf-env-axioms ok? 0= or if outcome-invalid rr-fail then
  s" axioms" rr-key rr-array rr-end-array ;
: rr-accepted-out ( d -- )
  s" verdict" rr-key s" accepted" rr-string
  s" label" rr-key rr-label rr-string rr-axioms-out ;
: rr-site ( site -- c-addr u ) ?dup if count else s" " then ;
: rr-numbers-out ( step -- )
  s" numbers" rr-key rr-array dup kept-first @ rr-int kept-second @ rr-int rr-end-array ;
: rr-code-out ( step -- step )
  s" code" rr-key dup kept-code @ dup rr-int s" reason" rr-key lf-diag-name rr-string ;
: rr-reason-out ( step -- )
  rr-object rr-code-out s" site" rr-key dup kept-site @ rr-site rr-string
  dup rr-numbers-out s" step" rr-key kept-step @ rr-int rr-end-object ;
: rr-diagnostic-out ( step -- )
  s" diagnostic" rr-key
  dup kept-code @ lf-diag-none = if drop rr-null else rr-reason-out then ;
: rr-failed-out ( d outcome -- )
  s" verdict" rr-key rr-outcome rr-step-of rr-diagnostic-out ;
\ The slot's outcome must be the one the step published.
: rr-agrees ( d outcome -- d outcome )
  2dup swap rr-step-of kept-outcome @ <> if outcome-invalid rr-fail then ;
: rr-verdict-out ( d slot -- )
  lf-slot-outcome@ rr-agrees dup ok? if drop rr-accepted-out else rr-failed-out then ;
\ A slot that is not final: invalid, with its diagnostic, when its check
\ began; not-checked when the run stopped before it.
: rr-unchecked-out ( d -- ) drop s" verdict" rr-key s" not-checked" rr-string ;
: rr-began? ( d -- flag ) run-record rr-stepped @ < ;
: rr-open-out ( d -- )
  dup rr-began? if outcome-invalid rr-failed-out else rr-unchecked-out then ;
: rr-decl-out ( d -- )
  rr-object s" index" rr-key dup rr-int s" name" rr-key dup rr-name-out
  dup lf-env-readable if rr-verdict-out else rr-open-out then rr-end-object ;
\ Every declaration, in input order, read in a snapshot of every slot of
\ the run's own environment; none when no check ran or the run could not
\ make its environment (the run's outcome says why). When that environment
\ is freed or another one is current, the text fails as invalid.
: rr-made-own? ( -- flag ) run-record dup rr-checked @ swap rr-own @ and ;
: rr-decls ( -- )
  rr-made-own? 0= if exit then rr-viewed? 0= if outcome-invalid rr-fail exit then
  lf-input-count 0 ?do i rr-decl-out loop ;
: rr-decls-out ( -- ) s" declarations" rr-key rr-array rr-decls rr-end-array ;

\ Write the record (see the header): the writer's outcome, else the first
\ failure found while writing.
: rr-begin-text ( -- )
  0 run-record rr-text-size ! outcome-ok run-record rr-fault !
  rr-text-room rr-w jw-limit ! ['] rr-sink rr-w jw-start ;
: rr-body ( -- )
  rr-object rr-head rr-input-out rr-export-out rr-source-out rr-host-out
  rr-settings-out rr-check-out rr-decls-out rr-end-object ;
: rr-write ( -- outcome )
  rr-begin-text rr-body rr-w jw-end dup ok? if drop run-record rr-fault @ then ;
\ The text, then a line feed, to a new file named c-addr u: ok, or invalid
\ when it cannot be created, written or closed.
: rr-save ( c-addr u -- outcome )
  w/o bin create-file if drop outcome-invalid exit then
  >r rr-text r@ write-file rr-lf r@ write-file or r> close-file or
  if outcome-invalid else outcome-ok then ;

base !   \ the BASE this file was loaded with

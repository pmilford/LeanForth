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
\ One run, in this order (bin/leanforth and tests/support/run-records.fs
\ are the drivers):
\ - rr-start ( c-addr u -- outcome ) keeps the name of the export file
\   c-addr u, the run's input from then on, and reads the file before it
\   is checked: its SHA-256, bytes and lines (rr-hash); its metadata, the
\   exporter, format and Lean versions, with the NDJSON reader; and its
\   manifest (manifest.fs), whose outcome, field and reason are kept
\   whatever they are. invalid when the file cannot be opened or read, or
\   when the metadata read or a manifest check that passed read bytes of
\   another SHA-256 (rr-moved? then true); full when the heap has no room
\   for the reader or the name is longer than rr-file-room.
\ - rr-settings! ( fuel deps -- ) gives every check fuel and the
\   environment room for deps dependencies, as lf-check-input takes them.
\ - rr-import ( flag -- outcome ) loads that same file into this context's
\   input with import/checker-input.fs, its manifest enforced when flag is
\   true (cin-read-checked, else cin-read; either way its two passes must
\   read bytes of one SHA-256, and the read then also fails unless that is
\   the SHA-256 rr-start recorded), and keeps the outcome and whether the
\   manifest was enforced. It is the only way a recorded run reads its input, and the
\   only way a record can say enforced (rr-read! and rr-file! are
\   internal). A run that is not to be recorded skips rr-start and loads
\   the file with the importer alone, rr-read-once ( c-addr u flag --
\   outcome ); rr-write then refuses (invalid).
\ - rr-check ( -- ) checks every declaration of the input in input order
\   in a new environment, which it keeps current, as lf-check-input does
\   (check-declaration.fs: lf-check-declaration, the budget, no new
\   context after a THROW), one declaration at a time with lf-env-step,
\   so that it can keep each declaration's diagnostic and step after its
\   check. The run's outcome is ok when every slot ended final. The
\   caller runs it only after a read that was ok.
\ - rr-finish ( -- outcome ) reads the file again: invalid when it cannot,
\   or when its digest, bytes or lines changed during the run (the record
\   would describe another input than the one checked).
\ - rr-write ( -- outcome ) writes the record into the module's buffer,
\   rr-text ( -- c-addr u ); rr-save ( c-addr u -- outcome ) writes that
\   to the file named c-addr u, then a line feed. rr-write is full when
\   the text passes rr-text-room bytes, a name rr-name-room or a host
\   text rr-note-room; invalid when a final slot's outcome is not the one
\   its step published, when an accepted slot's axiom set is unreadable
\   or not empty (allowlist version 0 names no axiom), when the run made
\   its environment but that is freed or not the current one (compared by
\   identity, which never repeats, not by address), when the checks ran
\   although the read was not ok, when a text breaks the text rule
\   (lib/text-rule.fs) or a name, host, metadata, reason or site text is
\   not shown, or when a number is outside I-JSON's exact range. A run
\   that could not make its environment lists no declaration. A failed
\   text is never a record: the writer never writes what the schema
\   refuses.
\ - rr-release ( -- ) frees the run's environment while it is the current
\   one, with the run's identity; rr-start and rr-check do it too. An
\   environment the caller made another one current over, or freed, is
\   never touched through its old address: it is left as it is (a leak if
\   the caller does not free it), never read stale or freed twice.
\ rr-source! ( c-addr u flag -- outcome ) names the LeanForth commit, 40
\ lowercase hexadecimal digits (else invalid), and whether the working
\ tree differed from it; rr-no-source forgets them, and the record then
\ says null for both. The host's Forth, version and engine come from
\ Gforth's words where the host has them (rr-forth-version, rr-program),
\ else "unknown".
\
\ Requires: lib/json-write.fs, lib/sha256.fs, lib/text-rule.fs,
\ import/ndjson.fs, import/manifest.fs, import/checker-input.fs
\ (rr-import), present/print-names.fs (names as text) and
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
require ./checker-input.fs
require ../lib/text-rule.fs
require ../lib/module.fs

\ Words only this module uses (rr-file!, rr-read!), in a word list that
\ is searched only while this file loads (ADR 0010's idea): so a recorded
\ run reads its input only through rr-import of rr-start's file. Tests
\ reach them with `rr-internal order+`.
wordlist constant rr-internal
rr-internal order+

65536 constant rr-text-room       \ longest record text, in bytes
255 constant rr-site-room         \ longest diagnostic site: a counted string's
4096 constant rr-file-room        \ longest name of the export file kept
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
  sha-digest-bytes 2* +field rr-seen        \ the metadata read's digest
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
  \ rr-own stays true after rr-release clears rr-env and rr-env-id: a run
  \ that made its environment and lost it can no longer be written.
  field: rr-env             \ the environment rr-check made, or 0
  field: rr-env-id          \ its identity (environment.fs), or 0
  field: rr-own             \ true once rr-check made its environment
  field: rr-enforced        \ true when rr-import read the input with its manifest checked
  field: rr-moved           \ true when the checked read loaded other bytes
  field: rr-file-size       \ the export file rr-start keeps: its name's length
  rr-file-room +field rr-file-buf
  field: rr-run             \ the run's outcome
  field: rr-fault           \ the first failure rr-write found itself, or ok
  lf-input-default /rr-step * +field rr-kept   \ at most lf-input-default declarations
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
: rr-unread ( -- )
  outcome-invalid run-record rr-read ! false run-record rr-enforced !
  false run-record rr-moved ! false run-record rr-checked ! 0 run-record rr-file-size ! ;
: rr-reset ( -- )
  rr-unknown outcome-invalid run-record rr-manifest-outcome !
  0 run-record rr-manifest-key ! 0 run-record rr-manifest-reason ! rr-unread ;
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
  run-record rr-digest dup run-record rr-sha sha256-final swap facts-hex sha256-hex ;
: rr-hash-open ( fid facts -- outcome )
  2dup rr-chunks >r drop close-file r> swap if drop outcome-invalid then ;
\ The facts of the file named c-addr u: ok, or invalid when it cannot be
\ opened, read or closed.
: rr-hash ( c-addr u facts -- outcome )
  dup rr-facts-start >r r/o bin open-file if drop r> drop outcome-invalid exit then
  r@ rr-hash-open r> over ok? if rr-facts-end else drop then ;

\ Every later read of the run must read the bytes rr-start hashed: a digest
\ c-addr u of a later read against that one, invalid with rr-moved? true
\ when they differ.
: rr-recorded ( -- c-addr u ) run-record rr-before facts-hex sha-digest-bytes 2* ;
: rr-matches ( c-addr u -- outcome )
  rr-recorded compare 0= dup 0= run-record rr-moved ! flag>outcome ;

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

\ The metadata read hashes what it reads, as the manifest check does
\ (manifest.fs), through the reader's tap: each line, then its line feed.
\ When it was ok, its digest must be rr-start's (rvRP3 round 3); a read
\ that failed has no whole digest, and the record keeps what it found.
: rr-tap ( export -- ) >r run-record rr-sha dup sha256-init ['] sha256-line r> export-tap! ;
: rr-tapped ( -- c-addr u )
  run-record dup rr-digest swap rr-sha sha256-final
  run-record dup rr-digest swap rr-seen sha256-hex
  run-record rr-seen sha-digest-bytes 2* ;
: rr-meta-read ( c-addr u -- outcome )
  run-record rr-export dup rr-handlers dup rr-tap export-read
  run-record rr-export export-untap ok? if rr-tapped rr-matches else outcome-ok then ;

\ The manifest's outcome and, for a failure, the field and the reason
\ export-error gives; ok when the export matches the manifest beside it,
\ and then the digest the check computed must be rr-start's.
: rr-manifest-keep ( outcome -- )
  dup run-record rr-manifest-outcome ! ok? if exit then
  run-record rr-export export-error run-record rr-manifest-reason rr-note! drop
  run-record rr-manifest-key rr-note! drop drop ;
: rr-manifest-seen ( -- c-addr u )
  run-record rr-manifest manifest-hex sha-digest-bytes 2* ;
: rr-manifest-read ( c-addr u -- outcome )
  run-record rr-manifest manifest-read dup rr-manifest-keep
  ok? if rr-manifest-seen rr-matches else outcome-ok then ;
: rr-manifest-check ( c-addr u -- outcome )
  run-record rr-export run-record rr-manifest manifest-init
  dup ok? if drop rr-manifest-read else nip nip then
  run-record rr-manifest manifest-free ;
: rr-passes ( c-addr u -- outcome )
  2dup rr-meta-read dup ok? if drop rr-manifest-check else nip nip then ;
: rr-reads ( c-addr u -- outcome )
  run-record rr-export export-init dup ok? if drop rr-passes else nip nip then
  run-record rr-export export-free ;

\ The run's own environment, the one rr-check made, is the current one:
\ verdicts are never read from any other (review F1). Environments are
\ compared by identity, which never repeats, not by address: a new
\ environment made where a freed one was is another one (rvRP 2).
: rr-ours? ( -- flag ) run-record rr-env-id @ dup if lf-env-id = else drop false then ;
\ The run's environment is freed only while it is current with the run's
\ identity, through the current environment, never through the address
\ kept: one the caller made another environment current over, or freed,
\ is never read or freed again (it stays allocated unless the caller
\ frees it: a leak, never a stale read or a double free; rvRP3 L2).
: rr-forget-env ( -- ) 0 run-record rr-env ! 0 run-record rr-env-id ! ;
: rr-release ( -- ) rr-ours? if lf-env lf-env-free drop then rr-forget-env ;

\ The export file the run keeps: rr-start's, which every later read of
\ the run uses (rvRP3 M1). rr-file! is internal (rr-internal): nothing
\ else may name the file of a recorded run (rvRP3 R2-3).
: rr-file ( -- c-addr u ) run-record dup rr-file-buf swap rr-file-size @ ;
: rr-started? ( -- flag ) rr-file nip 0<> ;
get-current rr-internal set-current
: rr-file! ( c-addr u -- flag )
  dup rr-file-room > if 2drop false exit then
  dup run-record rr-file-size ! run-record rr-file-buf swap move true ;
set-current
\ Start a run on the export file named c-addr u, as described above.
: rr-hash-file ( -- outcome ) rr-file run-record rr-before rr-hash ;
: rr-start ( c-addr u -- outcome )
  rr-release rr-reset rr-file! 0= if outcome-full exit then
  rr-hash-file dup ok? if drop rr-file rr-reads then ;
: rr-settings! ( fuel deps -- ) run-record rr-deps ! run-record rr-fuel ! ;
\ The importer's outcome, and no manifest enforced; internal: only
\ rr-import and rr-read-once below load the input (rvRP3 R2-3).
get-current rr-internal set-current
: rr-read! ( outcome -- ) run-record rr-read ! false run-record rr-enforced ! ;
set-current
\ rr-import loads the run's file itself with checker-input.fs, with the
\ manifest checked (cin-read-checked) when flag is true; the record says
\ enforced exactly then. What every recorded read guarantees: both of the
\ importer's passes read bytes with one SHA-256 (checker-input.fs compares
\ the second pass's digest with the first's, rvRP3 R2-1), and that
\ SHA-256 is the one rr-start recorded (rr-matches, else the read is
\ invalid and rr-moved? true). So the verdicts of every record are those
\ of bytes whose SHA-256 is input.sha256, whatever happened to the file
\ between the reads, or back again before rr-finish. Enforced adds only
\ that each pass also matched the manifest beside the file as it stood
\ for that pass.
: rr-bytes-check ( -- outcome ) cin-digest rr-matches ;
: rr-moved? ( -- flag ) run-record rr-moved @ ;
\ The export file c-addr u into the checker's input, its manifest checked
\ when flag is true.
: rr-read-file ( c-addr u flag -- outcome ) if cin-read-checked else cin-read then ;
: rr-load ( flag -- outcome )
  rr-file rot rr-read-file dup ok? if drop rr-bytes-check then ;
\ A run that is not recorded (bin/leanforth check without --record): the
\ export file c-addr u loaded by the importer alone (its two passes, the
\ manifest checked when flag is true, both passes' digests equal), with
\ none of rr-start's three reads (digest, metadata, manifest) and no name
\ kept, so rr-write then refuses (invalid).
: rr-read-once ( c-addr u flag -- outcome )
  rr-release rr-reset rr-read-file dup rr-read! ;
: rr-unstarted ( flag -- outcome ) drop outcome-invalid dup rr-read! ;
: rr-import ( flag -- outcome )
  false run-record rr-moved ! rr-started? 0= if rr-unstarted exit then
  dup rr-load dup rr-read! swap 0<> run-record rr-enforced ! ;
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
\ A snapshot of every slot of the run's own environment.
: rr-viewed? ( -- flag )
  rr-ours? if lf-env-view ok? lf-name-storage-valid? and else false then ;
: rr-final? ( d -- flag ) lf-env-readable dup if nip then ;
: rr-all-final? ( -- flag ) true lf-input-count 0 ?do i rr-final? and loop ;
: rr-confirm ( -- outcome )
  rr-viewed? if rr-all-final? flag>outcome else outcome-invalid then ;
: rr-own! ( env -- )
  dup run-record rr-env ! lf-envh-identity @ run-record rr-env-id !
  true run-record rr-own ! ;
\ A record keeps at most lf-input-default declarations: more is full,
\ once the environment is in use (a refused use gives its own outcome).
: rr-run-in ( env -- outcome )
  dup rr-own! lf-env-use dup ok? 0= if exit then drop
  lf-input-count lf-input-default > if outcome-full exit then
  lf-input-count rr-steps rr-confirm ;
\ A new run: an earlier run's environment freed, no step taken, and every
\ kept outcome invalid until its step publishes one, never ok (0).
: rr-unkept ( -- )
  run-record rr-kept lf-input-default /rr-step * erase
  lf-input-default 0 do outcome-invalid i rr-step-of kept-outcome ! loop ;
: rr-begun ( -- )
  rr-release rr-unkept true run-record rr-checked ! 0 run-record rr-stepped !
  false run-record rr-own ! ;
: rr-check ( -- )
  rr-begun run-record rr-fuel @ lf-check-budget run-record rr-deps @ lf-env-new
  dup ok? if drop rr-run-in else nip then run-record rr-run ! ;

\ The end of a run: the file read again, unchanged.
: rr-same-input? ( -- flag )
  run-record dup rr-before /rr-facts rot rr-after /rr-facts compare 0= ;
: rr-finish ( -- outcome )
  rr-file run-record rr-after rr-hash dup ok? if drop rr-same-input? flag>outcome then ;

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
  2dup tr-rule? 0= if outcome-invalid rr-fail then rr-w jw-string ;
: rr-shown ( c-addr u room -- )
  over < if outcome-full rr-fail then
  2dup tr-shown? 0= if outcome-invalid rr-fail then rr-string ;
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
: rr-read-ok? ( -- flag ) run-record rr-read @ ok? ;
: rr-manifest-ok? ( -- flag ) run-record rr-manifest-outcome @ ok? ;
: rr-why-out ( -- )
  run-record rr-manifest-reason rr-manifest-ok?
  if s" reason" rr-member else s" reason" rr-shown-out then ;
\ Whether the importer enforced the manifest. An enforced manifest that
\ the input read past although it does not match is a contradiction: the
\ text fails as invalid.
: rr-enforced? ( -- flag ) run-record rr-enforced @ ;
: rr-enforced-past? ( -- flag ) rr-enforced? rr-read-ok? and rr-manifest-ok? 0= and ;
: rr-enforced-out ( -- )
  rr-enforced-past? if outcome-invalid rr-fail then
  s" enforced" rr-key rr-enforced? rr-w jw-bool ;
: rr-manifest-out ( -- )
  s" manifest" rr-key rr-object
  s" outcome" rr-key run-record rr-manifest-outcome @ rr-outcome
  run-record rr-manifest-key s" field" rr-member rr-why-out rr-enforced-out
  rr-end-object ;
\ A run that did not start with rr-start (rr-read-once) has no facts of
\ its file to record: the text fails as invalid.
: rr-input-out ( -- )
  rr-started? 0= if outcome-invalid rr-fail then
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
\ Since plan task 6.2.0 universe parameters and arguments have no fixed
\ limit; parameters and referenceLevels are not limits since plan task
\ 6.2.0 and record 64, the old limits, a legacy value the 0.1 schema
\ requires, until the record's next version (RUN_RECORDS.md, item 3).
: rr-limits ( -- )
  lf-env-dep-capacity s" dependenciesPerCheck" rr-setting
  lf-param-capacity s" parameters" rr-setting
  lf-cref-argument-capacity s" referenceLevels" rr-setting ;
: rr-settings-out ( -- )
  s" settings" rr-key rr-object run-record rr-fuel @ s" fuel" rr-setting
  run-record rr-deps @ s" dependencyPool" rr-setting rr-stores rr-limits rr-end-object ;

\ The run: the importer's outcome, the run's (not-run without rr-check),
\ and the environment's run mode and allowlist version (null without one).
: rr-made ( -- env|0 ) rr-ours? if run-record rr-env @ else 0 then ;
\ Checks that ran although the read was not ok checked another input, the
\ one an earlier read left: the text fails as invalid (rvRP3 L1).
: rr-run-out ( -- )
  run-record rr-checked @ 0= if s" not-run" rr-string exit then
  rr-read-ok? 0= if outcome-invalid rr-fail then run-record rr-run @ rr-outcome ;
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
\ The reason (the catalogue's name of the code) and the site go through the
\ same rule and limits as every other text: shown, at most 128 and 255
\ bytes; an empty site (a diagnostic recorded without one) stays empty.
: rr-code-out ( step -- step )
  s" code" rr-key dup kept-code @ dup rr-int
  s" reason" rr-key lf-diag-name rr-note-room rr-shown ;
: rr-site-out ( step -- step )
  s" site" rr-key dup kept-site @ rr-site
  dup if rr-site-room rr-shown else rr-string then ;
: rr-reason-out ( step -- )
  rr-object rr-code-out rr-site-out
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
\ is freed or another one is current, the text fails as invalid; when the
\ input holds more declarations than a record keeps (lf-input-default; the
\ schema's limit), as full (rvRP3 R2-2).
: rr-made-own? ( -- flag ) run-record dup rr-checked @ swap rr-own @ and ;
: rr-fits? ( -- flag ) lf-input-count lf-input-default upto? ;
: rr-decls ( -- )
  rr-made-own? 0= if exit then rr-fits? 0= if outcome-full rr-fail exit then
  rr-viewed? 0= if outcome-invalid rr-fail exit then
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

order-   \ rr-internal off the search order
base !   \ the BASE this file was loaded with

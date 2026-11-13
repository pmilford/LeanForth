\ The JSON report of `leanforth check --json` (plan tasks 3.4.3 and, the
\ command line's part, 6.5.2): one JSON text in the format
\ leanforth-check-report, version 0.4 (schemas/check-report-0.4.schema.json;
\ docs/user/COMMAND_LINE.md, "JSON output") for a final run, or 0.5
\ (schemas/check-report-0.5.schema.json; plan step SN3) for a run of a
\ loaded snapshot (check --snapshot): 0.4's members, the export null, and
\ "mode" development, a "snapshot" member (the file, its identity, its
\ versions, the export it was written from, the information of the build
\ that wrote it) and on each declaration its "provenance" (checked,
\ snapshot or uses-snapshot; ADR 0020 D4, OQ-3). Then a line feed, written to
\ standard output with the project's JSON writer after a run of
\ cli/check-run.fs and before ck-release. Every verdict is read from the
\ slots of the run's own environment (ck-verdicts?), never from what the
\ run kept, which gives only each check's diagnostic, step and fuel; the
\ counts and the exit status are cli/tally.fs's, which the command line
\ fills before it writes the report. Every member but "measured" is
\ deterministic: the same for every run of the same export with the same
\ options and build, on either engine; "measured" holds the times, the
\ memory and the engine.
\ LeanForth-specific and untrusted: a report, never a source of verdicts.
\
\ cj-report ( c-addr u checked? -- outcome ) writes the report of the run
\ of the export file named c-addr u, its manifest checked when checked? is
\ true: ok, or the writer's failure (invalid for a text it refuses, full
\ when a name finds no heap), after which standard output holds a text
\ cut short, never a whole report. Names, and the export's file name, are
\ written as cli/name-text.fs shows them (Lean's Name.toString, with
\ escapes), so the report holds the same text as the text output.
\ State: one shared record, the writer cj-writer.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/json-write.fs
require ../core/diagnostics.fs
require ../core/input.fs
require ../kernel/environment.fs
require ../kernel/check-declaration.fs
require ../import/manifest.fs
require ../import/stage.fs
require ../import/feed.fs
require ../import/run-record.fs
require ./tally.fs
require ./name-text.fs
require ./check-run.fs

8 0 json-writer: cj-writer
: cj-schema ( -- c-addr u ) s" leanforth-check-report" ;
: cj-version ( -- c-addr u ) ck-snapped? if s" 0.5" else s" 0.4" then ;

\ Writing values and members.
: cj-key ( c-addr u -- ) cj-writer jw-key ;
: cj-string ( c-addr u -- ) cj-writer jw-string ;
: cj-n ( n -- ) cj-writer jw-n ;
: cj-ud ( ud -- ) decimal-text cj-writer jw-digits ;
: cj-null ( -- ) cj-writer jw-null ;
: cj-object ( -- ) cj-writer jw-open-object ;
: cj-end-object ( -- ) cj-writer jw-close-object ;
: cj-array ( -- ) cj-writer jw-open-array ;
: cj-end-array ( -- ) cj-writer jw-close-array ;
: cj-text ( c-addr u key-addr key-u -- ) cj-key cj-string ;
: cj-number ( n key-addr key-u -- ) cj-key cj-n ;
: cj-flag ( flag key-addr key-u -- ) cj-key cj-writer jw-bool ;
: cj-null-member ( key-addr key-u -- ) cj-key cj-null ;

\ A text as cli/name-text.fs shows it; one the heap cannot hold fails the
\ report as full.
: cj-shown ( c-addr u flag -- c-addr u ) 0= if outcome-full cj-writer jw-fail then ;
: cj-name-text ( d -- c-addr u ) lf-input-name nt-name cj-shown ;

\ ---- The read: its outcome, and for a failure where it failed.
: cj-nowhere ( -- )
  s" line" cj-null-member s" field" cj-null-member ;
: cj-ok-read ( -- )
  s" phase" cj-null-member cj-nowhere s" reason" cj-null-member s" at" cj-null-member ;
: cj-unopened ( -- )
  s" open" s" phase" cj-text cj-nowhere s" cannot open the export" s" reason" cj-text
  s" at" cj-null-member ;
: cj-staging ( -- )
  s" stage" s" phase" cj-text ck-stage stage-error 2>r 2>r s" line" cj-number
  2r> s" field" cj-text 2r> s" reason" cj-text s" at" cj-null-member ;
: cj-feeding ( -- )
  s" feed" s" phase" cj-text cj-nowhere
  s" the staged export could not be fed to the checker" s" reason" cj-text
  ck-feeding-record feed-at s" at" cj-number ;
\ A snapshot refused (0.3): what was refused, and the record.
: cj-snap-refused ( -- )
  s" snapshot" s" phase" cj-text cj-nowhere ck-snap snap-error >r
  s" reason" cj-text r> dup 0< if drop s" at" cj-null-member else s" at" cj-number then ;
: cj-staged ( -- ) ck-snap-bad? if cj-snap-refused else cj-staging then ;
: cj-where ( -- )
  ck-phase-failed case ck-staging of cj-staged endof ck-feeding of cj-feeding endof
    ck-opening of cj-unopened endof cj-ok-read endcase ;
: cj-read ( -- )
  s" read" cj-key cj-object ck-read-outcome outcome-text s" outcome" cj-text cj-where
  cj-end-object ;
\ The export's metadata, only when it names another exporter or Lean
\ version (read with --any-lean-version), in the shape of the export's
\ own meta record, each text as display text.
: cj-meta ( k key-addr key-u -- )
  rot ck-stage stage-meta-text nt-text cj-shown 2swap cj-text ;
: cj-exporter ( -- )
  s" exporter" cj-key cj-object 0 s" name" cj-meta 1 s" version" cj-meta cj-end-object ;
: cj-lean ( -- )
  s" lean" cj-key cj-object 4 s" githash" cj-meta 3 s" version" cj-meta cj-end-object ;
: cj-other ( -- )
  ck-other-lean? 0= if exit then s" exportMeta" cj-key cj-object cj-exporter
  s" format" cj-key cj-object 2 s" version" cj-meta cj-end-object cj-lean cj-end-object ;

\ ---- The run and its declarations, in input order.
: cj-run ( -- )
  ck-loaded? if ck-outcome outcome-text else s" not-run" then s" run" cj-text ;
\ Whether the run stopped on an internal fault (a check threw, or
\ publishing failed), as the text's line "the run stopped" says.
: cj-stopped ( -- ) ck-stopped? s" stopped" cj-flag ;
: cj-began? ( d -- flag ) ck-steps-begun < ;
\ The verdict as a run record writes it: accepted for ok, skipped for a
\ declaration Lean's replay skips (cli/tally.fs verdict-of).
: cj-verdict-text ( d -- c-addr u )
  dup cj-began? if verdict-of else drop not-checked then verdict-name ;
: cj-site ( site -- c-addr u ) ?dup if count else s" " then ;
: cj-numbers ( step -- )
  s" numbers" cj-key cj-array dup kept-first @ cj-n kept-second @ cj-n cj-end-array ;
: cj-reason ( step -- )
  cj-object dup kept-code @ dup s" code" cj-number lf-diag-name s" reason" cj-text
  dup kept-site @ cj-site s" site" cj-text dup cj-numbers kept-step @ s" step" cj-number
  cj-end-object ;
: cj-diagnostic ( d -- )
  s" diagnostic" cj-key ck-kept dup kept-code @ lf-diag-none =
  if drop cj-null else cj-reason then ;
\ The axiom set's bits; NOT PROVED when one does not count as proved, with
\ the axioms outside the allowlist that make it so (notProvedBy).
: cj-unlisted ( d -- ) dup lf-env-unlisted? if cj-name-text cj-string else drop then ;
: cj-not-proved-by ( d -- )
  s" notProvedBy" cj-key cj-array ['] cj-unlisted lf-env-axiom-deps drop cj-end-array ;
: cj-axioms ( d -- )
  dup lf-env-axioms drop dup s" axiomBits" cj-number
  lf-env-unproved 0<> dup s" notProved" cj-flag if cj-not-proved-by else drop then ;
\ What follows the verdict: the axioms of an accepted one, the diagnostic
\ of any other that began.
: cj-detail ( d -- )
  dup cj-began? 0= if drop exit then
  dup lf-env-outcome ok? if cj-axioms else cj-diagnostic then ;
\ A check's fuel used, null when it is not known (cli/check-run.fs).
: cj-fuel-used ( d -- ) s" fuel" cj-key ck-fuel-of dup 0< if drop cj-null else cj-n then ;
\ Where its verdict comes from (0.3): checked, snapshot, uses-snapshot.
\ With a stale snapshot (--snapshot-stale-ok): stale-snapshot,
\ uses-stale-snapshot.
: cj-stale-text ( origin -- c-addr u )
  lf-origin-saved = if s" stale-snapshot" else s" uses-stale-snapshot" then ;
: cj-origin-text ( origin -- c-addr u )
  dup lf-origin-checked <> ck-stale? and if cj-stale-text exit then
  case lf-origin-saved of s" snapshot" endof lf-origin-uses of s" uses-snapshot" endof
    s" checked" rot endcase ;
\ A result carried from a snapshot of an older verdict version (plan step
\ 6.2.5c3) is the snapshot's, never stale.
: cj-from ( d -- c-addr u )
  dup ck-carried? if drop s" snapshot" else lf-env-origin cj-origin-text then ;
: cj-provenance ( d -- )
  ck-snapped? if cj-from s" provenance" cj-text else drop then ;
: cj-decl ( d -- )
  cj-object dup s" index" cj-number dup cj-name-text s" name" cj-text
  dup cj-verdict-text s" verdict" cj-text dup cj-detail dup cj-provenance cj-fuel-used
  cj-end-object ;
: cj-decls ( -- )
  s" declarations" cj-key cj-array
  ck-verdicts? if lf-input-count 0 ?do i cj-decl loop then cj-end-array ;

\ ---- The counts (cli/tally.fs, in its verdict order), null when no
\ verdict could be read.
: cj-count-key ( verdict -- c-addr u )
  dup not-checked = if drop s" notChecked" else verdict-name then ;
: cj-count ( verdict -- ) dup cj-count-key cj-key cli-count-of @ cj-n ;
: cj-tallies ( -- ) verdict-kinds 0 do i verdict-kind cj-count loop ;
: cj-counts ( -- )
  s" counts" cj-key ck-verdicts? 0= if cj-null exit then
  cj-object lf-input-count s" declarations" cj-number cj-tallies
  cli-not-proved @ s" notProved" cj-number cj-end-object ;

\ ---- Fuel: per check, in all, and the declarations that used the most.
: cj-top ( k -- )
  ck-top@ cj-object dup s" index" cj-number dup cj-name-text s" name" cj-text
  dup ck-fuel-of s" fuel" cj-number cj-verdict-text s" verdict" cj-text cj-end-object ;
: cj-tops ( -- ) s" top" cj-key cj-array ck-tops 0 ?do i cj-top loop cj-end-array ;
: cj-no-tops ( -- ) s" top" cj-key cj-array cj-end-array ;
: cj-fuel ( -- )
  s" fuel" cj-key cj-object ck-fuel-budget s" perDeclaration" cj-number
  s" total" cj-key ck-fuel-total cj-ud ck-fuel-unknowns s" unknown" cj-number
  ck-verdicts? if cj-tops else cj-no-tops then cj-end-object ;

\ ---- The input as fed: declarations, term nodes, levels, constant
\ references and names; null when it was not fed.
: cj-input ( -- )
  s" input" cj-key ck-loaded? 0= if cj-null exit then
  cj-object ck-input-declarations s" declarations" cj-number
  ck-input-terms s" terms" cj-number ck-input-levels s" levels" cj-number
  ck-input-references s" references" cj-number ck-staged-names s" names" cj-number
  cj-end-object ;

\ ---- Measured: each phase's times in microseconds, the run's total so
\ far the last (null on a host without clocks), the peak resident memory
\ in bytes (null where the host does not say) and the stage's heap bytes
\ (null when nothing was staged); then the engine (null when not known).
: cj-phase ( k -- )
  dup ck-phase-name cj-key cj-object dup ck-phase-wall s" wall" cj-key cj-ud
  ck-phase-cpu s" cpu" cj-key cj-ud cj-end-object ;
: cj-times ( -- )
  s" microseconds" cj-key ck-timed? 0= if cj-null exit then
  ck-finish cj-object ck-phases 0 do i cj-phase loop cj-end-object ;
: cj-peak ( -- ) s" peakResidentBytes" cj-key ck-peak if cj-n else cj-null then ;
: cj-stage-bytes ( -- )
  s" stageBytes" cj-key ck-staged? if ck-staged-bytes cj-n else cj-null then ;
\ The engine bin/leanforth ran (gforth, or gforth-fast with --fast), as
\ display text; null when not known.
: cj-engine ( -- )
  s" engine" cj-key ck-engine dup if nt-text cj-shown cj-string else 2drop cj-null then ;
: cj-measured ( -- )
  s" measured" cj-key cj-object cj-times cj-peak cj-stage-bytes cj-engine cj-end-object ;

\ ---- The snapshot of a 0.3 report: the file, its identity (its header's
\ SHA-256), its format and verdict versions, the export it was written
\ from, the manifest's SHA-256 (null without one), the base (null: a base
\ snapshot) and the information text of the build that wrote it.
create cj-hex 64 allot
: cj-sha ( c-addr key-addr key-u -- ) rot cj-hex sha256-hex cj-hex 64 2swap cj-text ;
: cj-snap-export ( -- )
  s" export" cj-key cj-object ck-snap snap-export-sha s" sha256" cj-sha
  ck-snap snap-export-bytes s" bytes" cj-number ck-snap snap-export-lines s" lines"
  cj-number
  ck-snap snap-flags dup snap-enforced and 0<> s" manifestChecked" cj-flag
  snap-any-lean and 0<> s" anyLeanVersion" cj-flag cj-end-object ;
: cj-snap-manifest ( -- )
  ck-snap snap-flags snap-enforced and
  if ck-snap snap-manifest-sha s" manifestSha256" cj-sha
  else s" manifestSha256" cj-null-member then ;
: cj-snap-file ( -- ) ck-snap-file@ nt-text cj-shown s" file" cj-text ;
: cj-snap-info ( -- ) ck-snap snap-info nt-text cj-shown s" information" cj-text ;
\ With an export checked against the snapshot (plan step SN4): how many
\ declarations were taken from it and checked in this run, and how many
\ share a name with one of it but none's content; null without one.
: cj-import ( -- )
  ck-importing? ck-snap-bad? 0= and 0= if s" import" cj-null-member exit then
  s" import" cj-key cj-object ck-taken# s" taken" cj-number
  ck-checked# s" checked" cj-number ck-other# s" otherContent" cj-number
  cj-end-object ;
\ Each layer loaded on the base (review rvSN4 M1): its file, identity,
\ export and base (the snapshot's own identity).
: cj-layer ( k -- )
  cj-object dup ck-layer@ nt-text cj-shown s" file" cj-text
  dup ck-layer-id dup ck-lid-sum s" sha256" cj-sha ck-lid-export s" exportSha256" cj-sha
  ck-snap snap-sum s" base" cj-sha ck-layer-verdict s" verdictVersion" cj-number
  cj-end-object ;
: cj-layers ( -- )
  s" layers" cj-key cj-array ck-layers# 0 ?do i cj-layer loop cj-end-array ;
\ A stale snapshot loaded (--snapshot-stale-ok; ADR 0020 amendment 3):
\ this build's verdict version and how many results are stale; else null.
: cj-stale ( -- )
  ck-stale? 0= if s" stale" cj-null-member exit then
  s" stale" cj-key cj-object lf-verdict-version s" thisVerdictVersion" cj-number
  ck-stale# s" results" cj-number cj-end-object ;
: cj-snapshot ( -- )
  ck-snapped? 0= if exit then s" development" s" mode" cj-text
  ck-snap snap-id 0= if s" snapshot" cj-null-member exit then
  s" snapshot" cj-key cj-object cj-snap-file
  ck-snap snap-sum s" sha256" cj-sha snap-version s" formatVersion" cj-number
  ck-snap snap-verdict s" verdictVersion" cj-number cj-stale cj-snap-export
  cj-snap-manifest
  s" base" cj-null-member cj-layers cj-snap-info cj-import cj-end-object ;
\ ---- The report.
: cj-export ( c-addr u -- )
  ck-snap-only? if 2drop s" export" cj-null-member exit then nt-text cj-shown s" export"
  cj-text ;
: cj-head ( c-addr u checked? -- )
  cj-schema s" schema" cj-text cj-version s" schemaVersion" cj-text >r cj-export
  r> if s" checked" else s" not-checked" then s" manifest" cj-text cj-snapshot ;
\ anyLeanVersion only with --any-lean-version, so that a report without it
\ is as before.
: cj-any-lean ( -- ) ck-any-version? if true s" anyLeanVersion" cj-flag then ;
\ memoryPerCheck, in megabytes of 2^20 bytes, only with --memory-per-check
\ (core/scratch-meter.fs).
: cj-per-check ( -- )
  lf-meter-limit@ ?dup if 20 rshift s" memoryPerCheck" cj-number then ;
: cj-settings ( -- )
  s" settings" cj-key cj-object ck-fuel-budget s" fuel" cj-number
  lf-env-pool-start s" dependencyPool" cj-number
  cli-strict-axioms? s" strictAxioms" cj-flag cj-any-lean cj-per-check cj-end-object ;
: cj-status ( -- ) cli-worst @ s" exitStatus" cj-number ;
: cj-body ( c-addr u checked? -- )
  cj-object cj-head cj-settings cj-read cj-other cj-run cj-stopped cj-decls cj-counts
  cj-fuel cj-input cj-status cj-measured cj-end-object ;
: cj-report ( c-addr u checked? -- outcome )
  ['] type cj-writer jw-start cj-body cj-writer jw-end dup ok? if cr then ;

base !   \ the BASE this file was loaded with

\ The command line (plan tasks 3.4.1-3.4.3, v0): the Forth entry point that
\ bin/leanforth runs as `gforth src/main.fs -e cli-main COMMAND ...`.
\ Commands, documented in docs/user/COMMAND_LINE.md:
\   check [--no-manifest] [--fuel N] [--resources] [--json] EXPORT
\       stage the Lean export with the importer stage (its manifest
\       checked unless --no-manifest says not to) and feed it to the
\       checker, whose stores grow to fit (cli/check-run.fs: any size, all
\       of Lean's Init), check every declaration in file order with
\       check-declaration through the checked environment's publisher,
\       and print one line per declaration with its verdict, read from
\       its published slot; then a summary with the accepted ones' label
\       and axioms; with --resources also the resource report (time and
\       CPU of each phase, peak memory, the input's size, fuel in all and
\       the ten declarations that used the most); with --json all of it
\       as one JSON text instead (cli/check-json.fs);
\   check [--no-manifest] [--fuel N] --record RECORD EXPORT
\       the check of small exports that writes a run record (plan 2.2.5):
\       the export read into the checker's input at its default sizes
\       (import/checker-input.fs, which refuses inductive types), checked
\       by import/run-record.fs's run (rr-check), and printed as above;
\       run records 0.1 hold at most 32 declarations, so --record keeps
\       this path (docs/programming/RUN_RECORDS.md, "Version 0.2");
\   replay [--no-manifest] [--fuel N] EXPORT RECORD
\       check the export again and compare the new run record with RECORD
\       (import/run-replay.fs): the replay report, exit 0 confirmed, 1
\       refused (a difference), 4 when it cannot be compared;
\   print [--no-manifest] [--fuel N] [--detail] [--name NAME] EXPORT
\       check the export as check --record does, one declaration at a time
\       with the derivation log on, and print each one's proof outline
\       right after its check (cli/print.fs, present/proof-outline.fs), or
\       with --detail every step of its log; with --name only that one;
\   count [--no-manifest] EXPORT          the record counts (ndjson-count.fs);
\   reexport [--no-manifest] EXPORT COPY  the byte-exact copy (ndjson-emit.fs);
\   version, capabilities, help (also --version, --help and -h).
\ Exit codes (cli/tally.fs): 0 all accepted (or the command done), 1
\ something rejected, 2 unsupported or unknown, 3 a resource limit (out of
\ fuel or room), 4 malformed input (also a malformed command line, or a
\ file that cannot be opened or created), 5 an internal fault (a Forth
\ exception, a check that threw, a publisher fault), 6 all accepted but
\ some NOT PROVED (proposed; owner's confirmation pending). When codes
\ differ, the most severe wins, in the order 5, 4, 1, 3, 2, 6, 0. cli-main
\ leaves the host with status 100 + code, so that bin/leanforth tells
\ LeanForth's codes from the host's own failures (Gforth ends with 0 or 1
\ after an uncaught error), and maps any other status to 5.
\
\ Trust boundary: "accepted" is printed only by lf-check-verdict.
\ (kernel/check-declaration.fs) from a declaration's published slot, and
\ the exit code comes from the slots' outcomes as lf-env-outcome reads
\ them; staging, parsing and printing here can hand the checker a wrong
\ claim or misreport a failure, never make a declaration accepted. Names
\ are printed as cli/name-text.fs shows them, escaped, so a crafted name
\ cannot forge a line. An accepted declaration whose axiom set is not
\ empty is marked NOT PROVED (the owner's rule; the first checker accepts
\ no axiom, so none is yet). check --record, replay and print hold small
\ exports only (64 names, levels and term nodes, 32 declarations):
\ anything larger ends full, exit 3, and the output says so. Untrusted,
\ like everything in src/ until the review gate.
\
\ The Forth interface, for a Forth session or a test, each ( -- code )
\ after its arguments, printing what the command prints: cli-check
\ ( c-addr u ), cli-replay ( export-addr export-u record-addr record-u ),
\ cli-print ( c-addr u ), cli-count ( c-addr u ), cli-reexport ( in-addr
\ in-u out-addr out-u ), cli-version, cli-capabilities, cli-help. They use
\ the options in force: cli-options restores the defaults (manifest
\ checked, fuel cli-default-fuel, no record, text without the resource
\ report), cli-no-manifest, cli-fuel!, cli-record!, cli-resources and
\ cli-json change them. A THROW inside a command is caught and reported:
\ code 5. A check that threw spends its context (ADR 0012, G-P6): every
\ later check in that context ends invalid, with diagnostic 29, so a
\ session runs the next command in a new context (context-new).
\
\ Host words: next-arg (Gforth 0.7.3 and 1.0) reads the command line,
\ where a host without it reads none; (bye) leaves with a status, where a
\ host without it ends with an uncaught THROW, which the wrapper reports
\ as an internal fault; version-string names the host when it exists;
\ getenv reads the commit bin/leanforth found for the run record
\ (LEANFORTH_COMMIT, LEANFORTH_MODIFIED), where a host without it records
\ none.
\ State: one record in the checker context, cli-state (the options, the
\ command line's file names and first mistake, and which run a check
\ made), set up with the defaults in every context; cli/tally.fs's record
\ (the exit code so far and the declarations counted by verdict); and
\ one manifest record, cli-manifest, for re-exports, shared because it
\ owns heap buffers. A check's run is in cli/check-run.fs's shared
\ globals, or with --record in run-record.fs's. One command runs at a
\ time.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/bytes.fs
require ../core/diagnostics.fs
require ../core/input.fs
require ../kernel/environment.fs
require ../kernel/env-publish.fs
require ../kernel/check-declaration.fs
require ../import/ndjson.fs
require ../import/manifest.fs
require ../import/checker-input.fs
require ../import/run-record.fs
require ../import/run-replay.fs
require ../import/ndjson-count.fs
require ../import/ndjson-emit.fs
require ./print.fs
require ./tally.fs
require ./name-text.fs
require ./check-run.fs
require ./check-json.fs

100000 constant cli-default-fuel   \ fuel of each declaration's check
\ The most fuel --fuel takes: 2^53 - 1, the largest integer every JSON
\ reader holds exactly (I-JSON), so that reports and records hold it; on
\ a host whose cells are smaller, the largest cell.
: cli-fuel-limit ( -- n ) max-n 53 rshift if 1 53 lshift 1- else max-n then ;
cli-fuel-limit constant cli-fuel-most
begin-structure /cli-run
  field: opt-unchecked          \ true: manifests are not checked (--no-manifest)
  field: opt-fuel               \ fuel each declaration's check starts with (--fuel)
  2 cells +field opt-record     \ the run record's file name (--record), or 0 0
  field: opt-detail             \ true: print every step of the log (--detail)
  2 cells +field opt-name       \ the declaration to print (--name), or 0 0
  field: opt-resources          \ true: print the resource report (--resources)
  field: opt-json               \ true: the report as JSON (--json)
  4 cells +field arg-files      \ the file names given, in order (two c-addr u)
  field: arg-count              \ how many were given
  field: arg-set                \ the options the command takes, as bits
  2 cells +field arg-culprit    \ the argument of the first mistake, or 0 0
  field: arg-mistake            \ counted string: the first mistake, or 0
  field: run-ops                \ the run the last check made: its words (/cli-ops)
end-structure
/cli-run context-record: cli-state
manifest: cli-manifest

: cli-unchecked ( -- addr ) cli-state opt-unchecked ;
: cli-fuel ( -- addr ) cli-state opt-fuel ;
: cli-record ( -- addr ) cli-state opt-record ;
: cli-file ( k -- c-addr u ) 2* cells cli-state arg-files + 2@ ;
: cli-files ( -- addr ) cli-state arg-count ;

\ Options. cli-options also forgets the file names and any mistake.
: cli-options ( -- ) cli-state /cli-run erase cli-default-fuel cli-fuel ! ;
' cli-options context-setup
: cli-no-manifest ( -- ) true cli-unchecked ! ;
: cli-fuel! ( n -- ) cli-fuel ! ;
\ Write the run record of every later check to the file named c-addr u,
\ which must stay unchanged meanwhile.
: cli-record! ( c-addr u -- ) cli-record 2! ;
: cli-record? ( -- flag ) cli-record @ 0<> ;
\ check's report: with the resource report (--resources), as JSON (--json).
: cli-resources ( -- ) true cli-state opt-resources ! ;
: cli-json ( -- ) true cli-state opt-json ! ;
: cli-resources? ( -- flag ) cli-state opt-resources @ ;
: cli-json? ( -- flag ) cli-state opt-json @ ;
: cli-checked? ( -- flag ) cli-unchecked @ 0= ;

\ Numbers in decimal, whatever BASE is: xt runs with BASE decimal.
: in-decimal ( i*x xt -- j*x ) base @ >r decimal execute r> base ! ;
: do-decimal ( n -- ) 0 .r ;
: .decimal ( n -- ) ['] do-decimal in-decimal ;
: do-number-text ( n -- c-addr u ) 0 <# #s #> ;
: cli-number-text ( n -- c-addr u ) ['] do-number-text in-decimal ;
\ An internal fault: one line, and code 5.
: cli-fault ( c-addr -- ) ." internal fault: " count type cr exit-fault cli-code! ;
: cli-note ( c-addr -- ) ." note: " count type cr ;
\ A declaration's name as cli/name-text.fs shows it; one the heap cannot
\ hold is not shown, and is an internal fault.
: cli-unshown ( c-addr u -- ) 2drop ." [a name with no room to show]" exit-fault cli-code! ;
: cli-name. ( d -- ) lf-input-name nt-name if type else cli-unshown then ;

\ ---------------------------------------------------------------------------
\ check. Two runs, each checking every declaration in input order, each
\ with lf-env-step and its diagnostic kept, and stopping after a THROW in
\ a check (the context spent) or a fault of the publisher, which is an
\ internal fault: cli/check-run.fs's (the importer stage and the feed, any
\ size, every check's fuel kept), and with --record run-record.fs's
\ rr-check (small exports, written to a run record 0.1). The verdicts are
\ read after the run, each from its published slot, with the diagnostic
\ its check left: first counted (cli/tally.fs), then printed. The run
\ made is a table of its words (/cli-ops), chosen when the check starts.
\ Dependencies the --record run's environment holds, as make run-record's.
64 constant cli-pool
begin-structure /cli-ops
  field: ops-stepped      \ ( -- n ) declarations whose check began
  field: ops-outcome      \ ( -- outcome ) the run's outcome
  field: ops-ours?        \ ( -- flag ) the run's environment is current
  field: ops-kept         \ ( d -- step ) what d's check left: a /rr-step
  field: ops-stopped?     \ ( -- flag ) the run stopped on a fault
  field: ops-no-env.      \ ( -- ) why no environment could be made or used
  field: ops-room.        \ ( -- ) the note behind full
end-structure
: cli-ops ( -- ops ) cli-state run-ops @ ;
: cli-stepped ( -- n ) cli-ops ops-stepped @ execute ;
: cli-run-outcome ( -- outcome ) cli-ops ops-outcome @ execute ;
: cli-kept ( d -- step ) cli-ops ops-kept @ execute ;
\ Whether the run stopped on a fault: a THROW spends the context, a
\ publisher's fault leaves a slot open.
: cli-faulted? ( -- flag ) cli-ops ops-stopped? @ execute ;
\ Verdicts only from the run's own environment, by identity.
: cli-made? ( -- flag ) cli-ops ops-ours? @ execute lf-env-view ok? and ;
\ A declaration's axiom set: 0 when it is not accepted.
: cli-bits ( d -- bits ) lf-env-axioms drop ;
\ No room is a resource limit; anything else is a fault.
: full-or-fault ( outcome -- code ) outcome-full = if exit-limit else exit-fault then ;

\ Counting: each declaration whose check began by the verdict its slot
\ holds (and NOT PROVED apart), the rest not checked after a fault.
: cli-tally-one ( d -- ) dup lf-env-outcome dup cli-tally swap cli-bits cli-tally-proved ;
: cli-tally-stopped ( -- )
  exit-fault cli-code! lf-input-count cli-stepped - not-checked cli-count-of +! ;
: cli-tally-verdicts ( -- )
  cli-stepped 0 ?do i cli-tally-one loop cli-faulted? if cli-tally-stopped then ;
: cli-tally-run ( -- )
  cli-made? if cli-tally-verdicts else cli-run-outcome full-or-fault cli-code! then ;

\ Printing. The diagnostic declaration d's check left, when it left one.
: cli-at. ( step -- )
  ."  at " dup kept-site @ lf-diag-site. ." : " dup kept-first @ .decimal space
  kept-second @ .decimal ;
: cli-reason. ( step -- )
  dup kept-code @ dup lf-diag-none = if 2drop exit then
  ."   " dup lf-diag-name type ." ; diagnostic " .decimal cli-at. cr ;
: cli-why. ( d -- ) cli-kept cli-reason. ;
\ An accepted declaration that depends on an axiom is NOT PROVED.
: cli-not-proved. ( d -- )
  dup lf-env-outcome swap cli-bits not-proved?
  if ." ; NOT PROVED (it depends on an axiom)" then ;
\ Declaration d's line: its name and the verdict its slot holds.
: cli-verdict ( d -- )
  dup cli-name. ." : " dup lf-check-verdict. dup cli-not-proved. cr
  dup lf-env-outcome ok? if drop else cli-why. then ;
: cli-skipped ( d -- ) cli-name. ." : not checked" cr ;
: cli-stopped ( -- )
  ." internal fault: the run stopped: a check threw, or publishing failed" cr
  lf-input-count cli-stepped ?do i cli-skipped loop ;
: cli-verdicts ( -- )
  cli-stepped 0 ?do i cli-verdict loop cli-faulted? if cli-stopped then ;

\ The summary: "N declarations: a accepted, r rejected, ...", in
\ cli/tally.fs's verdict order.
: cli-kind. ( verdict -- ) dup not-checked = if drop ." not checked" else verdict-name type then ;
: cli-item ( first? verdict -- first? )
  dup cli-count-of @ ?dup 0= if drop exit then
  rot 0= if ." , " then .decimal space cli-kind. false ;
: cli-summary ( -- )
  lf-input-count dup .decimal ."  declaration" 1 <> if ." s" then ." : "
  true verdict-kinds 0 do i verdict-kind cli-item loop drop cr ;
\ The accepted ones' label and axioms, read from their slots: none, or
\ how many are NOT PROVED.
: cli-axioms. ( -- )
  ." axioms: " cli-not-proved @ ?dup 0= if ." none" exit then
  .decimal ."  NOT PROVED (they depend on an axiom)" ;
: cli-accepted. ( -- )
  outcome-ok cli-count-of @ ?dup 0= if exit then
  ." accepted: " .decimal ."  (experimental, not independently audited); "
  cli-axioms. cr ;

\ Notes after a run: the limits behind full, the fuel behind exhausted.
\ check --record leaves the stores' capacity settings at their defaults:
\ it reads with import/checker-input.fs and keeps the run record in
\ run-record.fs's tables, both sized for those defaults; check without it
\ feeds the stores, which grow, so only the checks' own limits remain.
: cli-limits ( -- )
  ." note: check --record, replay and print hold at most " lf-name-capacity .decimal
  ."  names, " lf-level-capacity .decimal ."  levels," cr ." note: "
  lf-term-capacity .decimal ."  term nodes and " lf-input-capacity .decimal
  ."  declarations per export; check without --record holds any size" cr ;
: cli-room-note ( -- )
  ." note: a check ran out of room; its diagnostic names the limit: memory, or a"
  cr ." note: walk's 64 levels of a term or a declaration's " lf-env-dep-capacity .decimal
  ."  dependencies (plan task 6.2.0)" cr ;
: cli-fuel-note ( -- )
  ." note: a check ran out of fuel (" cli-fuel @ .decimal
  ."  steps each); --fuel N gives each more" cr ;
: cli-notes ( -- )
  outcome-full cli-count-of @ if cli-ops ops-room. @ execute then
  outcome-exhausted cli-count-of @ if cli-fuel-note then ;

\ After the run, counted: the verdicts, the summary and the notes; or why
\ there was no run, when no environment could be made or used.
: cli-no-room. ( -- ) ." error: no room for the checked environment" cr ;
: cli-no-room ( -- ) cli-no-room. exit-limit cli-code! ;
: cli-no-env. ( outcome -- )
  outcome-full = if cli-no-room. exit then
  ." internal fault: no checked environment could be made or used" cr ;
: cli-results. ( -- )
  cli-made? if cli-verdicts cli-summary cli-accepted. cli-notes
  else cli-ops ops-no-env. @ execute then ;
: cli-results ( -- ) cli-tally-run cli-results. ;

\ The two runs' words. --record: run-record.fs's run.
: rr-stepped@ ( -- n ) run-record rr-stepped @ ;
: rr-run@ ( -- outcome ) run-record rr-run @ ;
: rr-stopped? ( -- flag ) lf-env-spent? rr-run@ ok? 0= or ;
: rr-no-env. ( -- ) rr-run@ cli-no-env. ;
create cli-recorded-ops
  ' rr-stepped@ , ' rr-run@ , ' rr-ours? , ' rr-step-of , ' rr-stopped? , ' rr-no-env. ,
  ' cli-limits ,
\ The feed's run (cli/check-run.fs); its facts may have found no room
\ before the environment was made.
: ck-run-stopped? ( -- flag ) ck-stopped? ck-outcome ok? 0= or ;
: ck-no-env. ( -- )
  ck-facts-made? if ck-outcome cli-no-env. exit then
  ." error: no room for the run's facts (a record of each declaration)" cr ;
create cli-fed-ops
  ' ck-steps-begun , ' ck-outcome , ' ck-ours? , ' ck-kept , ' ck-run-stopped? ,
  ' ck-no-env. , ' cli-room-note ,
: cli-fed? ( -- flag ) cli-ops cli-fed-ops = ;

\ A read that failed: the outcome, the reason, the field and the line
\ (0 for the manifest), and for a JSON error the byte within the line.
: cli-field. ( c-addr u -- ) dup if ." field " type ." , " else 2drop then ;
: cli-byte. ( export -- )
  export-json dup json-why @ if ." , byte " json-offset .decimal else drop then ;
: cli-error-head ( outcome why-addr why-u -- )
  ." error: " rot outcome-text type ." : " type ;
: cli-where ( line key-addr key-u export -- )
  >r ."  (" cli-field. ." line " .decimal r> cli-byte. ." )" cr ;
: cli-input-error ( outcome -- )
  >r cin-error r> -rot cli-error-head cin-export cli-where ;
\ A failure about the manifest is at line 0 (the export opened, see
\ cli-opens?): a hint at the export step and the explicit way out.
: manifest-failed? ( outcome -- flag )
  outcome-invalid = cli-checked? and cin-error 2drop 2drop 0= and ;
: cli-manifest-hint ( -- )
  c" the export is checked against EXPORT.manifest.json, which scripts/export.sh writes;"
  cli-note c" --no-manifest skips that check" cli-note ;
\ A checked read whose bytes are not the ones the run hashed first.
: cli-moved ( -- )
  ." error: invalid: the export changed between its digest and its reading" cr ;
: cli-read-error ( outcome -- outcome )
  rr-moved? if cli-moved else dup cli-input-error then ;
: cli-unread ( outcome -- )
  cli-read-error dup outcome-full = if cli-limits then
  dup manifest-failed? if cli-manifest-hint then outcome>code cli-code! ;
: cli-unchecked-note ( -- )
  cli-unchecked @ 0= if exit then
  c" the export's manifest is not checked (--no-manifest)" cli-note ;
\ The export, file 0, must open, so that a wrong name is not reported as
\ a missing manifest.
: cli-opens? ( -- flag )
  0 cli-file r/o bin open-file if drop false else close-file drop true then ;
: cli-unopened ( -- code ) ." error: cannot open the export" cr exit-malformed ;
\ check --record and replay: the export (file 0) into the checker's input,
\ its manifest checked unless --no-manifest: the file rr-start kept and
\ hashed, through rr-import, which records the outcome and whether the
\ manifest was enforced.
: cli-import ( -- outcome ) cli-checked? rr-import ;
: cli-run ( -- ) cli-import dup ok? if drop rr-check cli-results else cli-unread then ;
: cli-settings ( -- ) rr-release cli-fuel @ cli-pool rr-settings! ;

\ check without --record: the run of cli/check-run.fs. A stage that
\ failed is reported as a read is, with the stage's line, field and
\ reason; one that failed on its manifest is invalid at line 0 with no
\ reason of sealing (stage-why). A feed that failed gives the number of
\ the expression or declaration where it stopped, as feed.fs keeps it.
: cli-stage-error ( outcome -- )
  >r ck-stage stage-error r> -rot cli-error-head ck-stage stage-export cli-where ;
: cli-stage-manifest? ( outcome -- flag )
  outcome-invalid = cli-checked? and ck-stage stage-error 2drop 2drop 0= and
  ck-stage stage-why @ 0= and ;
: cli-feed-error ( outcome -- )
  s" the staged export could not be fed to the checker" cli-error-head
  ."  (it stopped at expression or declaration " ck-feeding-record feed-at .decimal
  ." )" cr ;
: cli-fed-unread ( outcome -- )
  ck-phase-failed ck-staging = 0= if cli-feed-error exit then
  dup cli-stage-error cli-stage-manifest? if cli-manifest-hint then ;

\ The resource report (--resources), after the summary and notes: each
\ phase's wall and CPU time in seconds, the run's total so far the last,
\ the peak resident memory and the stage's heap blocks, the input's size,
\ and the fuel used in all and by the declarations that used the most.
\ Times and memory differ from run to run; the rest does not.
\ Text right-aligned in a column of width characters.
: cli-column ( c-addr u width -- ) over - 0 max spaces type ;
\ Milliseconds as seconds with three decimals; microseconds in a column.
: do-seconds ( ms -- c-addr u ) 0 <# # # # [char] . hold #s #> ;
: cli-seconds ( ms -- c-addr u ) ['] do-seconds in-decimal ;
: cli-second. ( d-us -- ) 1000 um/mod nip cli-seconds 9 cli-column ;
\ Phase k's row: its name, then its wall and CPU times.
: cli-row ( k -- )
  ."   " dup ck-phase-name dup >r type 8 r> - spaces
  dup ck-phase-wall cli-second. ck-phase-cpu cli-second. cr ;
: cli-times. ( -- )
  ck-timed? 0= if ."   time: not measured on this host" cr exit then
  ck-finish ."   time (s)     wall      cpu" cr ck-phases 0 do i cli-row loop ;
\ Bytes in kB (10^3 bytes) below a MB, else in MB (10^6) with one decimal.
: cli-mb. ( bytes -- ) 100000 / 10 /mod .decimal ." ." .decimal ."  MB" ;
: cli-size. ( bytes -- )
  dup 1000000 < if 1000 / .decimal ."  kB" else cli-mb. then ;
: cli-stage-bytes. ( -- )
  ck-staged? if ." ; the stage's heap blocks " ck-staged-bytes cli-size. then ;
: cli-peak. ( -- ) ck-peak if cli-size. else ." not measured on this host" then ;
: cli-memory. ( -- ) ."   memory: peak resident " cli-peak. cli-stage-bytes. cr ;
: cli-input. ( -- )
  ck-loaded? 0= if exit then
  ."   input: " ck-input-declarations .decimal ."  declarations, "
  ck-input-terms .decimal ."  term nodes, " ck-input-levels .decimal ."  levels, "
  ck-input-references .decimal ."  constant references, " ck-staged-names .decimal
  ."  names" cr ;
: cli-unknown-fuel. ( -- )
  ck-fuel-unknowns ?dup 0= if exit then
  ."   fuel not known for " .decimal ."  declarations: a failed inference gives its"
  cr ."     counter up (their checks are not in the fuel above)" cr ;
: cli-fuel. ( -- )
  ."   fuel: " ck-fuel-total decimal-text type ."  steps in all, at most "
  ck-fuel-budget .decimal ."  per declaration" cr cli-unknown-fuel. ;
: cli-fuel-column ( n -- )
  ck-fuel-budget cli-number-text nip >r cli-number-text r> cli-column ;
: cli-top. ( k -- )
  ck-top@ ."     " dup ck-fuel-of cli-fuel-column space dup cli-name. ."  ("
  lf-env-outcome verdict-name type ." )" cr ;
: cli-tops. ( -- )
  ck-tops 0= if exit then ."   most fuel used:" cr ck-tops 0 ?do i cli-top. loop ;
: cli-resources. ( -- )
  ." resources:" cr cli-times. cli-memory. cli-input. cli-fuel. cli-tops. ;

\ The report: counted first, then printed, as text or as JSON
\ (cli/check-json.fs); a JSON text the writer refuses is an internal
\ fault, after the part already written.
: cli-fed-tally ( -- )
  ck-loaded? if cli-tally-run else ck-read-outcome outcome>code cli-code! then ;
: cli-fed-text ( -- )
  ck-loaded? if cli-results. else ck-read-outcome cli-fed-unread then
  cli-resources? if cli-resources. then ;
: cli-fed-json ( -- )
  0 cli-file cli-checked? cj-report dup ok? if drop exit then
  cr ." internal fault: the JSON report could not be written: " outcome-text type cr
  exit-fault cli-code! ;
: cli-fed-report ( -- ) cli-json? if cli-fed-json else cli-fed-text then ;
: cli-library-run ( -- )
  0 cli-file cli-checked? ck-load ok? if ck-check then cli-fed-tally cli-fed-report ;
\ After the run: stores that could not be given back their sizes are an
\ internal fault (later checks in this context would hold more).
: cli-restored ( -- )
  ck-restored ok? if exit then
  c" the stores could not be given back their sizes" cli-fault ;
\ The run xt, its report, then everything it holds freed, after a THROW
\ too (passed on). The run record's state is cleared first, as no record
\ can be written from this run.
: cli-fed-run ( xt -- code )
  cli-fed-ops cli-state run-ops ! rr-release rr-reset cli-fuel @ ck-start
  catch ck-release throw cli-restored cli-worst @ ;
: cli-library ( -- code )
  cli-json? 0= if cli-unchecked-note then ['] cli-library-run cli-fed-run ;
\ An export that does not open: the JSON report says so too.
: cli-unopened-run ( -- ) ck-unopened exit-malformed cli-code! cli-fed-json ;
: cli-not-opened ( -- code )
  cli-json? if ['] cli-unopened-run cli-fed-run else cli-unopened then ;

\ The run record (--record, and replay): the commit bin/leanforth found
\ (LEANFORTH_COMMIT, with LEANFORTH_MODIFIED true when the tree differed
\ from it), or none, null in the record; rr-start reads the export before
\ the run, rr-finish after it (invalid when it changed meanwhile),
\ rr-write writes the record, rr-save the file. A record that fails is
\ reported, joins the code and is never saved.
[defined] getenv [if]
: cli-env ( c-addr u -- c-addr' u' ) getenv ;
[else]
: cli-env ( c-addr u -- c-addr' u' ) 2drop 0 0 ;
[then]
: cli-modified? ( -- flag ) s" LEANFORTH_MODIFIED" cli-env s" true" compare 0= ;
: cli-source ( -- )
  s" LEANFORTH_COMMIT" cli-env cli-modified? rr-source! ok? 0= if rr-no-source then ;
: cli-record-start ( -- outcome ) cli-source 0 cli-file rr-start ;
: cli-record-text ( -- outcome ) rr-finish dup ok? if drop rr-write then ;
: cli-record-failed ( outcome -- )
  ." error: the run record was not written: " dup outcome-text type cr outcome>code
  cli-code! ;
\ Only a check with --record starts with rr-start, which reads the export
\ for the record (its digest, metadata and manifest) and keeps its name for
\ the run's later reads (rr-import, rr-finish).
: cli-recording? ( -- flag )
  cli-record? 0= if true exit then
  cli-record-start dup ok? if drop true else cli-record-failed false then ;
: cli-saved ( -- outcome )
  cli-record-text dup ok? if drop cli-record 2@ rr-save then ;
: cli-recorded ( -- )
  cli-record? 0= if exit then cli-saved dup ok? if drop else cli-record-failed then ;
\ RECORD must not name the export: comparing the names as text; the
\ wrapper also refuses one file under two names.
: cli-over-export? ( -- flag )
  cli-record? if cli-record 2@ 0 cli-file compare 0= else false then ;
: cli-checks ( -- code )
  cli-recorded-ops cli-state run-ops ! cli-unchecked-note cli-settings
  cli-recording? if cli-run cli-recorded then rr-release cli-worst @ ;
\ --record keeps the run of small exports, whose record has no resource
\ report: --json and --resources do not go with it (a mistake, code 4).
: cli-misused? ( -- flag ) cli-record? cli-json? cli-resources? or and ;
: cli-misuse-record ( -- code )
  ." error: --json and --resources do not go with --record" cr
  ." try: leanforth help" cr exit-malformed ;
: check-command ( -- code )
  cli-start cli-misused? if cli-misuse-record exit then
  cli-opens? 0= if cli-not-opened exit then
  cli-over-export? if ." error: RECORD must not be EXPORT" cr exit-malformed exit then
  cli-record? if cli-checks else cli-library then ;

\ replay: the export, file 0, checked again as check --record checks it,
\ and the new record compared with the record in file 1; the report
\ printed. 0 confirmed, 1 refused (a difference), 4 when the old record
\ cannot be compared or the export cannot be checked again.
: cli-rerun ( -- outcome )
  cli-settings cli-record-start dup ok? 0= if exit then drop
  cli-import ok? if rr-check then cli-record-text ;
: cli-compared ( outcome -- outcome )
  ok? if 1 cli-file rp-replay else rp-rerun-refused then ;
: replay-command ( -- code )
  cli-opens? 0= if cli-unopened exit then cli-rerun cli-compared rr-release
  rp-report ok? 0= if drop outcome-invalid then outcome>code ;

\ ---------------------------------------------------------------------------
\ print: the export (file 0) read as check --record reads it (its manifest
\ checked unless --no-manifest), read once more for binder names
\ (cli/print.fs), then each declaration checked in file order with the
\ derivation log on and printed right after its check with its proof
\ outline (present/proof-outline.fs: the verdict with its label and axioms,
\ the statement, the outline), or with --detail every step of its log.
\ With --name only that declaration is printed (the ones before it are
\ checked too, unprinted; the ones after it are not checked). No outline
\ is ever printed for a declaration that was not accepted, nor from a log
\ that ran out of room: the printer says why. Codes: those of check, from
\ the verdicts of the declarations printed (0 when every one is accepted,
\ whether or not its outline could be printed: an accepted declaration
\ whose log ran out of room says so in its text), 4 for a name no
\ declaration has, 5 when the run stopped (a check threw, publishing
\ failed, or the printer threw: then the log is switched off and the
\ environment freed all the same).
: cli-detail? ( -- flag ) cli-state opt-detail @ ;
: cli-named ( -- c-addr u ) cli-state opt-name 2@ ;
\ The declaration to print: its index, or -1 for all; false when none
\ has the name given.
: cli-chosen ( -- i true | false ) cli-named dup 0= if 2drop -1 true exit then pr-find ;
: cli-no-such ( -- )
  ." error: no declaration named " cli-named type cr exit-malformed cli-code! ;
: cli-shown? ( chosen i -- flag ) over 0< if 2drop true else = then ;
: cli-print-one ( i -- ) >r 0 cli-file r> cli-detail? pr-print outcome>code cli-code! ;
: cli-print-stopped ( -- )
  c" the run stopped: a check threw, or publishing failed" cli-fault ;
: cli-print-due ( chosen i -- chosen fault? )
  dup pr-step if drop true exit then over over cli-shown? if cli-print-one else drop then
  false ;
: cli-print-run ( chosen -- )
  lf-input-count 0 ?do
    i pr-due? if i cli-print-due if cli-print-stopped unloop drop exit then then
    dup i = if leave then
  loop drop ;
\ The environment of the run: made with the fuel and pool of check, made
\ current, and freed whatever happens in the run (a THROW is passed on
\ after it is freed).
: cli-env-made ( env outcome -- env true | false )
  dup ok? if drop true exit then nip outcome-full =
  if cli-no-room else c" no checked environment could be made" cli-fault then false ;
: cli-print-free ( env -- )
  lf-env-free ok? 0= if c" the checked environment could not be freed" cli-fault then ;
: cli-print-guarded ( env chosen -- env ior )
  over lf-env-use ok? 0= if drop c" the checked environment could not be used" cli-fault
  0 exit then ['] cli-print-run catch dup if nip then ;
: cli-print-env ( chosen -- )
  cli-fuel @ lf-check-budget cli-pool lf-env-new cli-env-made 0= if drop exit then
  swap cli-print-guarded swap cli-print-free throw ;
: cli-print-names ( -- flag )
  0 cli-file cli-checked? pr-present dup ok? if drop true else cli-unread false then ;
\ The log on for the run, and off again after it, also after a THROW.
: cli-printing ( -- )
  cli-print-names 0= if exit then cli-chosen 0= if cli-no-such exit then
  pr-log-on ['] cli-print-env catch lf-log-off lf-log-set throw ;
: print-command ( -- code )
  cli-start cli-opens? 0= if cli-unopened exit then cli-unchecked-note
  rr-release 0 cli-file cli-checked? rr-read-once dup ok?
  if drop cli-printing else cli-unread then cli-worst @ ;

\ ---------------------------------------------------------------------------
\ count: the report of ndjson-count.fs, or its error line.
: cli-count-read ( c-addr u -- outcome )
  cli-unchecked @ if count-plain-read else count-checked-read then ;
: cli-counted ( -- code )
  count-start dup ok? if drop 0 cli-file cli-count-read then
  dup ok? if drop .report exit-accepted else dup .count-error outcome>code then ;
: count-command ( -- code )
  cli-opens? if cli-unchecked-note cli-counted else cli-unopened then ;

\ reexport: the copy of ndjson-emit.fs, the manifest checked through
\ cli-manifest, bound to the re-exporter's export. COPY must not name
\ EXPORT (bin/leanforth also refuses one file under two names).
: cli-copy-checked ( c-addr u -- outcome )
  reexported cli-manifest manifest-init dup ok? 0= if nip nip exit then
  drop cli-manifest manifest-read ;
: cli-reader ( -- xt )
  cli-unchecked @ if ['] reexport-plain else ['] cli-copy-checked then ;
: cli-copy ( c-addr u fid -- outcome ) cli-reader reexport-read ;
\ The copy, then the file closed on every path; the first failure wins.
: cli-into ( c-addr u fid -- outcome )
  dup >r ['] cli-copy catch r> closed swap throw over ok? if nip else drop then ;
: cli-same? ( -- flag ) 0 cli-file 1 cli-file compare 0= ;
: cli-create ( -- fid true | false )
  1 cli-file w/o bin create-file 0= dup 0= if nip then ;
: cli-uncreated ( -- code ) ." error: cannot create the copy" cr exit-malformed ;
: cli-copied ( fid -- code )
  0 cli-file rot cli-into dup reexport-report reexport-free cli-manifest manifest-free
  outcome>code ;
: cli-reexported ( -- code ) cli-create if cli-copied else cli-uncreated then ;
: reexport-command ( -- code )
  cli-same? if ." error: COPY must not be EXPORT" cr exit-malformed exit then
  cli-opens? if cli-unchecked-note cli-reexported else cli-unopened then ;

\ ---------------------------------------------------------------------------
\ version and capabilities. The texts are lists, one line of output per
\ line of source, split by what they describe.
: cli-version-text ( -- c-addr u ) s" 0.1.0-dev" ;
[defined] version-string [if]
: cli-host. ( -- ) ." Gforth " version-string type ;
[else]
: cli-host. ( -- ) ." a Forth-2012 host" ;
[then]
: cli-reads. ( -- )
  ." reads: " pinned-exporter type space pinned-exporter-version type ." , format "
  pinned-format-version type ." , Lean " pinned-lean-version type ."  ("
  pinned-lean-githash type ." )" cr ;
: version-command ( -- code )
  ." leanforth " cli-version-text type
  ."  (development version; experimental, not independently audited)" cr
  ." forth: " cli-host. cr cli-reads. exit-accepted ;
: cli-check-input. ( -- )
  ."   check: Lean 4.35.0 exports (lean4export 3.1.0 NDJSON) of any size, such as" cr
  ."     all of Lean's Init, staged and fed in Forth; the manifest checked unless" cr
  ."     --no-manifest; a summary, --resources (time, memory, fuel), --json" cr ;
: cli-check-rules. ( -- )
  ."   check: definitions and theorems built from Sort, variables, application, fun," cr
  ."     forall and earlier accepted declarations (the first checker, ADR 0011)," cr
  ."     and inductive blocks that are not recursive, indexed or mutual (5.2.1a);" cr
  ."     an accepted one is labelled experimental, not independently audited" cr ;
: cli-other-commands. ( -- )
  ."   check --record, replay: run records 0.1 and their replay (plan task 2.2.5)" cr
  ."   print: a readable proof outline of each accepted declaration, from the" cr
  ."     checker's derivation log (plan tasks 2.4.1, 2.4.4; untrusted presentation)" cr
  ."   count, reexport: exports of any size, up to all of Mathlib" cr ;
: cli-checks. ( -- ) ." supported:" cr cli-check-input. cli-check-rules. cli-other-commands. ;
: cli-lacks. ( -- )
  ." not yet supported (check answers unsupported or unknown, exit 2):" cr
  ."   axioms (5.3.1), opaque declarations (4.2.6), unsafe and partial definitions;" cr
  ."   let (4.2.3), literals (5.2.3), projections (5.2.2) and metadata (4.1.3) in a term;" cr
  ."   recursive and indexed inductive types (5.2.1b, 5.2.1c), quotients (5.2.4)," cr
  ."   mutual and nested blocks (5.2.5); unfolding definitions (4.2.2), so some" cr
  ."   correct proofs end unknown; check --record, replay and print refuse" cr
  ."   inductive types while reading" cr ;
: cli-check-limits. ( -- )
  ."   check: stores that grow with the export (memory); a walk holds 64 levels" cr
  ."     of a term; " lf-env-dep-capacity .decimal ."  dependencies per declaration, "
  lf-env-pool-max .decimal ."  per export (plan task 6.2.0)" cr ;
: cli-small-limits. ( -- )
  ."   check --record, replay, print: " lf-name-capacity .decimal ."  names, "
  lf-level-capacity .decimal ."  levels, " lf-term-capacity .decimal ."  term nodes," cr
  ."     " lf-input-capacity .decimal ."  declarations per export, "
  cli-pool .decimal ."  dependencies per export" cr ;
: cli-limits. ( -- )
  ." limits (check answers full or exhausted, exit 3):" cr cli-check-limits.
  cli-small-limits.
  ."   universe parameters per declaration and universe arguments per constant:" cr
  ."     no fixed limit (memory)" cr
  ."   fuel " cli-default-fuel .decimal ."  steps per declaration (--fuel N, at most "
  cli-fuel-most cli-number-text type ." )" cr ;
: cli-planned. ( -- )
  ." planned, not built: program, serve, print and --record on any size," cr
  ."   the axiom names of each accepted declaration (plan task 5.3.2)" cr ;
: capabilities-command ( -- code )
  ." leanforth " cli-version-text type ." : what this build can do" cr
  cli-checks. cli-lacks. cli-limits. cli-planned. exit-accepted ;

\ ---------------------------------------------------------------------------
\ help, one part per kind of command.
: cli-check-usage. ( -- )
  ."   check [--no-manifest] [--fuel N] [--resources] [--json] EXPORT" cr
  ."       check every declaration of a Lean export, in file order, any size;" cr
  ."       --resources adds time, memory and fuel, --json prints it all as JSON" cr
  ."   check [--no-manifest] [--fuel N] --record RECORD EXPORT" cr
  ."       the same for a small export, and write its run record to RECORD" cr ;
: cli-other-usage. ( -- )
  ."   replay [--no-manifest] [--fuel N] EXPORT RECORD" cr
  ."       check the export again and compare the run record with RECORD" cr
  ."   print [--no-manifest] [--fuel N] [--detail] [--name NAME] EXPORT" cr
  ."       check the export and print each accepted declaration's proof outline" cr
  ."   count [--no-manifest] EXPORT     count the export's records by kind" cr
  ."   reexport [--no-manifest] EXPORT COPY" cr
  ."       write the export again, byte for byte as Lean's exporter writes it" cr ;
: cli-info-usage. ( -- )
  ."   version        versions of LeanForth, its Forth host and the format read" cr
  ."   capabilities   what this build supports, what it does not, and its limits" cr
  ."   help           this text" cr ;
: cli-usage. ( -- )
  ." usage: leanforth COMMAND [OPTION]... [FILE]..." cr
  cli-check-usage. cli-other-usage. cli-info-usage. ;
: cli-codes. ( -- )
  ." exit status: 0 all accepted (or done), 1 something rejected," cr
  ."   2 unsupported or unknown, 3 a resource limit, 4 malformed input or" cr
  ."   command line, 5 an internal fault, 6 all accepted but some NOT PROVED" cr
  ."   (proposed); the most severe of 5, 4, 1, 3, 2, 6 wins" cr ;
: help-command ( -- code ) cli-usage. cli-codes. exit-accepted ;

\ ---------------------------------------------------------------------------
\ The Forth interface: a command run with its arguments, any THROW
\ caught and reported as an internal fault.
: cli-thrown ( ior -- code )
  ." internal fault: a Forth exception (THROW " .decimal ." )" cr exit-fault ;
: cli-guard ( xt -- code ) catch ?dup if cli-thrown then ;
: cli-file! ( c-addr u k -- ) 2* cells cli-state arg-files + 2! ;
: cli-check ( c-addr u -- code ) 0 cli-file! ['] check-command cli-guard ;
: cli-replay ( export-addr export-u record-addr record-u -- code )
  1 cli-file! 0 cli-file! ['] replay-command cli-guard ;
: cli-print ( c-addr u -- code ) 0 cli-file! ['] print-command cli-guard ;
\ print's options: every step (--detail), one declaration (--name; the
\ name must stay unchanged meanwhile).
: cli-detail ( -- ) true cli-state opt-detail ! ;
: cli-name! ( c-addr u -- ) cli-state opt-name 2! ;
: cli-count ( c-addr u -- code ) 0 cli-file! ['] count-command cli-guard ;
: cli-reexport ( in-addr in-u out-addr out-u -- code )
  1 cli-file! 0 cli-file! ['] reexport-command cli-guard ;
: cli-version ( -- code ) ['] version-command cli-guard ;
: cli-capabilities ( -- code ) ['] capabilities-command cli-guard ;
: cli-help ( -- code ) ['] help-command cli-guard ;

\ ---------------------------------------------------------------------------
\ Reading the command line. The arguments after the command are the
\ options it takes and its file names; the first mistake is kept with its
\ argument and reported before anything runs.
[defined] next-arg [if]
: cli-arg ( -- c-addr u true | false ) next-arg over if true else 2drop false then ;
[else]
: cli-arg ( -- false ) false ;
[then]
: cli-wrong ( c-addr u why -- )
  cli-state arg-mistake @ if drop 2drop exit then
  cli-state arg-mistake ! cli-state arg-culprit 2! ;
: cli-mistake? ( -- flag ) cli-state arg-mistake @ 0<> ;

\ Tables of names: entries laid down by a defining word, the name last,
\ ending with a cell 0 where the next entry's word would be.
begin-structure /cli-entry
  field: cli-entry-run          \ the entry's word
  field: cli-entry-first        \ an option's bit; a command's number of file names
  field: cli-entry-second       \ a command's options, as bits; 0 for an option
  0 +field cli-entry-name       \ counted string, then aligned
end-structure
: cli-entry, ( xt first second "name" -- ) rot , swap , , parse-name counted, ;
: cli-entry-next ( entry -- entry' ) cli-entry-name count + aligned ;
: cli-entry-named? ( c-addr u entry -- c-addr u entry flag )
  dup >r cli-entry-name count 2over compare 0= r> swap ;
: cli-entry-find ( c-addr u table -- entry | 0 )
  begin dup @ while cli-entry-named? if nip nip exit then cli-entry-next repeat
  drop 2drop 0 ;

\ The options, as bits of the set a command takes. Each option's word
\ ( c-addr u -- ) is given the option's own text, and reads its value.
1 constant takes-no-manifest
2 constant takes-fuel
4 constant takes-record
8 constant takes-detail
16 constant takes-name
32 constant takes-resources
64 constant takes-json
: cli-value ( c-addr u -- c-addr' u' true | false )
  cli-arg if 2swap 2drop true else c" an option without its value" cli-wrong false then ;
\ A decimal number from 0 to max-n with nothing else: (n true) or false.
: do-digits ( c-addr u -- ud rest ) 0 0 2swap >number nip ;
: cli-digits ( c-addr u -- ud rest ) ['] do-digits in-decimal ;
: cli-in-range? ( ud -- n true | false ) 0= over 0< 0= and if true else drop false then ;
: cli-decimal ( c-addr u -- n true | false )
  dup 0= if 2drop false exit then cli-digits if 2drop false else cli-in-range? then ;
\ A fuel amount, at most cli-fuel-most.
: cli-fuel-value ( c-addr u n -- )
  dup cli-fuel-most > if drop c" a fuel amount above 9007199254740991" cli-wrong exit then
  cli-fuel! 2drop ;
: cli-fuel-option ( c-addr u -- )
  cli-value 0= if exit then 2dup cli-decimal
  if cli-fuel-value else c" not a fuel amount" cli-wrong then ;
: cli-record-option ( c-addr u -- ) cli-value if cli-record! then ;
: cli-manifest-option ( c-addr u -- ) 2drop cli-no-manifest ;
: cli-detail-option ( c-addr u -- ) 2drop true cli-state opt-detail ! ;
: cli-name-option ( c-addr u -- ) cli-value if cli-state opt-name 2! then ;
: cli-resources-option ( c-addr u -- ) 2drop cli-resources ;
: cli-json-option ( c-addr u -- ) 2drop cli-json ;
create cli-option-table
  ' cli-manifest-option takes-no-manifest 0 cli-entry, --no-manifest
  ' cli-fuel-option takes-fuel 0 cli-entry, --fuel
  ' cli-record-option takes-record 0 cli-entry, --record
  ' cli-detail-option takes-detail 0 cli-entry, --detail
  ' cli-name-option takes-name 0 cli-entry, --name
  ' cli-resources-option takes-resources 0 cli-entry, --resources
  ' cli-json-option takes-json 0 cli-entry, --json
  0 ,
: cli-takes? ( entry -- flag ) cli-entry-first @ cli-state arg-set @ and 0<> ;
: cli-taken ( c-addr u entry -- )
  dup cli-takes? if cli-entry-run @ execute exit then
  drop c" an option this command does not take" cli-wrong ;
: cli-option ( c-addr u -- )
  2dup cli-option-table cli-entry-find ?dup
  if cli-taken else c" an unknown option" cli-wrong then ;
\ A file name, the first or the second.
: cli-positional ( c-addr u -- )
  cli-files @ dup 2 < if cli-file! 1 cli-files +! exit then
  drop c" one file name too many" cli-wrong ;
: cli-option? ( c-addr u -- flag ) 1 min s" -" compare 0= ;
: cli-argument ( c-addr u -- ) 2dup cli-option? if cli-option else cli-positional then ;
: cli-arguments ( set -- )
  cli-state arg-set ! begin cli-arg while cli-argument repeat ;

\ The commands: each one's word ( -- code ), the number of file names it
\ needs and the options it takes.
takes-no-manifest takes-fuel or takes-record or takes-resources or takes-json or
constant check-set
takes-no-manifest takes-fuel or constant replay-set
takes-no-manifest takes-fuel or takes-detail or takes-name or constant print-set
create cli-commands
  ' check-command 1 check-set cli-entry, check
  ' replay-command 2 replay-set cli-entry, replay
  ' print-command 1 print-set cli-entry, print
  ' count-command 1 takes-no-manifest cli-entry, count
  ' reexport-command 2 takes-no-manifest cli-entry, reexport
  ' version-command 0 0 cli-entry, version
  ' version-command 0 0 cli-entry, --version
  ' capabilities-command 0 0 cli-entry, capabilities
  ' help-command 0 0 cli-entry, help
  ' help-command 0 0 cli-entry, --help
  ' help-command 0 0 cli-entry, -h
  0 ,

\ A mistake: what is wrong and its argument, then where help is; code 4.
: cli-misuse ( -- code )
  ." error: " cli-state arg-mistake @ count type cli-state arg-culprit 2@ dup
  if ." : " type else 2drop then cr ." try: leanforth help" cr exit-malformed ;
: cli-file-count ( entry -- entry )
  dup cli-entry-first @ cli-files @ = if exit then
  s" " c" a wrong number of file names" cli-wrong ;
: cli-unknown ( c-addr u -- code ) c" an unknown command" cli-wrong cli-misuse ;
: cli-known ( entry -- code )
  dup cli-entry-second @ cli-arguments cli-file-count
  cli-mistake? if drop cli-misuse else cli-entry-run @ cli-guard then ;
: cli-command ( c-addr u -- code )
  2dup cli-commands cli-entry-find ?dup if nip nip cli-known else cli-unknown then ;
: cli-line ( -- code )
  cli-options cli-arg if cli-command else cli-usage. exit-malformed then ;

\ Leaving the host with status 100 + code.
[defined] (bye) [if]
: cli-leave ( code -- ) 100 + (bye) ;
[else]
: cli-leave ( code -- ) drop -1 throw ;
[then]
\ The entry point: read the command line, run the command, leave.
: cli-main ( -- ) ['] cli-line cli-guard cli-leave ;

base !   \ the BASE this file was loaded with

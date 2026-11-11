\ The command line (plan tasks 3.4.1-3.4.3, v0): the Forth entry point that
\ bin/leanforth runs as `gforth src/main.fs -e cli-main COMMAND ...`.
\ Commands, documented in docs/user/COMMAND_LINE.md:
\   check [--no-manifest] [--fuel N] [--resources] [--json] [--fast]
\         [--strict-axioms] [--any-lean-version] [--jobs N] EXPORT
\       stage the Lean export with the importer stage (its manifest
\       checked unless --no-manifest says not to; with --any-lean-version
\       its metadata may name any exporter and Lean version of format
\       3.1.0, and a note says what it named: the verdicts stay those of
\       Lean 4.35.0's rules) and feed it to the
\       checker, whose stores grow to fit (cli/check-run.fs: any size, all
\       of Lean's Init), check every declaration in file order with
\       check-declaration through the checked environment's publisher,
\       and print one line per declaration with its verdict, read from
\       its published slot; then a summary with the accepted ones' label
\       and axioms; with --resources also the resource report (time and
\       CPU of each phase, peak memory, the input's size, fuel in all and
\       the ten declarations that used the most); with --json all of it
\       as one JSON text instead (cli/check-json.fs); with
\       --strict-axioms a NOT PROVED declaration gives exit 6; with
\       --jobs N, N workers check at once (cli/check-run.fs,
\       kernel/env-schedule.fs), the output the same as one's;
\   check [--no-manifest] [--fuel N] [--fast] [--strict-axioms]
\         --record RECORD EXPORT
\       the check of small exports that writes a run record (plan 2.2.5):
\       the export read into the checker's input at its default sizes
\       (import/checker-input.fs, which refuses inductive types), checked
\       by import/run-record.fs's run (rr-check), and printed as above;
\       run records 0.2 hold at most 32 declarations, so --record keeps
\       this path (docs/programming/RUN_RECORDS.md, "Version 0.2");
\   replay [--no-manifest] [--fuel N] [--fast] EXPORT RECORD
\       check the export again and compare the new run record with RECORD
\       (import/run-replay.fs): the replay report, exit 0 confirmed, 1
\       refused (a difference), 4 when it cannot be compared;
\   print [--no-manifest] [--fuel N] [--fast] [--detail] [--name NAME]
\         [--latex] [--statement FORMS] [--any-lean-version] EXPORT
\       check the export as check does, one declaration at a time with the
\       derivation log on, and print each one's proof outline right after
\       its check (cli/print.fs, present/proof-outline.fs), or with
\       --detail every step of its log; with --name only that declaration;
\       with --lf instead write the whole export, unchecked, as one
\       LeanForth text (cli/print-lf.fs);
\   count [--no-manifest] EXPORT          the record counts (ndjson-count.fs);
\   reexport [--no-manifest] EXPORT COPY  the byte-exact copy (ndjson-emit.fs);
\   version, capabilities, help (also --version, --help and -h).
\ --fast is bin/leanforth's: it runs gforth-fast instead of Gforth's
\ checking engine, gforth (owner, 2026-11-04); the Forth side only takes
\ it. Exit codes (cli/tally.fs): 0 all accepted (or the command done), 1
\ something rejected, 2 unsupported or unknown, 3 a resource limit (out of
\ fuel or room), 4 malformed input (also a malformed command line, or a
\ file that cannot be opened or created), 5 an internal fault (a Forth
\ exception, a check that threw, a publisher fault), 6 all accepted but
\ some NOT PROVED, only with --strict-axioms: by default NOT PROVED keeps
\ Lean's code (owner, 2026-11-04). When codes
\ differ, the most severe wins, in the order 5, 4, 1, 3, 2, 6, 0. cli-main
\ leaves the host with status 100 + code, so that bin/leanforth tells
\ LeanForth's codes from the host's own failures (Gforth ends with 0 or 1
\ after an uncaught error), and maps any other status to 5.
\
\ Trust boundary: "accepted" is printed only by lf-check-verdict.
\ (kernel/check-declaration.fs) from a declaration's published slot, and
\ the exit code comes from the slots' outcomes as lf-env-outcome reads
\ them, a rejected one marked skipped (an unsafe or partial declaration,
\ which Lean's replay skips: lf-env-skipped?) with Lean's code 0; staging,
\ parsing and printing here can hand the checker a wrong
\ claim or misreport a failure, never make a declaration accepted. Names
\ are printed as cli/name-text.fs shows them, escaped, so a crafted name
\ cannot forge a line. An accepted declaration that depends on an axiom
\ outside the allowlist (core/axiom-allowlist.fs) is marked NOT PROVED
\ on its line, with those axioms named, and counted apart (the owner's
\ rule). check
\ --record and replay hold small exports only (64 names, levels and term
\ nodes, 32 declarations): anything larger ends full, exit 3, and the
\ output says so. Untrusted, like everything in src/ until the review gate.
\
\ The Forth interface, for a Forth session or a test, each ( -- code )
\ after its arguments, printing what the command prints: cli-check
\ ( c-addr u ), cli-replay ( export-addr export-u record-addr record-u ),
\ cli-print ( c-addr u ), cli-count ( c-addr u ), cli-reexport ( in-addr
\ in-u out-addr out-u ), cli-version, cli-capabilities, cli-help. They use
\ the options in force: cli-options restores the defaults (manifest
\ checked, fuel cli-default-fuel, no record, text without the resource
\ report, NOT PROVED with Lean's code, the pinned versions only),
\ cli-no-manifest, cli-fuel!, cli-record!, cli-resources, cli-json,
\ cli-strict and cli-any-lean change them. A
\ THROW inside a command is caught and reported: code 5. A check that
\ threw spends its context (ADR 0012, G-P6): every
\ later check in that context ends invalid, with diagnostic 29, so a
\ session runs the next command in a new context (context-new).
\
\ Host words: next-arg (Gforth 0.7.3 and 1.0) reads the command line,
\ where a host without it reads none; (bye) leaves with a status, where a
\ host without it ends with an uncaught THROW, which the wrapper reports
\ as an internal fault; version-string names the host when it exists;
\ getenv reads the commit bin/leanforth found for the run record
\ (LEANFORTH_COMMIT, LEANFORTH_MODIFIED) and the engine it ran
\ (LEANFORTH_ENGINE, cli/check-run.fs), where a host without it records
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
require ../kernel/inductive-block.fs
require ../import/ndjson.fs
require ../import/manifest.fs
require ../import/checker-input.fs
require ../import/run-record.fs
require ../import/run-replay.fs
require ../import/ndjson-count.fs
require ../import/ndjson-emit.fs
require ./print.fs
require ./print-lf.fs
require ./tally.fs
require ./name-text.fs
require ./check-run.fs
require ./check-json.fs

20000000 constant cli-default-fuel   \ fuel of each declaration's check
: cli-version-text ( -- c-addr u ) s" 0.1.0-dev" ;   \ LeanForth's version
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
  field: opt-latex              \ true: print's outlines as LaTeX (--latex)
  field: opt-forms              \ print's statement forms (--statement), 0: all
  field: opt-lf                 \ true: print writes the export as LeanForth text (--lf)
  field: opt-strict             \ true: NOT PROVED gives exit 6 (--strict-axioms)
  field: opt-any-lean           \ true: an export of any Lean version (--any-lean-version)
  field: opt-jobs               \ workers that check at once (--jobs); 0, 1: one
  field: opt-fuel-given         \ true: --fuel was given
  2 cells +field opt-save       \ the snapshot to write (--save-snapshot), or 0 0
  2 cells +field opt-snapshot   \ the snapshot to read (--snapshot), or 0 0
  4 cells +field arg-files      \ the file names given, in order (two c-addr u)
  field: arg-count              \ how many were given
  field: arg-set                \ the options the command takes, as bits
  2 cells +field arg-culprit    \ the argument of the first mistake, or 0 0
  field: arg-mistake            \ counted string: the first mistake, or 0
  field: run-ops                \ the run the last check made: its words (/cli-ops)
  field: run-named              \ axioms named so far on a NOT PROVED line
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
\ check's exit code: NOT PROVED gives 6 (--strict-axioms), not Lean's code.
: cli-strict ( -- ) true cli-state opt-strict ! ;
: cli-strict? ( -- flag ) cli-state opt-strict @ ;
\ check and print: read an export whose metadata names another exporter
\ or Lean version, only its format pinned (--any-lean-version); the
\ verdicts stay those of Lean 4.35.0's rules, and a note says so.
: cli-any-lean ( -- ) true cli-state opt-any-lean ! ;
: cli-any-lean? ( -- flag ) cli-state opt-any-lean @ ;
\ check: how many workers check declarations at once (--jobs; plan task
\ 6.5.4); 0 or 1, the default, checks one at a time.
: cli-jobs ( -- n ) cli-state opt-jobs @ ;
: cli-jobs! ( n -- ) cli-state opt-jobs ! ;
: cli-checked? ( -- flag ) cli-unchecked @ 0= ;
\ check: write the run's snapshot to a file (--save-snapshot FILE), or
\ report a snapshot's verdicts without an export (--snapshot FILE; ADR
\ 0020, plan step SN3); each file name must stay unchanged meanwhile.
: cli-save! ( c-addr u -- ) cli-state opt-save 2! ;
: cli-save? ( -- flag ) cli-state opt-save @ 0<> ;
: cli-snapshot! ( c-addr u -- ) cli-state opt-snapshot 2! ;
: cli-snapshot? ( -- flag ) cli-state opt-snapshot @ 0<> ;
\ The fuel a snapshot run asks for: --fuel's, or -1 for the snapshot's.
: cli-asked-fuel ( -- n ) cli-state opt-fuel-given @ if cli-fuel @ else -1 then ;

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
: cli-unshown ( c-addr u -- )
  2drop ." [a name with no room to show]" exit-fault cli-code! ;
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
\ The room the --record run's dependency pool starts with, as make
\ run-record's; the pool grows (plan task 6.2.0).
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
\ holds (skipped, or its outcome; and NOT PROVED apart), the rest not
\ checked after a fault.
: cli-tally-one ( d -- )
  dup verdict-of cli-tally dup lf-env-outcome swap cli-bits cli-tally-proved ;
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
\ An accepted declaration that depends on an axiom outside the allowlist
\ is NOT PROVED, each such axiom named (in file order, separated by
\ commas; cli-axioms-named counts the names printed).
: cli-axioms-named ( -- addr ) cli-state run-named ;
: cli-axiom-named ( d -- )
  dup lf-env-unlisted? 0= if drop exit then
  cli-axioms-named @ if ." , " then 1 cli-axioms-named +! cli-name. ;
: cli-not-proved. ( d -- )
  dup lf-env-outcome over cli-bits not-proved? 0= if drop exit then
  ." ; NOT PROVED: depends on " 0 cli-axioms-named !
  ['] cli-axiom-named lf-env-axiom-deps drop cli-axioms-named @ 0= if ." an axiom" then ;
\ Declaration d's line: its name and the verdict its slot holds.
\ In a run of a snapshot (ADR 0020 D4, OQ-3) a verdict says where it comes
\ from: taken from the snapshot, not re-checked; or checked in this run
\ but resting on the snapshot's results (step SN4's dependent exports).
: cli-origin. ( origin -- )
  lf-origin-saved = if ." from snapshot, not re-checked in this run"
  else ." checked in this run, uses results from the snapshot" then ;
: cli-accepted-from. ( d origin -- )
  ." accepted (experimental, not independently audited; " cli-origin. ." ); "
  lf-env-axioms ok? if lf-check-axioms. else drop ." axioms: ?" then ;
: cli-failed-from. ( d origin -- )
  over lf-env-outcome rot swap lf-check-failed. ."  (" cli-origin. ." )" ;
: cli-labelled. ( d origin -- )
  over lf-env-outcome ok? if cli-accepted-from. else cli-failed-from. then ;
: cli-verdict. ( d -- )
  dup lf-env-origin ?dup if cli-labelled. else lf-check-verdict. then ;
: cli-verdict ( d -- )
  dup cli-name. ." : " dup cli-verdict. dup cli-not-proved. cr
  dup lf-env-outcome ok? if drop else cli-why. then ;
\ A declaration the stopped run never reached: verdict not checked, said
\ so that it cannot be read as skipped, the verdict of an unsafe or
\ partial declaration (review rvUNNI L5).
: cli-unreached ( d -- ) cli-name. ." : not checked (not reached: the run stopped)" cr ;
\ Why a run stopped, as far as the parallel scheduler knows (its cause).
: cli-reason ( -- c-addr u )
  lf-sched-cause CASE
    1 OF s" every worker was lost after a check threw and none could be made again" ENDOF
    2 OF s" the job pool refused a check" ENDOF
    3 OF s" waiting for a worker failed" ENDOF
    >r s" a check threw, or publishing failed" r>
  ENDCASE ;
: cli-stopped ( -- )
  ." internal fault: the run stopped: " cli-reason type cr
  lf-input-count cli-stepped ?do i cli-unreached loop ;
: cli-verdicts ( -- )
  cli-stepped 0 ?do i cli-verdict loop cli-faulted? if cli-stopped then ;

\ The summary: "N declarations: a accepted, r rejected, ...", in
\ cli/tally.fs's verdict order.
: cli-kind. ( verdict -- )
  dup not-checked = if drop ." not checked" else verdict-name type then ;
: cli-item ( first? verdict -- first? )
  dup cli-count-of @ ?dup 0= if drop exit then
  rot 0= if ." , " then .decimal space cli-kind. false ;
\ In a run with a snapshot (development mode), how many verdicts came
\ from it (review rvSN3 m6).
: cli-from-snapshot# ( -- n ) 0 lf-input-count 0 ?do i lf-env-origin lf-origin-saved = -
  loop ;
: cli-summary-label ( -- )
  ck-snapped? 0= if exit then
  ." ; " cli-from-snapshot# dup .decimal ."  from the snapshot, " lf-input-count swap -
  .decimal ."  checked in this run" ;
: cli-summary ( -- )
  lf-input-count dup .decimal ."  declaration" 1 <> if ." s" then ." : "
  true verdict-kinds 0 do i verdict-kind cli-item loop drop cli-summary-label cr ;
\ The accepted ones' label and axioms, read from their slots: none when
\ they use no axiom; else the allowlisted axioms they use (which count as
\ proved, docs/user/COMMAND_LINE.md), then how many are NOT PROVED, or
\ none (review rvAX L4).
: cli-listed. ( bits -- )
  lf-axiom-propext lf-check-axiom. lf-axiom-choice lf-check-axiom.
  lf-axiom-sound lf-check-axiom. drop ."  (allowlisted); " ;
: cli-unproved. ( -- )
  cli-not-proved @ ?dup 0= if ." none NOT PROVED" exit then
  .decimal ."  NOT PROVED (they depend on an axiom)" ;
: cli-axioms. ( -- )
  ." axioms: " cli-axioms-used @ ?dup 0= if ." none" exit then
  lf-allowlist-bits and ?dup if cli-listed. then cli-unproved. ;
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
  ." note: check --record and replay hold at most " lf-name-capacity .decimal
  ."  names, " lf-level-capacity .decimal ."  levels," cr ." note: "
  lf-term-capacity .decimal ."  term nodes and " lf-input-capacity .decimal
  ."  declarations per export; check without --record holds any size" cr ;
\ What can end a check full besides memory: the scratch each check has
\ above the input (import/feed.fs; plan task 6.2.2), which grows, up to
\ about 2^31 term nodes, levels and constant references each, unless the
\ context's setting (core/input.fs's lf-input-room!) sets a limit; before
\ compact-store plan step S5 it was fixed. A check's dependencies, the
\ pool and a block's constructors grow (plan task 6.2.0). The second line
\ begins with the text prefix.
: cli-scratch. ( prefix-addr prefix-u -- )
  ." each check's scratch above the input grows, up to " feed-term-room .decimal cr
  type ." term nodes, levels and constant references each (plan task 6.2.2)" cr ;
: cli-room-note ( -- )
  ." note: a check ran out of room; its diagnostic names the limit: memory, or" cr
  ." note: " s" note: " cli-scratch. ;
: cli-fuel-note ( -- )
  ." note: a check ran out of fuel (" cli-fuel @ .decimal
  ."  steps each); --fuel N gives each more" cr ;
\ NOT PROVED keeps Lean's exit status unless --strict-axioms asks for 6.
: cli-not-proved-note ( -- )
  ." note: NOT PROVED declarations keep Lean's exit status; --strict-axioms"
  cr ." note: makes it 6" cr ;
: cli-notes ( -- )
  outcome-full cli-count-of @ if cli-ops ops-room. @ execute then
  outcome-exhausted cli-count-of @ if cli-fuel-note then
  cli-not-proved @ cli-strict-axioms? 0= and if cli-not-proved-note then ;

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
\ before the environment was made. Whether it stopped is ck-stopped?, the
\ word the JSON report reads too.
: ck-no-env. ( -- )
  ck-facts-made? if ck-outcome cli-no-env. exit then
  ." error: no room for the run's facts (a record of each declaration)" cr ;
create cli-fed-ops
  ' ck-steps-begun , ' ck-outcome , ' ck-ours? , ' ck-kept , ' ck-stopped? ,
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

\ The environment's texts, where the host has getenv (see the run record
\ below and the snapshot's information).
[defined] getenv [if]
: cli-env ( c-addr u -- c-addr' u' ) getenv ;
[else]
: cli-env ( c-addr u -- c-addr' u' ) 2drop 0 0 ;
[then]
: cli-modified? ( -- flag ) s" LEANFORTH_MODIFIED" cli-env s" true" compare 0= ;

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
\ A snapshot refused (--snapshot): the outcome, what was refused, and the
\ record (slot or tier record) where it was.
: cli-snap-error ( -- )
  ." error: " ck-read-outcome outcome-text type ." : the snapshot was refused: "
  ck-snap snap-error >r type r> dup 0< if drop else ."  (record " .decimal ." )" then cr ;
: cli-fed-unread ( outcome -- )
  ck-snap-bad? if drop cli-snap-error exit then
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
\ The engine bin/leanforth ran: gforth, or gforth-fast with --fast.
: cli-engine-name. ( c-addr u -- ) nt-text if type else cli-unshown then ;
: cli-engine. ( -- )
  ."   engine: " ck-engine dup if cli-engine-name. else 2drop ." not known" then cr ;
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
  verdict-of verdict-name type ." )" cr ;
: cli-tops. ( -- )
  ck-tops 0= if exit then ."   most fuel used:" cr ck-tops 0 ?do i cli-top. loop ;
\ A parallel check's workers (--jobs; kernel/env-schedule.fs): checks
\ handed out, run again because they began too early, refused by
\ readiness, handed out only because nothing else could run (the last
\ two are 0 unless the plan is wrong), workers replaced after a THROW.
: cli-sched. ( -- )
  ."     checks handed out " lf-sched-launched .decimal ." , run again " lf-sched-reruns
  .decimal ." , not ready " lf-sched-unready .decimal ." , forced " lf-sched-forced
  .decimal ." , workers replaced " lf-sched-renewed .decimal cr ;
: cli-no-workers. ( -- )
  ck-why ck-why-host = if
    ."   workers: not used: threads need an x86-64 host (ADR 0009): checked one" cr
    ."     at a time" cr exit then
  ck-why if
    ."   workers: not used: the thread pool could not start (code " ck-why .decimal ." ):" cr
    ."     checked one at a time" cr exit then
  ."   workers: none could be made (no heap, or this context's input differs" cr
  ."     from a new one's): checked one at a time" cr ;
\ Cores that run workers at once: all on threads, one when they take turns.
: cli-cores ( -- n ) task-host task-threads = if task-cores else 1 then ;
: cli-jobs. ( -- )
  ck-parallel? 0= if exit then ck-jobs-run? 0= if cli-no-workers. exit then
  ."   workers: " ck-jobs .decimal ."  (--jobs), on " cli-cores .decimal ."  cores" cr
  cli-sched. ;
: cli-resources. ( -- )
  ." resources:" cr cli-times. cli-memory. cli-engine. cli-jobs. cli-input. cli-fuel.
  cli-tops. ;

\ An export whose metadata names another exporter or Lean version (read
\ with --any-lean-version): what it names, escaped as names are, so it
\ cannot forge a line; the verdicts are those of Lean 4.35.0's rules.
: cli-meta. ( k -- ) ck-stage stage-meta-text nt-text if type else cli-unshown then ;
: cli-made-by. ( -- )
  ." export made by Lean " 3 cli-meta. ."  (githash " 4 cli-meta. ." ), written by "
  0 cli-meta. space 1 cli-meta. ." ; verdicts are Lean " pinned-lean-version type ." 's" ;
: cli-other-note ( -- ) ck-other-lean? if ." note: " cli-made-by. cr then ;

\ The report: counted first, then printed, as text or as JSON
\ (cli/check-json.fs); a JSON text the writer refuses is an internal
\ fault, after the part already written.
: cli-save-failed? ( -- flag ) cli-save? ck-snap-saved@ ok? 0= and ;
: cli-fed-tally ( -- )
  ck-loaded? if cli-tally-run else ck-read-outcome outcome>code cli-code! then
  cli-save-failed? if ck-snap-saved@ outcome>code cli-code! then ;
\ A snapshot written (--save-snapshot), or why not; a snapshot read
\ (--snapshot): its file, identity and versions, the export it was
\ written from, how many results it gave, and the note that saved
\ results support no claim (ADR 0020 D4).
create cli-hex 64 allot
: cli-sha. ( c-addr -- ) cli-hex sha256-hex cli-hex 64 type ;
: cli-saved. ( -- )
  cli-save? 0= if exit then
  ck-snap-saved@ ?dup if ." error: the snapshot was not written: " outcome-text type cr
  else ." snapshot: written to " cli-state opt-save 2@ nt-text if type else cli-unshown
  then cr
  then ;
\ Whether a text is plain: letters, digits, ".", "-", "_", " " only.
: cli-plain? ( c-addr u -- flag )
  true -rot bounds ?do
    i count nip dup [char] a [char] z 1+ within over [char] A [char] Z 1+ within or
    over [char] 0 [char] 9 1+ within or over [char] . = or over [char] - = or
    over [char] _ = or swap bl = or and
  loop ;
\ The commit the snapshot's information names, or "unknown", also for a
\ text that is not plain (a line feed in it could forge a report line;
\ review rvSN3 m1).
: cli-commit-key ( -- c-addr u ) s\" \"commit\":\"" ;
: cli-quote-at ( c-addr u -- n )
  dup >r 0 ?do dup i + count nip [char] " = if drop i unloop r> drop exit then loop drop
  r> ;
: cli-shown-commit ( c-addr u -- c-addr' u' )
  2dup cli-plain? over 0<> and 0= if 2drop s" unknown" then ;
: cli-written-by ( -- c-addr u )
  ck-snap snap-info cli-commit-key search 0= if 2drop s" unknown" exit then
  cli-commit-key nip /string 2dup cli-quote-at nip cli-shown-commit ;
\ With an export (plan step SN4): how many of its declarations were
\ checked in this run, and how many share a name with a declaration of the
\ snapshot but the content of none.
: cli-import. ( -- )
  ck-importing? 0= if exit then
  ." import: " lf-input-count cli-from-snapshot# - .decimal ."  checked in this run; "
  ck-other# .decimal ."  with the name of a declaration of the snapshot, not its content"
  cr ;
: cli-snapshot. ( -- )
  ." snapshot: " cli-state opt-snapshot 2@ nt-text if type else cli-unshown then
  ."  (sha256 " ck-snap snap-sum cli-sha. ." ), export sha256 " ck-snap snap-export-sha
  cli-sha.
  ." , verdict version " lf-verdict-version .decimal ." , written by LeanForth "
  cli-written-by type ." : " cli-from-snapshot# .decimal
  ."  results taken from it, not re-checked in this run" cr cli-import.
  ." note: development and research mode: a final run re-checks everything from the" cr
  ." note: export and reads no snapshot; only its results support a claim" cr ;
: cli-fed-text ( -- )
  cli-other-note ck-loaded? if cli-results. else ck-read-outcome cli-fed-unread then
  ck-snapped? ck-loaded? and if cli-snapshot. then cli-saved.
  cli-resources? if cli-resources. then ;
\ Whether the export's manifest was checked: for a snapshot run without an
\ export, when the run that wrote the snapshot checked it.
: cli-manifest-checked? ( -- flag )
  ck-snap-only? if ck-snap snap-flags snap-enforced and 0<> else cli-checked? then ;
: cli-fed-json ( -- )
  0 cli-file cli-manifest-checked? cj-report dup ok? if drop exit then
  cr ." internal fault: the JSON report could not be written: " outcome-text type cr
  exit-fault cli-code! ;
: cli-fed-report ( -- ) cli-json? if cli-fed-json else cli-fed-text then ;
\ The information a snapshot keeps of the build that wrote it (ADR 0020
\ D3): never compared, only shown. A JSON text: the version, the commit
\ bin/leanforth found (LEANFORTH_COMMIT, LEANFORTH_MODIFIED), the host, the
\ engine and the cell width, each text kept only when it is plain (letters,
\ digits, ".", "-", "_", " "), else null.
create cli-info 512 allot
variable cli-info#
: cli-info+ ( c-addr u -- )
  dup cli-info# @ + 512 > if 2drop exit then
  tuck cli-info cli-info# @ + swap move cli-info# +! ;
: cli-info-text ( c-addr u -- )
  2dup cli-plain? over 0<> and
  if s\" \"" cli-info+ cli-info+ s\" \"" cli-info+ else 2drop s" null" cli-info+ then ;
: cli-info-host ( -- c-addr u ) [defined] version-string [if] version-string [else] 0 0
  [then] ;
: cli-info-build ( -- c-addr u )
  0 cli-info# ! s\" {\"leanforth\":" cli-info+ cli-version-text cli-info-text
  s\" ,\"commit\":" cli-info+ s" LEANFORTH_COMMIT" cli-env cli-info-text
  s\" ,\"modified\":" cli-info+ cli-modified? if s" true" else s" false" then cli-info+
  s\" ,\"gforth\":" cli-info+ cli-info-host cli-info-text
  s\" ,\"engine\":" cli-info+ ck-engine cli-info-text
  s\" ,\"cellBits\":" cli-info+ 1 cells 8 * cli-number-text cli-info+
  s" }" cli-info+ cli-info cli-info# @ ;
: cli-snapshot-save ( -- )
  cli-save? 0= if exit then cli-state opt-save 2@ cli-info-build ck-snapshot-save drop ;
: cli-library-run ( -- )
  0 cli-file cli-checked? ck-load ok? if ck-check cli-snapshot-save then
  cli-fed-tally cli-fed-report ;
\ check --snapshot FILE: the snapshot's verdicts, published again from it
\ (cli/check-run.fs ck-snapshot-load), no export read.
: cli-snapshot-run ( -- )
  cli-state opt-snapshot 2@ cli-asked-fuel ck-snapshot-load ok? if ck-check then
  cli-fed-tally cli-fed-report ;
\ check --snapshot FILE EXPORT: the export read on into the snapshot's
\ tier, what is the snapshot's taken from it, the rest checked (plan step
\ SN4; cli/check-run.fs ck-snapshot-import, kernel/env-import.fs).
: cli-import-run ( -- )
  cli-state opt-snapshot 2@ cli-asked-fuel ck-snapshot-import ok?
  if 0 cli-file cli-checked? ck-load ok? if ck-check then then
  cli-fed-tally cli-fed-report ;
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
  cli-any-lean? ck-any-version! cli-jobs ck-jobs! catch ck-release throw cli-restored
  cli-worst @ ;
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
\ Run records 0.2 hold the pinned versions only: --any-lean-version does
\ not go with --record either.
: cli-any-misused? ( -- flag ) cli-record? cli-any-lean? and ;
: cli-misuse-any ( -- code )
  ." error: --any-lean-version does not go with --record" cr
  ." try: leanforth help" cr exit-malformed ;
\ The run of small exports checks one declaration at a time: --jobs above
\ 1 does not go with --record.
: cli-jobs-misused? ( -- flag ) cli-record? cli-jobs 1 > and ;
: cli-misuse-jobs ( -- code )
  ." error: --jobs does not go with --record" cr
  ." try: leanforth help" cr exit-malformed ;
\ Snapshots (ADR 0020 D6): neither --snapshot nor --save-snapshot goes
\ with --record; a snapshot is not yet both read and written in one run.
: cli-snap-misused? ( -- flag ) cli-record? cli-snapshot? cli-save? or and ;
: cli-snap-both? ( -- flag ) cli-snapshot? cli-save? and ;
: cli-misuse-snap ( c-addr u -- code )
  ." error: " type cr ." try: leanforth help" cr exit-malformed ;
: cli-snap-misuse ( -- code|0 )
  cli-snap-misused? if s" --snapshot and --save-snapshot do not go with --record"
    cli-misuse-snap exit then
  cli-snap-both? if
  s" --snapshot and --save-snapshot do not go together yet (plan step SN4)"
    cli-misuse-snap exit then 0 ;
\ With an export (it must open), the export checked against the snapshot.
: cli-snapshot-check ( -- code )
  cli-files @ 0= if ['] cli-snapshot-run cli-fed-run exit then
  cli-opens? 0= if cli-not-opened exit then ['] cli-import-run cli-fed-run ;
: check-command ( -- code )
  cli-start cli-strict? cli-strict-axioms! cli-misused? if cli-misuse-record exit then
  cli-any-misused? if cli-misuse-any exit then
  cli-jobs-misused? if cli-misuse-jobs exit then
  cli-snap-misuse ?dup if exit then
  cli-snapshot? if cli-snapshot-check exit then
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
\ print: the export (file 0) staged and fed as check reads it (its manifest
\ checked unless --no-manifest; any size), with the feed's hooks that keep
\ binder names and declaration lines for the printer (cli/print.fs),
\ then each declaration checked in file order with the derivation log on
\ and printed right after its check with its proof outline
\ (present/proof-outline.fs: the verdict with its label and axioms, the
\ statement, the outline), or with --detail every step of its log. With
\ --name only that declaration is printed (the ones before it are checked
\ too, unprinted; the ones after it are not checked). No outline is ever
\ printed for a declaration that was not accepted, nor from a log that ran
\ out of room: the printer says why. Codes: those of check, from the
\ verdicts of the declarations printed (0 when every one is accepted,
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
  ." error: no declaration named " cli-named nt-text if type else cli-unshown then cr
  exit-malformed cli-code! ;
: cli-shown? ( chosen i -- flag ) over 0< if 2drop true else = then ;
: cli-print-one ( i -- ) >r 0 cli-file r> cli-detail? pr-print outcome>code cli-code! ;
: cli-print-stopped ( -- )
  ." internal fault: the run stopped: " cli-reason type cr exit-fault cli-code! ;
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
  cli-fuel @ lf-check-budget lf-env-pool-start lf-env-new cli-env-made 0= if drop exit then
  swap cli-print-guarded swap cli-print-free throw ;
\ The outline's style and the names it shows, set before the run.
: cli-style ( -- )
  cli-state opt-latex @ lf-outline-latex!
  cli-state opt-forms @ ?dup 0= if lf-forms-all then lf-forms!
  ['] nt-name ['] nt-text lf-outline-names! ;
\ The log on for the run, and off again after it, also after a THROW.
: cli-printing ( -- )
  cli-chosen 0= if cli-no-such exit then cli-style
  pr-log-on ['] cli-print-env catch lf-log-off lf-log-set throw ;
\ A read that failed, as check's is reported (cli-fed-unread), and its code.
: cli-print-unread ( outcome -- ) cli-fed-unread ck-read-outcome outcome>code cli-code! ;
\ --lf (cli/print-lf.fs): the whole export as one LeanForth text on the
\ standard output, unchecked, so nothing but the text goes there; options
\ that shape outlines do not go with it (a mistake, code 4).
: cli-lf? ( -- flag ) cli-state opt-lf @ 0<> ;
: cli-lf-misused? ( -- flag )
  cli-detail? cli-named nip 0<> or cli-state opt-latex @ 0<> or cli-state opt-forms @ 0<> or ;
: cli-lf-misuse ( -- )
  ." error: --lf does not go with --detail, --name, --latex or --statement" cr
  exit-malformed cli-code! ;
: cli-lf-note ( -- )
  cli-unchecked @ if s" \ note: the export's manifest was not checked (--no-manifest)" type cr then
  ck-other-lean? if ." \ note: " cli-made-by. cr then ;
: cli-lf-run ( -- )
  cli-lf-misused? if cli-lf-misuse exit then
  s" \ LeanForth text written by leanforth print --lf; untrusted presentation, not a proof" type cr
  cli-lf-note
  cli-fuel @ lf-file-write drop ;
: cli-print-library ( -- )
  0 cli-file cli-checked? pr-load dup ok? 0= if cli-print-unread exit then drop
  cli-lf? if cli-lf-run else cli-other-note cli-printing then ;
\ The run, then everything it holds freed, after a THROW too (passed on).
: print-command ( -- code )
  cli-start cli-opens? 0= if cli-unopened exit then
  cli-lf? 0= if cli-unchecked-note then ['] cli-print-library cli-fed-run ;

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
  ."     --no-manifest; a summary, --resources (time, memory, fuel), --json;" cr
  ."     Gforth's checking engine, or gforth-fast with --fast; --jobs N checks" cr
  ."     with N workers (threads on Gforth 1.0), the same output as one" cr ;
: cli-check-rules. ( -- )
  ."   check: Lean's kernel rules as built so far, each result labelled" cr
  ."     experimental, not independently audited: definitions, theorems, opaque" cr
  ."     declarations and axioms (an axiom outside Lean's standard three is NOT" cr
  ."     PROVED, as Lean's exit status 0); fun, forall, application, let," cr
  ."     number and string literals, projections, unfolding of definitions;" cr
  ."     proof irrelevance and eta; quotients; inductive types, recursive," cr
  ."     indexed and mutual ones, with their recursors; unsafe and partial" cr
  ."     declarations skipped, as Lean's replay skips them (5.2.7); several of" cr
  ."     these are merged but their review gates are open" cr
  ."     (docs/project/PROJECT_PROGRESS.md)" cr ;
: cli-other-commands. ( -- )
  ."   check --record, replay: run records 0.2 and their replay (plan task 2.2.5)" cr
  ."   print: a readable proof outline of each accepted declaration, from the" cr
  ."     checker's derivation log (plan tasks 2.4.1, 2.4.4; untrusted presentation)" cr
  ."   count, reexport: exports of any size, up to all of Mathlib" cr ;
: cli-checks. ( -- )
  ." supported:" cr cli-check-input. cli-check-rules. cli-other-commands. ;
: cli-lacks. ( -- )
  ." not yet supported (check answers unsupported or unknown, exit 2):" cr
  ."   nested inductive types (5.2.5b), a block with both safe and unsafe" cr
  ."   members (5.2.7 part b), metadata (mdata) in a term (4.1.3);" cr
  ."   recursor reductions on a variable (a follow-up of 5.2.2)," cr
  ."   so a correct proof can still end unknown;" cr
  ."   check --record and replay (the old reader) refuse inductive types, and" cr
  ."   answer unsupported for let, literals, projections and metadata;" cr
  ."   the checker has not yet checked a Mathlib declaration" cr
  ."   (0 of 729,263); check --jobs feeds each worker its own copy of the" cr
  ."   input's per-context part (the stage is shared; plan task 7.2.1)" cr ;
: cli-check-limits. ( -- )
  ."   check: stores, walks and lists that grow with the export (memory), any" cr
  ."     depth and number of dependencies or constructors (plan task 6.2.0);" cr
  ."     " s"     " cli-scratch. ;
: cli-small-limits. ( -- )
  ."   check --record, replay: " lf-name-capacity .decimal ."  names, "
  lf-level-capacity .decimal ."  levels, " lf-term-capacity .decimal ."  term nodes," cr
  ."     " lf-input-capacity .decimal ."  declarations per export" cr ;
: cli-limits. ( -- )
  ." limits (check answers full or exhausted, exit 3):" cr cli-check-limits.
  cli-small-limits.
  ."   universe parameters per declaration and universe arguments per constant:" cr
  ."     no fixed limit (memory)" cr
  ."   fuel " cli-default-fuel .decimal ."  steps per declaration (--fuel N, at most "
  cli-fuel-most cli-number-text type ." )" cr ;
: cli-planned. ( -- )
  ." planned, not built: program, serve and --record on any size," cr
  ."   every axiom name of each accepted declaration, as #print axioms" cr
  ."     (plan task 5.3.2; today: the allowlist's names and NOT PROVED's)" cr ;
: capabilities-command ( -- code )
  ." leanforth " cli-version-text type ." : what this build can do" cr
  cli-checks. cli-lacks. cli-limits. cli-planned. exit-accepted ;

\ ---------------------------------------------------------------------------
\ help, one part per kind of command.
: cli-check-usage. ( -- )
  ."   check [--no-manifest] [--fuel N] [--resources] [--json] [--fast]" cr
  ."         [--strict-axioms] [--any-lean-version] [--jobs N]" cr
  ."         [--save-snapshot FILE] EXPORT" cr
  ."       check every declaration of a Lean export, in file order, any size;" cr
  ."       --jobs N checks with N workers at once (default 1), same output;" cr
  ."       --resources adds time, memory and fuel, --json prints it all as JSON;" cr
  ."       --strict-axioms makes a NOT PROVED declaration exit 6;" cr
  ."       --any-lean-version (check, print) reads an export of another Lean or" cr
  ."       exporter version in format 3.1.0, its verdicts still Lean 4.35.0's;" cr
  ."       --save-snapshot FILE writes the checked environment to FILE" cr
  ."   check --snapshot FILE [--fuel N] [--resources] [--json] [--fast]" cr
  ."         [--no-manifest] [--jobs N] [EXPORT]" cr
  ."       the verdicts a snapshot holds, labelled, not re-checked (development" cr
  ."       and research only: a final run re-checks the export); with EXPORT," cr
  ."       its declarations the snapshot holds unchanged taken from it, the rest" cr
  ."       checked" cr
  ."   check [--no-manifest] [--fuel N] [--fast] [--strict-axioms]" cr
  ."         --record RECORD EXPORT" cr
  ."       the same for a small export, and write its run record to RECORD" cr ;
: cli-engine-usage. ( -- )
  ."   --fast (check, replay, print) runs gforth-fast, about 2.4 times quicker" cr
  ."       than Gforth's checking engine, the default, with the same verdicts" cr ;
: cli-other-usage. ( -- )
  ."   replay [--no-manifest] [--fuel N] [--fast] EXPORT RECORD" cr
  ."       check the export again and compare the run record with RECORD" cr
  ."   print [--no-manifest] [--fuel N] [--fast] [--detail] [--name NAME]" cr
  ."         [--latex] [--statement FORMS] [--any-lean-version] EXPORT" cr
  ."       check the export and print each accepted declaration's proof outline;" cr
  ."       FORMS: lean, mathematics, leanforth, all (default), joined by commas" cr
  ."   print --lf [--no-manifest] [--fuel N] [--fast] [--any-lean-version] EXPORT" cr
  ."       write every declaration as one LeanForth text, unchecked; what the" cr
  ."       words cannot write is listed on stderr and stubbed" cr
  ."   count [--no-manifest] EXPORT     count the export's records by kind" cr
  ."   reexport [--no-manifest] EXPORT COPY" cr
  ."       write the export again, byte for byte as Lean's exporter writes it" cr ;
: cli-info-usage. ( -- )
  ."   version        versions of LeanForth, its Forth host and the format read" cr
  ."   capabilities   what this build supports, what it does not, and its limits" cr
  ."   help           this text" cr ;
: cli-usage. ( -- )
  ." usage: leanforth COMMAND [OPTION]... [FILE]..." cr
  cli-check-usage. cli-other-usage. cli-info-usage. cli-engine-usage. ;
: cli-codes. ( -- )
  ." exit status: 0 all accepted (or done), 1 something rejected," cr
  ."   2 unsupported or unknown, 3 a resource limit, 4 malformed input or" cr
  ."   command line, 5 an internal fault, 6 all accepted but some NOT PROVED" cr
  ."   (with --strict-axioms; else 0, as Lean); the most severe of" cr
  ."   5, 4, 1, 3, 2, 6 wins" cr ;
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
128 constant takes-latex
256 constant takes-statement
512 constant takes-strict
1024 constant takes-fast
2048 constant takes-lf
4096 constant takes-any-lean
8192 constant takes-jobs
16384 constant takes-save
32768 constant takes-snapshot
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
  cli-fuel! 2drop true cli-state opt-fuel-given ! ;
: cli-fuel-option ( c-addr u -- )
  cli-value 0= if exit then 2dup cli-decimal
  if cli-fuel-value else c" not a fuel amount" cli-wrong then ;
: cli-record-option ( c-addr u -- ) cli-value if cli-record! then ;
: cli-save-option ( c-addr u -- ) cli-value if cli-save! then ;
: cli-snapshot-option ( c-addr u -- ) cli-value if cli-snapshot! then ;
: cli-manifest-option ( c-addr u -- ) 2drop cli-no-manifest ;
: cli-detail-option ( c-addr u -- ) 2drop true cli-state opt-detail ! ;
: cli-name-option ( c-addr u -- ) cli-value if cli-state opt-name 2! then ;
: cli-resources-option ( c-addr u -- ) 2drop cli-resources ;
: cli-json-option ( c-addr u -- ) 2drop cli-json ;
: cli-latex-option ( c-addr u -- ) 2drop true cli-state opt-latex ! ;
\ --statement FORMS: lean, mathematics, leanforth (or all), separated by commas.
: cli-statement-option ( c-addr u -- )
  cli-value 0= if exit then 2dup pr-forms
  if cli-state opt-forms ! 2drop else c" not a list of statement forms" cli-wrong then ;
: cli-strict-option ( c-addr u -- ) 2drop cli-strict ;
\ --fast: bin/leanforth chose the engine before Forth ran; nothing to do.
: cli-fast-option ( c-addr u -- ) 2drop ;
: cli-lf-option ( c-addr u -- ) 2drop true cli-state opt-lf ! ;
: cli-any-lean-option ( c-addr u -- ) 2drop cli-any-lean ;
\ --jobs N, N at least 1; check-run.fs cuts it to the cores. Each worker holds a
\ copy of the input, so memory grows with the workers made.
: cli-jobs-value ( c-addr u n -- )
  dup 1 < if drop c" not a number of jobs" cli-wrong exit then
  cli-state opt-jobs ! 2drop ;
: cli-jobs-option ( c-addr u -- )
  cli-value 0= if exit then 2dup cli-decimal
  if cli-jobs-value else c" not a number of jobs" cli-wrong then ;
create cli-option-table
  ' cli-manifest-option takes-no-manifest 0 cli-entry, --no-manifest
  ' cli-fuel-option takes-fuel 0 cli-entry, --fuel
  ' cli-record-option takes-record 0 cli-entry, --record
  ' cli-detail-option takes-detail 0 cli-entry, --detail
  ' cli-name-option takes-name 0 cli-entry, --name
  ' cli-resources-option takes-resources 0 cli-entry, --resources
  ' cli-json-option takes-json 0 cli-entry, --json
  ' cli-latex-option takes-latex 0 cli-entry, --latex
  ' cli-statement-option takes-statement 0 cli-entry, --statement
  ' cli-strict-option takes-strict 0 cli-entry, --strict-axioms
  ' cli-fast-option takes-fast 0 cli-entry, --fast
  ' cli-lf-option takes-lf 0 cli-entry, --lf
  ' cli-any-lean-option takes-any-lean 0 cli-entry, --any-lean-version
  ' cli-jobs-option takes-jobs 0 cli-entry, --jobs
  ' cli-save-option takes-save 0 cli-entry, --save-snapshot
  ' cli-snapshot-option takes-snapshot 0 cli-entry, --snapshot
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
takes-no-manifest takes-fuel or takes-fast or constant checking-set
checking-set takes-record or takes-resources or takes-json or takes-strict or
takes-any-lean or takes-jobs or takes-save or takes-snapshot or constant check-set
checking-set constant replay-set
checking-set takes-detail or takes-name or takes-latex or takes-statement or
takes-lf or takes-any-lean or constant print-set
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
\ check --snapshot takes no export (with one, step SN4's, it is refused
\ when it runs).
: cli-files-wanted? ( entry -- flag )
  cli-entry-first @ cli-files @ 2dup = if 2drop true exit then
  swap 1- = cli-snapshot? and ;
: cli-file-count ( entry -- entry )
  dup cli-files-wanted? if exit then
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

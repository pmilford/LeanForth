\ The command line (plan tasks 3.4.1-3.4.3, v0): the Forth entry point that
\ bin/leanforth runs as `gforth src/main.fs -e cli-main COMMAND ...`.
\ Commands, documented in docs/user/COMMAND_LINE.md:
\   check [--no-manifest] [--fuel N] [--resources] [--json] [--fast]
\         [--strict-axioms] [--any-lean-version] [--jobs N]
\         [--memory-per-check MB] EXPORT
\       stage the Lean export with the importer stage (its manifest
\       checked unless --no-manifest says not to; with --any-lean-version
\       its metadata may name any exporter and Lean version of format
\       3.1.0, and a note says what it named: the verdicts stay those of
\       Lean 4.35.0's rules) and feed it to the
\       checker, whose stores grow to fit (cli/check-run.fs: any size, all
\       of Lean's Init), check every declaration in file order with
\       check-declaration through the checked environment's publisher,
\       and print one line per declaration with its verdict, read from
\       its published slot; then a summary with the accepted ones' count
\       and axioms; with --resources also the resource report (time and
\       CPU of each phase, peak memory, the input's size, fuel in all and
\       the ten declarations that used the most); with --json all of it
\       as one JSON text instead (cli/check-json.fs); with
\       --strict-axioms a NOT PROVED declaration gives exit 6; with
\       --jobs N, N workers check at once (cli/check-run.fs,
\       kernel/env-schedule.fs), the output the same as one's; with
\       --memory-per-check MB, a check whose scratch would pass MB
\       megabytes is full (core/scratch-meter.fs);
\   check [--no-manifest] [--fuel N] [--fast] [--strict-axioms]
\         --record RECORD EXPORT
\       the check of small exports that writes a run record (plan 2.2.5):
\       the export read into the checker's input at its default sizes
\       (import/checker-input.fs, which refuses inductive types), checked
\       by import/run-record.fs's run (rr-check), and printed as above;
\       run records 0.3 hold at most 32 declarations, so --record keeps
\       this path (docs/programming/RUN_RECORDS.md, "Versioning");
\   replay [--no-manifest] [--fuel N] [--fast] EXPORT RECORD
\       check the export again and compare the new run record with RECORD
\       (import/run-replay.fs): the replay report, exit 0 confirmed, 1
\       refused (a difference), 4 when it cannot be compared;
\   print [--no-manifest] [--fuel N] [--fast] [--detail] [--name NAME]
\         [--latex] [--statement FORMS] [--kernel] [--any-lean-version] EXPORT
\       check the export as check does, one declaration at a time with the
\       derivation log on, and print each one's proof outline right after
\       its check (cli/print.fs, present/proof-outline.fs), or with
\       --detail every step of its log; with --name only that declaration;
\       with --lf instead write the whole export, unchecked, as one
\       LeanForth text (cli/print-lf.fs);
\   count [--no-manifest] EXPORT          the record counts (ndjson-count.fs);
\   reexport [--no-manifest] EXPORT COPY  the byte-exact copy (ndjson-emit.fs);
\   version, capabilities, help (also --version, --help and -h).
\ --fast and --checked are bin/leanforth's: gforth-fast is the default engine,
\ --checked runs Gforth's checking engine, gforth (owner, 2026-11-11); the
\ Forth side only takes them. Exit codes (cli/tally.fs): 0 all accepted (or the command done), 1
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
\ are printed as present/name-text.fs shows them, escaped, so a crafted name
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
require ../lib/blocks.fs
require ../lib/bounds.fs
require ../lib/decimal.fs
require ../lib/bits.fs
require ../lib/text-run.fs
require ../lib/name-table.fs
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
require ../present/name-text.fs
require ./check-run.fs
require ./check-lf.fs
require ./check-json.fs
require ../front/meta-config.fs
require ../front/elab-decl.fs
require ../front/step-log.fs

100000000 constant cli-default-fuel   \ fuel of each declaration's check
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
  field: opt-kernel             \ true: print terms as the kernel has them, no notation (--kernel)
  field: opt-strict             \ true: NOT PROVED gives exit 6 (--strict-axioms)
  field: opt-any-lean           \ true: an export of any Lean version (--any-lean-version)
  field: opt-jobs               \ workers that check at once (--jobs); 0, 1: one
  field: opt-fuel-given         \ true: --fuel was given
  2 cells +field opt-save       \ the snapshot to write (--save-snapshot), or 0 0
  2 cells +field opt-snapshot   \ the snapshot to read (--snapshot), or 0 0
  field: opt-layers             \ the layers on it (--snapshot again): (c-addr u) each
  field: opt-layers#            \ how many
  field: opt-stale              \ true: a snapshot of an older verdict version may load
  4 cells +field arg-files      \ the file names given, in order (two c-addr u)
  field: arg-count              \ how many were given
  field: arg-set                \ the options the command takes, as bits
  2 cells +field arg-culprit    \ the argument of the first mistake, or 0 0
  field: arg-mistake            \ counted string: the first mistake, or 0
  field: run-ops                \ the run the last check made: its words (/cli-ops)
  field: run-named              \ axioms named so far on a NOT PROVED line
  field: opt-progress           \ true: progress lines on stderr (--progress)
  field: opt-progress-secs      \ seconds between them (--progress[=SECONDS])
  field: run-printed            \ verdict lines already written, as the run went
  field: run-noted              \ true: the other-version note came before them
  field: opt-memory             \ megabytes each check's scratch may hold
                                \ (--memory-per-check); 0: no limit
  2 cells +field opt-env        \ the library export of a LeanForth text (--env), or 0 0
  2 cells +field opt-elab       \ the library's elaboration data (--elab-data), or 0 0
  field: opt-elab-fuel          \ elaboration steps of a declaration (--elab-fuel)
  field: opt-elab-fuel-given    \ true: --elab-fuel was given
  2 cells +field opt-steps      \ the step log's file, or - (--steps), or 0 0
  field: run-steps-fid          \ the step log's file while it is written
  field: run-steps-bad          \ true: writing it (or an axiom's name) failed
  field: run-steps-axiom        \ xt ( c-addr u -- ): where an axiom's name goes
  2field: run-steps-whole       \ the step log's bytes through its last line feed
  field: run-steps-uncut        \ true: the failed log could not be cut back
  field: arg-seen               \ every argument read, 0 the command: its address each
  field: arg-seen#              \ how many
  field: arg-paths              \ the files the command reads and writes (/cli-path each)
  field: arg-paths#             \ how many
  field: opt-engines            \ 1: --fast given, 2: --checked given (both: a mistake)
end-structure
/cli-run context-record: cli-state
manifest: cli-manifest

: cli-unchecked ( -- addr ) cli-state opt-unchecked ;
: cli-fuel ( -- addr ) cli-state opt-fuel ;
: cli-record ( -- addr ) cli-state opt-record ;
: cli-file ( k -- c-addr u ) 2* cells cli-state arg-files + 2@ ;
: cli-files ( -- addr ) cli-state arg-count ;

\ Options. cli-options also forgets the file names, any mistake and an
\ earlier command's memory limit per check (cli-fed-run sets this one's).
: cli-options ( -- )
  cli-state /cli-run erase cli-default-fuel cli-fuel ! 0 lf-meter-limit! ;
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
\ check: the megabytes (of 2^20 bytes) each declaration's check may hold
\ in scratch (--memory-per-check; core/scratch-meter.fs); 0, the
\ default, sets no limit but the heap's. A check past it is full.
: cli-per-check ( -- mb ) cli-state opt-memory @ ;
: cli-per-check! ( mb -- ) cli-state opt-memory ! ;
: cli-per-check-apply ( -- ) cli-per-check 20 lshift lf-meter-limit! ;
\ check: a progress line on stderr every SECONDS (--progress[=SECONDS],
\ default 60; 0: after every report), and the text report's verdict lines
\ written as they become final (cli/check-run.fs).
60 constant cli-progress-default
: cli-progress! ( seconds -- )
  cli-state opt-progress-secs ! true cli-state opt-progress ! ;
: cli-progress? ( -- flag ) cli-state opt-progress @ ;
: cli-progress-apply ( -- )
  cli-progress? if cli-state opt-progress-secs @ ck-progress! then ;
: cli-checked? ( -- flag ) cli-unchecked @ 0= ;
\ check: write the run's snapshot to a file (--save-snapshot FILE), or
\ report a snapshot's verdicts without an export (--snapshot FILE; ADR
\ 0020, plan step SN3); each file name must stay unchanged meanwhile.
: cli-save! ( c-addr u -- ) cli-state opt-save 2! ;
: cli-save? ( -- flag ) cli-state opt-save @ 0<> ;
: cli-snapshot! ( c-addr u -- ) cli-state opt-snapshot 2! ;
: cli-snapshot? ( -- flag ) cli-state opt-snapshot @ 0<> ;
\ --snapshot-stale-ok (a development flag, owner 2026-11-11; ADR 0020
\ amendment 3): a snapshot of an older verdict version loads, its results
\ reported as stale, never as this build's verdicts.
: cli-stale? ( -- flag ) cli-state opt-stale @ ;
\ The fuel a snapshot run asks for: --fuel's, or -1 for the snapshot's.
: cli-asked-fuel ( -- n ) cli-state opt-fuel-given @ if cli-fuel @ else -1 then ;

\ Numbers in decimal, whatever BASE is: lib/decimal.fs (.decimal,
\ u>decimal, in-decimal).
\ An internal fault: one line, and code 5.
: cli-fault ( c-addr -- ) ." internal fault: " count type cr exit-fault cli-code! ;
: cli-note ( c-addr -- ) ." note: " count type cr ;
\ A declaration's name as present/name-text.fs shows it; one the heap cannot
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
\ No room is a resource limit; anything else is a fault.
: full-or-fault ( outcome -- code ) outcome-full = if exit-limit else exit-fault then ;

\ Counting: each declaration whose check began by the verdict its slot
\ holds (skipped, or its outcome; and NOT PROVED apart), the rest not
\ checked after a fault.
: cli-tally-one ( d -- )
  dup verdict-of cli-tally dup decl-outcome swap decl-axioms cli-tally-proved ;
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
: cli-depends. ( d -- )
  ." depends on " 0 cli-axioms-named !
  ['] cli-axiom-named lf-env-axiom-deps drop cli-axioms-named @ 0= if ." an axiom" then ;
: cli-not-proved. ( d -- )
  dup decl-outcome over decl-axioms not-proved?
  if ." ; NOT PROVED: " cli-depends. else drop then ;
\ Declaration d's line: its name and the verdict its slot holds.
\ In a run of a snapshot (ADR 0020 D4, OQ-3) a verdict says where it comes
\ from: taken from the snapshot, not re-checked; or checked in this run
\ but resting on the snapshot's results (step SN4's dependent exports).
\ With a stale snapshot (--snapshot-stale-ok), the verdict is labelled
\ stale: another build's rules, not this one's.
: cli-stale-from. ( -- ) ." from a stale snapshot (an older verdict version), not this "
  ." build's verdict" ;
\ In a carry run (plan step 6.2.5c3; a snapshot of an older verdict
\ version inside the window) a carried result names the version it comes
\ from, and a declaration checked again says why (env-import.fs why-*).
: cli-carried-from. ( -- )
  ." from snapshot of verdict version " ck-snap snap-verdict .decimal
  ." , carried: this build's changes since cannot affect it; not re-checked in this run" ;
: cli-taken-from. ( d -- )
  ck-carried? if cli-carried-from. exit then
  ck-stale? if cli-stale-from. else ." from snapshot, not re-checked in this run" then ;
: cli-reach-why. ( why -- )
  ." : inside the reach of verdict version " why-step .decimal ." 's change" ;
: cli-why-again. ( why -- )
  dup why-code case why-reach of cli-reach-why. endof
    why-outcome of drop ." : its saved outcome is never carried" endof
    nip ." : a result its lookups reach answers otherwise now" endcase ;
: cli-here. ( d -- )
  ." checked in this run" dup ck-reason ?dup if cli-why-again. then
  lf-env-origin lf-origin-uses = if
    ." , uses results from the " ck-stale? if ." stale " then ." snapshot" then ;
: cli-origin. ( d origin -- d )
  over swap lf-origin-saved = if cli-taken-from. else cli-here. then ;
\ The axioms of an accepted declaration, never unknown (tally.fs
\ decl-axioms: axioms it cannot read are an internal fault).
: cli-accepted-from. ( d origin -- )
  ." accepted (" cli-origin. ." ); " decl-axioms lf-check-axioms. ;
: cli-failed-from. ( d origin -- )
  over dup decl-outcome lf-check-failed. ."  (" cli-origin. drop ." )" ;
: cli-labelled. ( d origin -- )
  over decl-accepted? if cli-accepted-from. else cli-failed-from. then ;
: cli-labelled? ( d -- flag ) dup lf-env-origin swap ck-reason or 0<> ;
\ Unlabelled, as check-declaration's lf-check-verdict. prints it, accepted
\ only as tally.fs's decl-accepted? means it.
: cli-plain. ( d -- )
  dup decl-accepted? if ." accepted; " decl-axioms lf-check-axioms. exit then
  dup decl-outcome lf-check-failed. ;
: cli-verdict. ( d -- )
  dup cli-labelled? if dup lf-env-origin cli-labelled. else cli-plain. then ;
: cli-verdict ( d -- )
  dup cli-name. ." : " dup cli-verdict. dup cli-not-proved. cr
  dup decl-accepted? if drop else cli-why. then ;
\ A declaration the stopped run never reached: verdict not checked, said
\ so that it cannot be read as skipped, the verdict of an unsafe or
\ partial declaration (review rvUNNI L5).
: cli-unreached ( d -- ) cli-name. ." : not checked (not reached: the run stopped)" cr ;
\ Why a run stopped, as far as the parallel scheduler knows (its cause),
\ or the input the workers read moved during the run (check-run.fs's
\ ck-shift?).
: cli-moved-reason ( -- c-addr u )
  s" the input the workers read in place changed during the run" ;
: cli-sched-reason ( -- c-addr u )
  lf-sched-cause CASE
    1 OF s" every worker was lost after a check threw and none could be made again" ENDOF
    2 OF s" the job pool refused a check" ENDOF
    3 OF s" waiting for a worker failed" ENDOF
    >r s" a check threw, or publishing failed" r>
  ENDCASE ;
: cli-reason ( -- c-addr u ) ck-shifted? if cli-moved-reason else cli-sched-reason then ;
: cli-stopped ( -- )
  ." internal fault: the run stopped: " cli-reason type cr
  lf-input-count cli-stepped ?do i cli-unreached loop ;
\ The lines a run wrote as it went (check-run.fs's ck-lines!) are the first
\ ones; the rest are written here, so a finished run's report is the same.
\ A NOT PROVED line names the axioms it rests on (lf-env-axiom-deps), which
\ every earlier slot, final by now, gives the same set as at the end.
: cli-stream ( d -- flag ) cli-verdict 1 cli-state run-printed +! true ;
: cli-printed ( -- n ) cli-state run-printed @ ;
: cli-verdicts ( -- )
  cli-stepped cli-printed 2dup > if ?do i cli-verdict loop else 2drop then
  cli-faulted? if cli-stopped then ;

\ The summary: "N declarations: a accepted, r rejected, ...", in
\ cli/tally.fs's verdict order.
: cli-kind. ( verdict -- )
  dup not-checked = if drop ." not checked" else verdict-name type then ;
\ A comma before every item after the first: first? from under x and n.
: cli-comma ( first? n -- n ) swap 0= if ." , " then ;
: cli-comma-under ( first? x n -- x n ) rot swap cli-comma ;
: cli-item ( first? verdict -- first? )
  dup cli-count-of @ ?dup 0= if drop exit then
  cli-comma-under .decimal space cli-kind. false ;
: cli-stale-of. ( n -- ) .decimal ck-stale? if ."  stale" then ;
: cli-from. ( -- )
  ck-carrying? 0= if ck-saved# cli-stale-of. exit then ck-carried# .decimal
  ."  carried" ck-stale? if ."  and " ck-stale# cli-stale-of. then ;
: cli-summary-label ( -- )
  ck-snapped? 0= if exit then ." ; " cli-from. ."  from the snapshot, "
  lf-input-count ck-saved# - .decimal ."  checked in this run" ;
: cli-summary ( -- )
  lf-input-count dup .decimal ."  declaration" 1 <> if ." s" then ." : "
  true verdict-kinds 0 do i verdict-kind cli-item loop drop cli-summary-label cr ;
\ How many were accepted, and their axioms, read from their slots: none when
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
  ." accepted: " .decimal ." ; " cli-axioms. cr ;

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
\ Whether a check passed its memory limit (--memory-per-check): its
\ diagnostic says so.
: cli-over-memory? ( -- flag )
  false cli-stepped 0 ?do i cli-kept kept-code @ lf-diag-memory-limit = or loop ;
: cli-per-check-note ( -- )
  ." note: a check passed its memory limit (" cli-per-check .decimal
  ."  MB each); --memory-per-check MB gives each more" cr ;
: cli-notes ( -- )
  outcome-full cli-count-of @ if cli-ops ops-room. @ execute then
  cli-over-memory? if cli-per-check-note then
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
\ (0 for the manifest), and for a JSON error the byte within the line
\ (import/ndjson.fs's .export-where).
: cli-error-head ( why-addr why-u outcome -- )
  ." error: " outcome-text type ." : " type ;
: cli-input-error ( outcome -- )
  cin-export swap >r cin-error r> cli-error-head .export-where cr ;
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
  ck-stage stage-export swap >r ck-stage stage-error r> cli-error-head
  .export-where cr ;
: cli-stage-manifest? ( outcome -- flag )
  outcome-invalid = cli-checked? and ck-stage stage-error 2drop 2drop 0= and
  ck-stage stage-why @ 0= and ;
: cli-feed-error ( outcome -- )
  s" the staged export could not be fed to the checker" rot cli-error-head
  ."  (it stopped at expression or declaration " ck-feeding-record feed-at .decimal
  ." )" cr ;
\ A snapshot refused (--snapshot): the outcome, what was refused, and the
\ record (slot or tier record) where it was.
: cli-snap-error ( -- )
  ." error: " ck-read-outcome outcome-text type ." : the snapshot was refused: "
  ck-snap snap-error >r type r> dup 0< if drop else ."  (record " .decimal ." )" then cr ;
\ A snapshot refused for its verdict version (plan step 6.2.5c3, R9): the
\ versions this build reads, and the ways on; for an older base with
\ layers or an older layer (plan step 6.2.5c7), or for a change of the
\ importer since (review of snap-compat L1, M2), why and the ways on.
: cli-why-is? ( c-addr u -- flag )
  ck-snap snap-why @ ?dup if count compare 0= else 2drop false then ;
: cli-older-note ( -- )
  ." note: this build reads snapshots of verdict versions "
  lf-verdict-version lf-window-oldest .decimal ."  to " lf-verdict-version .decimal
  ." : check the export" cr
  ." note: again, or look with --snapshot-stale-ok (every result stale)" cr ;
: cli-newer-note ( -- )
  ." note: the snapshot's verdict version is newer than this build's ("
  lf-verdict-version .decimal ." ): use the build that wrote it" cr ;
: cli-version-note ( -- )
  ck-snap snap-verdict lf-verdict-version > if cli-newer-note else cli-older-note then ;
: cli-layered-note ( -- )
  ." note: layers on or of a snapshot of an older verdict version load with plan step" cr
  ." note: 6.2.5c7: check the exports again, or look with --snapshot-stale-ok" cr ;
: cli-reading-note ( -- )
  ." note: this build reads exports otherwise than the build that wrote the snapshot:" cr
  ." note: check the export (or check --snapshot FILE EXPORT), or look with" cr
  ." note: --snapshot-stale-ok (every result stale)" cr ;
: cli-layered? ( -- flag )
  s" older base with layers" cli-why-is? s" older layer" cli-why-is? or ;
: cli-window-note ( -- )
  s" verdict version" cli-why-is? if cli-version-note exit then
  s" export reading" cli-why-is? if cli-reading-note exit then
  cli-layered? if cli-layered-note then ;
: cli-fed-unread ( outcome -- )
  ck-snap-bad? if drop cli-snap-error cli-window-note exit then
  ck-phase-failed ck-staging = 0= if cli-feed-error exit then
  dup cli-stage-error cli-stage-manifest? if cli-manifest-hint then ;

\ The resource report (--resources), after the summary and notes: each
\ phase's wall and CPU time in seconds, the run's total so far the last,
\ the peak resident memory and the stage's heap blocks, the input's size,
\ and the fuel used in all and by the declarations that used the most.
\ Times and memory differ from run to run; the rest does not.
\ Text right-aligned in a column of width characters.
\ Milliseconds as seconds with three decimals; microseconds in a column.
: do-seconds ( ms -- c-addr u ) 0 <# # # # [char] . hold #s #> ;
: cli-seconds ( ms -- c-addr u ) ['] do-seconds in-decimal ;
: cli-second. ( d-us -- ) 1000 um/mod nip cli-seconds 9 type-right ;
\ Phase k's row: its name, then its wall and CPU times.
: cli-row ( k -- )
  ."   " dup ck-phase-name 8 type-left
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
  ."   fuel: " ck-fuel-total ud>decimal type ."  steps in all, at most "
  ck-fuel-budget .decimal ."  per declaration" cr cli-unknown-fuel. ;
: cli-fuel-column ( n -- )
  ck-fuel-budget u>decimal nip >r u>decimal r> type-right ;
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
\ A pool the system made fewer worker tasks for than workers (near its
\ process limit; lib/task.fs): the workers took turns on those it made.
: cli-lacked. ( -- )
  ck-lacked 0= if exit then ."     worker tasks started: " ck-made .decimal
  ."  (the system refused " ck-lacked .decimal ."  more)" cr ;
: cli-jobs. ( -- )
  ck-parallel? 0= if exit then ck-jobs-run? 0= if cli-no-workers. exit then
  ."   workers: " ck-jobs .decimal ."  (--jobs), on " cli-cores .decimal ."  cores" cr
  cli-lacked. cli-sched. ;
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
\ The note before the lines a run writes as it goes, once.
: cli-noted ( -- ) cli-other-note true cli-state run-noted ! ;

\ The report: counted first, then printed, as text or as JSON
\ (cli/check-json.fs); a JSON text the writer refuses is an internal
\ fault, after the part already written.
\ A save that failed after a run that read its input; a run that read
\ nothing keeps the read's status (and says the snapshot was not written:
\ the record's save outcome is invalid until a save, review rvSN4 m2).
: cli-save-failed? ( -- flag ) cli-save? ck-snap-saved@ ok? 0= and ck-loaded? and ;
: cli-fed-tally ( -- )
  ck-loaded? if cli-tally-run else ck-read-outcome outcome>code cli-code! then
  cli-save-failed? if ck-snap-saved@ outcome>code cli-code! then ;
\ A snapshot written (--save-snapshot), or why not; a snapshot read
\ (--snapshot): its file, identity and versions, the export it was
\ written from, how many results it gave, and the note that saved
\ results support no claim (ADR 0020 D4).
create cli-hex 64 allot
: cli-sha. ( c-addr -- ) cli-hex sha256-hex cli-hex 64 type ;
\ A layer after an export checked against an older snapshot: the way on.
: cli-upgrade-note ( -- )
  ck-carry-import? 0= if exit then
  ." note: no layer is written on a snapshot of an older verdict version yet (plan" cr
  ." note: step 6.2.5c7): upgrade it first, check --snapshot OLD --save-snapshot NEW" cr ;
: cli-saved. ( -- )
  cli-save? 0= if exit then
  ck-snap-saved@ ?dup if ." error: the snapshot was not written: " outcome-text type cr
    cli-upgrade-note
  else ." snapshot: written to " cli-state opt-save 2@ nt-text if type else cli-unshown
  then cr
  then ;
\ Whether a text is plain: letters, digits, ".", "-", "_", " " only (no
\ character odd, outside those ranges).
create cli-plain-chars
  char a , char z ,  char A , char Z ,  char 0 , char 9 ,
  char . , char . ,  char - , char - ,  char _ , char _ ,  bl , bl ,
here cli-plain-chars - 2 cells / constant cli-plain-chars#
: cli-odd? ( char -- flag ) cli-plain-chars cli-plain-chars# in-ranges? 0= ;
: cli-plain? ( c-addr u -- flag ) ['] cli-odd? text-any? 0= ;
\ The commit the snapshot's information names, or "unknown", also for a
\ text that is not plain (a line feed in it could forge a report line;
\ review rvSN3 m1).
: cli-commit-key ( -- c-addr u ) s\" \"commit\":\"" ;
: cli-quote-at ( c-addr u -- n ) tuck [char] " byte-scan nip - ;
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
  ." import: " ck-checked# .decimal ."  checked in this run; "
  ck-other# .decimal ."  with the name of a declaration of the snapshot, not its content"
  cr ;
\ Each layer loaded on it (review rvSN4 M1): its file, identity, export.
: cli-layer-sums. ( k -- )
  ."  (sha256 " ck-layer-id dup ck-lid-sum cli-sha.
  ." ), export sha256 " ck-lid-export cli-sha. ;
: cli-layer. ( k -- )
  ." layer: " dup ck-layer@ nt-text if type else cli-unshown then
  dup cli-layer-sums. ." , verdict version " dup ck-layer-verdict .decimal
  ck-layer-stale? if ."  (stale)" then ." , on the snapshot above" cr ;
: cli-layers. ( -- ) ck-layers# 0 ?do i cli-layer. loop ;
: cli-stale. ( -- )
  ck-stale? 0= if exit then
  ." stale: --snapshot-stale-ok loaded a snapshot of an older verdict version than this" cr
  ." stale: build's (" lf-verdict-version .decimal ." ): its "
  ck-stale# .decimal ."  results are not this build's verdicts" cr ;
\ A carry run (plan step 6.2.5c3): the declarations checked again, by why
\ (env-import.fs why-*), each group after the first after a comma.
: cli-again# ( -- n ) 0 lf-input-count 0 ?do i ck-reason 0<> - loop ;
: cli-reach-group ( first? k -- first? )
  dup step-why ck-again# ?dup 0= if drop exit then cli-comma-under
  .decimal ."  inside the reach of verdict version " .decimal ." 's change" false ;
: cli-outcome-group ( first? -- first? )
  why-outcome ck-again# ?dup if
    cli-comma .decimal ."  whose saved outcome is never carried" false then ;
: cli-answers-group ( first? -- first? )
  why-answers ck-again# ?dup if
    cli-comma .decimal ."  whose lookups reach a result checked again" false then ;
: cli-groups ( -- )
  true lf-verdict-version 1+ ck-snap snap-verdict 1+ ?do i cli-reach-group loop
  cli-outcome-group cli-answers-group drop ;
: cli-again. ( -- )
  cli-again# dup .decimal ck-stale? if ."  shown stale, not checked again" then
  if ."  (" cli-groups ." )" then ;
\ Printed after the carry pass, before any check (the owner, 2026-11-12:
\ the count of re-checks first): text only.
\ Before the checks, a declaration whose lookups reach a result checked
\ again may still be carried on its turn (plan step 6.2.5c4).
: cli-at-most. ( -- ) why-answers ck-again# if ." at most " then ;
: cli-carry. ( -- )
  ." carry: a snapshot of verdict version " ck-snap snap-verdict .decimal
  ." , this build's " lf-verdict-version .decimal ." : " ck-carried# .decimal
  ."  results carried; to check again: " cli-at-most. cli-again. cr ;
: cli-taken. ( -- )
  ck-carrying? if ck-carried# .decimal ."  results carried from it" exit then
  ck-saved# .decimal ."  results taken from it"
  ck-layers# if ."  and its layers" then ;
: cli-version. ( -- )
  ." , verdict version " ck-snap snap-verdict .decimal
  ck-snap snap-stale @ if ."  (stale)" then
  ck-carrying? if ."  (this build: " lf-verdict-version .decimal ." )" then ;
: cli-carried. ( -- )
  ck-carrying? 0= if exit then
  ." carried: this build's changes since that verdict version cannot affect them" cr
  ." checked again: " cli-again. cr ;
: cli-snapshot. ( -- )
  ." snapshot: " cli-state opt-snapshot 2@ nt-text if type else cli-unshown then
  ."  (sha256 " ck-snap snap-sum cli-sha. ." ), export sha256 " ck-snap snap-export-sha
  cli-sha. cli-version. ." , written by LeanForth " cli-written-by type ." : " cli-taken.
  ." , not re-checked in this run" cr cli-carried. cli-layers. cli-stale. cli-import.
  ." note: development and research mode: a final run re-checks everything from the" cr
  ." note: export and reads no snapshot; only its results support a claim" cr ;
: cli-fed-text ( -- )
  cli-state run-noted @ 0= if cli-other-note then
  ck-loaded? if cli-results. else ck-read-outcome cli-fed-unread then
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
\ digits, ".", "-", "_", " ") and 1 to 128 bytes long, else null (review
\ R2 of 2026-11-18: a long text no longer drops parts of the JSON).
\ Written by lib/json-write.fs into a cell-counted buffer (lib/bounds.fs)
\ that holds the longest such text (six members, four texts of 128 bytes),
\ so the writer's limit is never reached; one record, set up while loading,
\ used by the main task only.
1024 constant cli-info-room
begin-structure /cli-info
  1 0 jw-size +field cli-info-writer
  field: cli-info-count          \ the text: its length, then its bytes
  cli-info-room +field cli-info-bytes
end-structure
create cli-info /cli-info allot
: cli-iw ( -- writer ) cli-info cli-info-writer ;
1 0 cli-iw jw-init 0= [if] .( leanforth.fs: the information writer) cr abort [then]
cli-info-room cli-iw jw-limit !
: cli-info-sink ( c-addr u -- ) cli-info cli-info-count cli-info-room cell-counted+? drop ;
: cli-info-plain? ( c-addr u -- flag ) dup 1 129 within >r cli-plain? r> and ;
: cli-info-text ( c-addr u -- )
  2dup cli-info-plain? if cli-iw jw-string else 2drop cli-iw jw-null then ;
: cli-info-key ( c-addr u -- ) cli-iw jw-key ;
: cli-info-host ( -- c-addr u ) [defined] version-string [if] version-string [else] 0 0
  [then] ;
: cli-info-members ( -- )
  s" leanforth" cli-info-key cli-version-text cli-info-text
  s" commit" cli-info-key s" LEANFORTH_COMMIT" cli-env cli-info-text
  s" modified" cli-info-key cli-modified? cli-iw jw-bool
  s" gforth" cli-info-key cli-info-host cli-info-text
  s" engine" cli-info-key ck-engine cli-info-text
  s" cellBits" cli-info-key cell-bits cli-iw jw-u ;
\ The text; "{}" if the writer refused it, which the sizes above exclude.
: cli-info-build ( -- c-addr u )
  0 cli-info cli-info-count ! ['] cli-info-sink cli-iw jw-start
  cli-iw jw-open-object cli-info-members cli-iw jw-close-object
  cli-iw jw-end ok? if cli-info cli-info-count cell-count else s" {}" then ;
: cli-snapshot-save ( -- )
  cli-save? 0= if exit then cli-state opt-save 2@ cli-info-build ck-snapshot-save drop ;
\ The text report's lines are written as the run goes (JSON is one text).
: cli-streaming ( -- ) cli-json? if exit then cli-noted ['] cli-stream ck-lines! ;
: cli-library-run ( -- )
  0 cli-file cli-checked? ck-load ok? if cli-streaming ck-check cli-snapshot-save then
  cli-fed-tally cli-fed-report ;
\ check --snapshot FILE: the snapshot's verdicts, published again from it
\ (cli/check-run.fs ck-snapshot-load), no export read; each further
\ --snapshot LAYER a layer loaded on it (kernel/env-layers.fs). With
\ --save-snapshot NEW (no layer), FILE written again as a base of this
\ build's versions (plan step 6.2.5c5): an older one upgraded. The text
\ report's first line in a carry run is cli-carry. (plan step 6.2.5c3).
: cli-layers ( -- ) cli-state opt-layers @ cli-state opt-layers# @ ck-layers! ;
: cli-carry-first ( -- ) cli-json? 0= if ['] cli-carry. ck-carried! then ;
: cli-snapshot-run ( -- )
  cli-layers cli-carry-first cli-state opt-snapshot 2@ cli-asked-fuel
  ck-snapshot-load
  ok? if ck-check cli-snapshot-save then
  cli-fed-tally cli-fed-report ;
\ check --snapshot FILE EXPORT: the export read on into the snapshot's
\ tier, what is the snapshot's taken from it, the rest checked (plan step
\ SN4; cli/check-run.fs ck-snapshot-import, kernel/env-import.fs); with
\ --save-snapshot, what was checked written as a layer of the snapshot.
: cli-import-run ( -- )
  cli-layers cli-carry-first cli-state opt-snapshot 2@ cli-asked-fuel
  ck-snapshot-import ok?
  if 0 cli-file cli-checked? ck-load ok? if ck-check cli-snapshot-save then then
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
  cli-fed-ops cli-state run-ops ! 0 cli-state run-printed ! 0 cli-state run-noted !
  rr-release rr-reset cli-fuel @ ck-start
  cli-stale? snap-stale-allowed !
  cli-any-lean? ck-any-version! cli-jobs ck-jobs! cli-progress-apply cli-per-check-apply
  catch ck-release throw cli-restored
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
: cli-checks ( -- code )
  cli-recorded-ops cli-state run-ops ! cli-unchecked-note cli-settings
  cli-recording? if cli-run cli-recorded then rr-release cli-worst @ ;
\ --record keeps the run of small exports, whose record has no resource
\ report: --json and --resources do not go with it (a mistake, code 4).
: cli-misused? ( -- flag ) cli-record? cli-json? cli-resources? or and ;
: cli-misuse-record ( -- code )
  ." error: --json and --resources do not go with --record" cr
  ." try: leanforth help" cr exit-malformed ;
\ Run records 0.3 hold the pinned versions only: --any-lean-version does
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
\ Nor does --memory-per-check: a run record does not hold it.
: cli-per-check-misused? ( -- flag ) cli-record? cli-per-check 0<> and ;
: cli-misuse-per-check ( -- code )
  ." error: --memory-per-check does not go with --record" cr
  ." try: leanforth help" cr exit-malformed ;
: cli-progress-misused? ( -- flag ) cli-record? cli-progress? and ;
: cli-misuse-progress ( -- code )
  ." error: --progress does not go with --record" cr
  ." try: leanforth help" cr exit-malformed ;
\ Snapshots (ADR 0020 D6): neither --snapshot nor --save-snapshot goes
\ with --record; both together write a layer, so only with an export.
: cli-snap-misused? ( -- flag ) cli-record? cli-snapshot? cli-save? or and ;
\ Without an export they write the snapshot again with this build's
\ versions (plan step 6.2.5c5), of one snapshot: not with layers.
: cli-snap-both? ( -- flag )
  cli-snapshot? cli-save? and cli-files @ 0= and cli-state opt-layers# @ 0<> and ;
: cli-misuse-snap ( c-addr u -- code )
  ." error: " type cr ." try: leanforth help" cr exit-malformed ;
\ --snapshot-stale-ok reads a snapshot; a stale verdict is never written
\ into another (ADR 0020 amendment 3).
: cli-stale-misuse ( -- code|0 )
  cli-stale? 0= if 0 exit then
  cli-snapshot? 0= if s" --snapshot-stale-ok needs --snapshot" cli-misuse-snap exit then
  cli-save? if s" --snapshot-stale-ok does not go with --save-snapshot" cli-misuse-snap
    exit then 0 ;
: cli-snap-misuse ( -- code|0 )
  cli-snap-misused? if s" --snapshot and --save-snapshot do not go with --record"
    cli-misuse-snap exit then
  cli-snap-both? if
  s" --save-snapshot without an export writes one snapshot again, not its layers"
    cli-misuse-snap exit then
  cli-save? cli-state opt-layers# @ 0<> and
  if s" --save-snapshot writes a layer on one snapshot only" cli-misuse-snap exit then
  cli-stale-misuse ;
: cli-wrong ( c-addr u why -- )
  cli-state arg-mistake @ if drop 2drop exit then
  cli-state arg-mistake ! cli-state arg-culprit 2! ;
: cli-mistake? ( -- flag ) cli-state arg-mistake @ 0<> ;
\ Every argument read is kept by its address, in order, the command 0:
\ its index names it in bin/leanforth's list of arguments that are one
\ file (cli-same-file?).
: cli-seen ( -- addr n ) cli-state arg-seen @ cli-state arg-seen# @ ;
: cli-seen-room ( -- outcome )
  cli-state arg-seen# @ 1+ cells cli-state arg-seen block-resize ;
: cli-seen-full ( c-addr u -- c-addr u ) 2dup c" no room for the arguments" cli-wrong ;
: cli-seen+ ( c-addr u -- c-addr u )
  cli-seen-room ok? 0= if cli-seen-full exit then
  over cli-seen cells + ! 1 cli-state arg-seen# +! ;


\ check [--env EXPORT | --snapshot FILE] FILE.lf (plan tasks 8.2.1c-d;
\ cli/check-lf.fs): a LeanForth text run by the LeanForth words, its
\ declarations staged after the library's -- an export's, or a snapshot's
\ as check --snapshot FILE EXPORT loads it, its declarations then taken
\ from it by the import pass -- and checked as an export's, the report
\ check's own. A text that stops with an error is not checked at all: the
\ error is printed at its line and column, with its outcome's code (4 a
\ mistake, 2 a form not supported yet, 3 no room). Neither a run record,
\ a written snapshot nor JSON goes with a text yet; --env goes only with
\ one, and not with --snapshot. --elab-data FILE (plan row FE1d) goes only
\ with a text and its library: the library's elaboration data, read and
\ checked before the text runs (cli/check-lf.fs); refused, nothing runs.
: cli-text-file? ( -- flag )
  0 cli-file dup 3 < if 2drop false exit then + 3 - 3 s" .lf" compare 0= ;
: cli-library-file ( -- c-addr u ) cli-state opt-env 2@ ;
: cli-elab-file ( -- c-addr u ) cli-state opt-elab 2@ ;
: cli-elab-error ( -- )
  ." error: " ck-read-outcome dup outcome-text type
  ." : the elaboration data was refused at line " elab-error-line .decimal
  ."  (error " elab-error-code .decimal ." ): " elab-error-why type
  ." ; the LeanForth text was not checked" cr outcome>code cli-code! ;
\ The elaboration data read, by kind, before the verdicts.
: cli-elab-count. ( kind -- ) elab-count .decimal ;
\ The kinds format 1 had, then the kinds formats 2 and 3 added.
: cli-elab-format1 ( -- )
  elab-instance cli-elab-count. ."  instances, " elab-default cli-elab-count.
  ."  default instances, " elab-reducibility cli-elab-count.
  ."  reducibility statuses, " elab-eliminator cli-elab-count. ."  eliminators" ;
: cli-elab-format2 ( -- )
  ." , " elab-left-out cli-elab-count. ."  instances left out, "
  elab-class cli-elab-count. ."  classes, " elab-tag cli-elab-count. ."  tags, "
  elab-matcher cli-elab-count. ."  matchers, " elab-projection cli-elab-count.
  ."  projections" ;
: cli-elab-format3 ( -- )
  ." , " elab-sunfold cli-elab-count. ."  smart-unfolding bodies" ;
: cli-elab-note ( -- )
  cli-elab-file nip 0= if exit then ." elaboration data: " cli-elab-format1
  cli-elab-format2 cli-elab-format3 cr ;
\ An error's outcome as the line names it: error 41's is none of the
\ vocabulary, an internal fault (exit 5, author/errors.fs lfa-internal).
: cli-author-outcome. ( outcome -- )
  dup outcome? if outcome-text type else drop ." internal fault" then ;
: cli-text-error ( -- )
  ." error: " lf-author-code lf-author-outcome dup cli-author-outcome.
  ." : the LeanForth text was not checked: " lf-author-error. cr outcome>code cli-code! ;
\ The text ran, but its records did not reach the stage whole (review L4):
\ the refusal's outcome, said of the text, never of an export line the
\ user cannot see.
: cli-records-error ( -- )
  ." error: " ck-read-outcome dup outcome-text type
  ." : the records written for the LeanForth text were refused; the text was not checked"
  cr outcome>code cli-code! ;
\ After the verdicts, in the text report, the open parts by-sorry left
\ (front/tactic-run.fs; ADR 0021 Amendment 1: the JSON report's fields
\ wait for the owner's [format] decision).
: cli-open-parts ( -- ) cli-json? 0= if lf-open-parts. then ;
\ A text of only #check lines (plan S1; front/elab-decl.fs): nothing for
\ the kernel to check, which a text with no declaration of its own is
\ told (error 49); as Lean, exit 0, the terms printed as the text ran.
: cli-checks-only? ( -- flag )
  lfc-failed? lf-author-code lfa-e-nothing = and lf-elab-checks 0> and ;
: cli-checks-only ( -- ) ." nothing checked by the kernel" cr ;
\ --steps FILE or --steps - (plan S2, s2-steps; docs/design/S2_INTERFACE.md
\ 6): the step log of the text's tactic proofs (front/step-log.fs), for
\ the declarations accepted, with each one's axioms and open parts,
\ written after the report to FILE or to standard output. It changes no
\ verdict and no exit code (a log that ran out of room while the text ran
\ is cut and says so); only a log that cannot be written is an error
\ (exit 3).
: cli-steps ( -- c-addr u ) cli-state opt-steps 2@ ;
: cli-steps? ( -- flag ) cli-steps nip 0<> ;
: cli-steps-fail ( -- ) true cli-state run-steps-bad ! ;
: cli-steps-bad ( outcome -- outcome' )
  cli-state run-steps-bad @ if drop outcome-full then ;
\ Accepted: the newest input declaration of that full name (the text's
\ come after the library's: pr-newest finds them first), accepted as the
\ kernel means it (tally.fs decl-accepted?, review PB2).
: cli-step-find ( c-addr u -- d true | false )
  pr-newest 0= if false exit then dup decl-accepted? dup 0= if nip then ;
: cli-step-axiom ( d -- )
  lf-input-name nt-name if cli-state run-steps-axiom @ execute exit then
  2drop cli-steps-fail ;
: cli-step-axioms ( d xt -- outcome )
  cli-state run-steps-axiom ! ['] cli-step-axiom lf-env-axiom-deps cli-steps-bad ;
\ A FILE whose writing failed ends at its last whole line, never in the
\ middle of one (review N14): nothing is written after the first failure,
\ and the file is cut back to the bytes through its last line feed, the
\ end of the last write that ended in one. The file holds no mark of its
\ own that it was cut (the step log's format, schema 1, has no record for
\ one): a header's step count followed by fewer step lines finds a cut
\ inside a declaration, but a cut between declarations looks whole, so
\ only the exit status shows that a log is complete (re-check S2). When
\ the cut itself fails (its
\ position, flush or resize, or the close), the error says the file may
\ end inside a line (review N3); the code is 3 either way.
: cli-steps-fid ( -- fid ) cli-state run-steps-fid @ ;
: cli-steps-uncut ( -- ) true cli-state run-steps-uncut ! ;
: cli-steps-whole! ( -- )
  cli-steps-fid file-position
  if 2drop cli-steps-uncut else cli-state run-steps-whole 2! then ;
: cli-line-end? ( c-addr u -- flag ) dup 0= if nip exit then + 1- 1 s\" \n" compare 0= ;
: cli-steps-mark ( c-addr u -- ) cli-line-end? if cli-steps-whole! then ;
: cli-steps-put ( c-addr u -- )
  cli-state run-steps-bad @ if 2drop exit then
  2dup cli-steps-fid write-file if 2drop cli-steps-fail else cli-steps-mark then ;
: cli-steps-cut ( outcome -- outcome )
  dup ok? if exit then cli-steps-fid flush-file
  cli-state run-steps-whole 2@ cli-steps-fid resize-file or if cli-steps-uncut then ;
: cli-steps-to ( sink -- outcome )
  ['] cli-step-find ['] cli-step-axioms lf-steps-write cli-steps-bad ;
: cli-steps-closed ( outcome -- outcome )
  cli-steps-fid close-file if drop cli-steps-uncut outcome-full then ;
: cli-steps-file ( -- outcome )
  cli-steps w/o create-file if drop outcome-full exit then cli-state run-steps-fid !
  0 0 cli-state run-steps-whole 2! ['] cli-steps-put cli-steps-to cli-steps-cut
  cli-steps-closed ;
: cli-stdout? ( -- flag ) cli-steps s" -" compare 0= ;
: cli-steps-out ( -- outcome )
  cli-stdout? if ['] type cli-steps-to else cli-steps-file then ;
\ What is left of a FILE: nothing when it could not be made.
: cli-steps-left. ( -- )
  cli-stdout? cli-steps-fid 0= or if exit then
  cli-state run-steps-uncut @ if ." ; it may end inside a line" exit then
  ." ; it ends at its last whole line" ;
: cli-steps-write ( -- )
  cli-steps? 0= if exit then cli-steps-out ok? if exit then
  ." error: the step log could not be written: " cli-steps type cli-steps-left. cr
  outcome-full outcome>code cli-code! ;
: cli-text-report ( -- )
  lfc-elab-failed? if cli-elab-error exit then
  cli-checks-only? if cli-checks-only exit then
  lfc-failed? if cli-text-error exit then lfc-refused? if cli-records-error exit then
  cli-fed-tally cli-fed-report cli-open-parts cli-steps-write ;
\ --jobs N with a text: no worker can share the run's input (the words'
\ run moved this context's stores on, see ck-workers-made), so the text
\ is checked one declaration at a time, and a note says so first.
: cli-serial-text ( -- c-addr )
  c" --jobs does not apply to LeanForth text yet; checking one declaration at a time" ;
: cli-text-jobs-note ( -- ) cli-jobs 1 > if cli-serial-text cli-note then ;
: cli-text-lines ( -- )
  cli-json? if exit then cli-text-jobs-note true cli-state run-noted !
  ['] cli-stream ck-lines! ;
: cli-text-load ( -- outcome )
  cli-library-file lfc-env! cli-elab-file lfc-elab-file!
  0 cli-file cli-checked? ck-lf-load ;
: cli-text-loaded ( -- outcome )
  cli-snapshot? 0= if cli-text-load exit then
  cli-layers cli-state opt-snapshot 2@ cli-asked-fuel ck-snapshot-import
  dup ok? if drop cli-text-load then ;
: cli-elab-fuel-set ( -- )
  cli-state opt-elab-fuel-given @ if cli-state opt-elab-fuel @ else lf-meta-default-budget
  then lf-elab-fuel! ;
: cli-text-run ( -- )
  cli-steps? lf-steps-record! cli-elab-fuel-set
  lfc-fresh cli-text-loaded ok? if cli-elab-note cli-text-lines ck-check
  then cli-text-report ;
: cli-text-misused? ( -- flag )
  cli-record? cli-save? or cli-json? or cli-snapshot? cli-library-file nip 0<> and or ;
: cli-text-misuse ( -- code )
  s" --record, --save-snapshot, --json and --env with --snapshot: not with a text"
  cli-misuse-snap ;
: cli-env-opens? ( -- flag )
  cli-library-file dup 0= if 2drop true exit then
  r/o bin open-file if drop false else close-file drop true then ;
\ --elab-data needs a library, and not a layered snapshot yet: the hash
\ checked would be the base's, the names the layers' too (review fe1d L1).
: cli-elab? ( -- flag ) cli-elab-file nip 0<> ;
: cli-elab-alone? ( -- flag ) cli-elab? cli-library-file nip 0= cli-snapshot? 0= and and ;
: cli-elab-alone ( -- code )
  s" --elab-data needs --env or --snapshot, the library it describes" cli-misuse-snap ;
: cli-elab-layered? ( -- flag ) cli-elab? cli-state opt-layers# @ 0<> and ;
: cli-elab-layers ( -- code )
  s" --elab-data does not go with a layered snapshot yet" cli-misuse-snap ;
: cli-elab-misuse ( -- code | 0 )
  cli-elab-alone? if cli-elab-alone exit then
  cli-elab-layered? if cli-elab-layers exit then 0 ;
: cli-steps-misplaced? ( -- code true | false )
  cli-steps? 0= if false exit then
  s" --steps goes only with a LeanForth text (FILE.lf)" cli-misuse-snap true ;
: cli-elab-fuel-misplaced? ( -- code true | false )
  cli-state opt-elab-fuel-given @ 0= if cli-steps-misplaced? exit then
  s" --elab-fuel goes only with a LeanForth text (FILE.lf)" cli-misuse-snap true ;
: cli-elab-misplaced? ( -- code true | false )
  cli-state opt-elab @ 0= if cli-elab-fuel-misplaced? exit then
  s" --elab-data goes only with a LeanForth text (FILE.lf)" cli-misuse-snap true ;
: cli-text-refused ( -- code | 0 )
  cli-text-misused? if cli-text-misuse exit then
  cli-elab-misuse ?dup if exit then cli-snap-misuse ;
: cli-text-command ( -- code )
  cli-text-refused ?dup if exit then
  cli-opens? 0= if ." error: cannot open the LeanForth text" cr exit-malformed exit then
  cli-env-opens? 0= if cli-unopened exit then
  cli-library-file nip if cli-unchecked-note then ['] cli-text-run cli-fed-run ;
: cli-text? ( -- code true | false )
  cli-text-file? if cli-text-command true exit then
  cli-elab-misplaced? if true exit then
  cli-state opt-env @ 0= if false exit then
  s" --env goes only with a LeanForth text (FILE.lf)" cli-misuse-snap true ;
\ With an export (it must open), the export checked against the snapshot.
: cli-snapshot-check ( -- code )
  cli-files @ 0= if ['] cli-snapshot-run cli-fed-run exit then
  cli-opens? 0= if cli-not-opened exit then ['] cli-import-run cli-fed-run ;
\ No file a command writes may be one it reads or another it writes,
\ checked before anything runs (exit 4): RECORD (--record), FILE
\ (--save-snapshot), STEPS (--steps, not -) and reexport's COPY against
\ EXPORT or FILE.lf, --env, --elab-data, every --snapshot, and the
\ manifests of EXPORT and of --env, which the command reads beside them
\ ("<export>.manifest.json", import/manifest.fs; listed even under
\ --no-manifest). Two names are one file when they are the same text, or
\ when bin/leanforth found them one file by device and inode (test -ef,
\ through symbolic links and relative names): it lists those arguments in
\ LEANFORTH_SAME_FILES as " I:J " pairs of their indices (cli-seen),
\ I < J, as " Im:J " when argument I's manifest is argument J, and as
\ " Ip:J " when I.partial (--save-snapshot I writes it first) is.
begin-structure /cli-path
  2 cells +field path-text      \ the file's name, as given
  field: path-label             \ counted string: what the messages call it
  field: path-out?              \ true: the command writes it
  field: path-derived           \ 0, or ( -- c-addr u ): the file is path-text + suffix
end-structure
: cli-arg-index ( c-addr -- i true | false ) cli-seen cells-index ;
: cli-hold# ( n -- ) s>d #s 2drop ;
: cli-pair-to ( i j -- i ) <# bl hold cli-hold# [char] : hold ;
: cli-pair-from ( i -- c-addr u ) s>d #s bl hold #> ;
: cli-pair-text ( i j -- c-addr u ) cli-pair-to cli-pair-from ;
: cli-dpair-text ( i char j -- c-addr u ) cli-pair-to hold cli-pair-from ;
: cli-pair ( i j -- c-addr u ) ['] cli-pair-text in-decimal ;
: cli-dpair ( i char j -- c-addr u ) ['] cli-dpair-text in-decimal ;
: cli-same-files ( -- c-addr u ) s" LEANFORTH_SAME_FILES" cli-env ;
: cli-listed? ( c-addr u -- flag ) cli-same-files 2swap search nip nip ;
: cli-same-pair? ( i j -- flag ) 2dup > if swap then cli-pair cli-listed? ;
: cli-path ( i -- addr ) /cli-path * cli-state arg-paths @ + ;
: cli-texts ( a b -- c-addr1 u1 c-addr2 u2 ) swap path-text 2@ rot path-text 2@ ;
\ A derived path d (an export's manifest, a snapshot's FILE.partial) is
\ the file named by its text, the stem, then its suffix; its letter in
\ the pairs is m or p.
: cli-derived? ( path -- flag ) path-derived @ 0<> ;
: cli-suffix ( d -- c-addr u ) path-derived @ execute ;
: cli-manifest? ( d -- flag ) path-derived @ ['] manifest-suffix = ;
: cli-mark ( d -- char ) cli-manifest? if [char] m else [char] p then ;
: cli-path-addr ( path -- c-addr ) path-text 2@ drop ;
: cli-name# ( d -- u ) dup path-text @ swap cli-suffix nip + ;
\ Plain path p's text is derived path d's name: as long, d's stem first,
\ d's suffix last (the last two read p's text only when it is as long).
: cli-length-of? ( d p -- flag ) path-text @ swap cli-name# = ;
: cli-stem-of? ( d p -- flag ) cli-path-addr swap path-text 2@ tuck compare 0= ;
: cli-suffix-of? ( d p -- flag )
  cli-path-addr over path-text @ + swap cli-suffix tuck compare 0= ;
: cli-derived-text? ( d p -- flag )
  2dup cli-length-of? 0= if 2drop false exit then
  2dup cli-stem-of? if cli-suffix-of? else 2drop false then ;
\ How many of paths a and b are derived, negated (true is -1).
: cli-manifests ( a b -- n ) cli-derived? swap cli-derived? + ;
\ Two derived paths: the same suffix of the same stem.
: cli-both-text? ( a b -- flag )
  2dup path-derived @ swap path-derived @ <> if 2drop false exit then
  cli-texts compare 0= ;
\ Paths a and b name one text (the derived one first, when only one is).
: cli-manifest-first ( a b -- a' b' ) dup cli-derived? if swap then ;
: cli-same-text? ( a b -- flag )
  2dup cli-manifests dup 0= if drop cli-texts compare 0= exit then
  -1 = if cli-manifest-first cli-derived-text? else cli-both-text? then ;
: cli-path-index ( path -- i true | false ) cli-path-addr cli-arg-index ;
: cli-indices ( a b -- i j true | false )
  cli-path-index if swap cli-path-index if swap true exit then then drop false ;
\ Argument i, or the derived file d of argument i, and argument j are
\ one file. Two derived files are compared by text alone: two manifests
\ are only read (cli-clash?), and FILE.partial is no manifest's name.
: cli-plain-place? ( a b -- flag ) cli-indices dup if drop cli-same-pair? then ;
: cli-marked ( i j d -- i char j ) cli-mark swap ;
: cli-manifest-place? ( d b -- flag )
  over swap cli-indices if rot cli-marked cli-dpair cli-listed? else drop false then ;
: cli-same-place? ( a b -- flag )
  cli-manifest-first over cli-derived? if cli-manifest-place? else cli-plain-place? then ;
: cli-same-file? ( a b -- flag )
  2dup cli-same-text? if 2drop true else cli-same-place? then ;
: cli-written? ( a b -- flag ) path-out? @ swap path-out? @ or ;
\ Paths a and b clash when either is written and they are one file.
: cli-clash? ( a b -- flag ) 2dup cli-written? if cli-same-file? else 2drop false then ;
: cli-paths-room ( -- outcome )
  cli-state arg-paths# @ 1+ /cli-path * cli-state arg-paths block-resize ;
: cli-path! ( c-addr u label out? addr -- )
  dup /cli-path erase tuck path-out? ! tuck path-label ! path-text 2! ;
: cli-path+ ( c-addr u label out? -- )   \ THROW -59 when there is no room
  cli-paths-room ok? 0= if -59 throw then
  cli-state arg-paths# @ cli-path cli-path! 1 cli-state arg-paths# +! ;
: cli-in+ ( c-addr u label -- ) over if false cli-path+ else drop 2drop then ;
: cli-out+ ( c-addr u label -- ) over if true cli-path+ else drop 2drop then ;
: cli-layer-in ( i -- )
  2* cells cli-state opt-layers @ + 2@ c" the snapshot read" cli-in+ ;
: cli-layers-in ( -- ) cli-state opt-layers# @ 0 ?do i cli-layer-in loop ;
\ An export's manifest, read with it, and the snapshot's FILE.partial,
\ written first (lib/sections.fs): the stem's name, derived.
: cli-last-path ( -- addr ) cli-state arg-paths# @ 1- cli-path ;
: cli-derive ( xt -- ) cli-last-path path-derived ! ;
: cli-manifest-in ( c-addr u label -- )
  over 0= if drop 2drop exit then cli-in+ ['] manifest-suffix cli-derive ;
: cli-partial-out ( -- )
  cli-save? 0= if exit then
  cli-state opt-save 2@ c" FILE.partial" cli-out+ ['] sections-suffix cli-derive ;
: cli-steps-out+ ( -- )
  cli-steps 2dup s" -" compare if c" STEPS" cli-out+ else 2drop then ;
\ The file names, set by the command line or by cli-check (cli-files
\ counts only those of the command line).
: cli-first-in ( -- )
  0 cli-file cli-text-file? if c" FILE.lf" cli-in+ exit then
  2dup c" EXPORT" cli-in+ c" EXPORT's manifest" cli-manifest-in ;
: cli-env-in ( -- )
  cli-library-file 2dup c" the --env export" cli-in+
  c" the --env export's manifest" cli-manifest-in ;
\ The command's second file, when it writes one (reexport's COPY).
: cli-copy-out+ ( copy? -- ) if 1 cli-file c" COPY" cli-out+ then ;
: cli-inputs ( -- )
  cli-first-in cli-env-in cli-elab-file c" the --elab-data file" cli-in+
  cli-state opt-snapshot 2@ c" the snapshot read" cli-in+ cli-layers-in ;
: cli-outputs ( copy? -- )
  cli-copy-out+ cli-record 2@ c" RECORD" cli-out+
  cli-state opt-save 2@ c" FILE" cli-out+ cli-partial-out cli-steps-out+ ;
: cli-paths ( copy? -- ) 0 cli-state arg-paths# ! cli-inputs cli-outputs ;
: cli-clash-in ( i -- j true | false )
  cli-state arg-paths# @ over 1+ ?do
    dup cli-path i cli-path cli-clash? if drop i true unloop exit then loop drop false ;
: cli-clash ( -- i j true | false )
  cli-state arg-paths# @ 0 ?do i cli-clash-in if i swap true unloop exit then loop false ;
: cli-label. ( path -- ) path-label @ count type ;
: cli-clash. ( i j -- )   \ the later one first when it is written
  cli-path swap cli-path swap dup path-out? @ 0= if swap then
  ." error: " cli-label. ."  must not be " cli-label. cr ;
\ 0, or 4 after the message when a written file is read or written twice;
\ copy?: the command's second file is one it writes. Each command that
\ writes a file runs it first.
: cli-clashing ( copy? -- code|0 )
  cli-paths cli-clash if cli-clash. exit-malformed else 0 then ;
: check-command ( -- code )
  cli-start false cli-clashing ?dup if exit then
  cli-strict? cli-strict-axioms! cli-misused? if cli-misuse-record exit then
  cli-text? if exit then cli-any-misused? if cli-misuse-any exit then
  cli-jobs-misused? if cli-misuse-jobs exit then
  cli-per-check-misused? if cli-misuse-per-check exit then
  cli-progress-misused? if cli-misuse-progress exit then
  cli-snap-misuse ?dup if exit then
  cli-snapshot? if cli-snapshot-check exit then
  cli-opens? 0= if cli-not-opened exit then
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
\ (present/proof-outline.fs: the verdict with its axioms, the
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
  cli-state opt-kernel @ 0= lf-print-notation!
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
  cli-fuel @ lf-file-write if exit-undecided cli-code! then ;
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
  dup >r ['] cli-copy catch r> closed swap throw outcome-and ;
: cli-create ( -- fid true | false )
  1 cli-file w/o bin create-file 0= dup 0= if nip then ;
: cli-uncreated ( -- code ) ." error: cannot create the copy" cr exit-malformed ;
: cli-copied ( fid -- code )
  0 cli-file rot cli-into dup reexport-report reexport-free cli-manifest manifest-free
  outcome>code ;
: cli-reexported ( -- code ) cli-create if cli-copied else cli-uncreated then ;
: reexport-command ( -- code )
  true cli-clashing ?dup if exit then
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
  ." leanforth " cli-version-text type cr
  ." forth: " cli-host. cr cli-reads. exit-accepted ;
: cli-check-input. ( -- )
  ."   check: Lean 4.35.0 exports (lean4export 3.1.0 NDJSON) of any size, such as" cr
  ."     all of Lean's Init, staged and fed in Forth; the manifest checked unless" cr
  ."     --no-manifest; a summary, --resources (time, memory, fuel), --json;" cr
  ."     gforth-fast, or Gforth's checking engine with --checked; --jobs N checks" cr
  ."     with N workers (threads on Gforth 1.0), the same output as one" cr ;
: cli-check-rules. ( -- )
  ."   check: Lean's kernel rules as built so far: definitions, theorems, opaque" cr
  ."     declarations and axioms (an axiom outside Lean's standard three is NOT" cr
  ."     PROVED, as Lean's exit status 0); fun, forall, application, let," cr
  ."     number and string literals, projections, unfolding of definitions;" cr
  ."     proof irrelevance and eta; quotients; inductive types, recursive," cr
  ."     indexed and mutual ones, with their recursors; unsafe and partial" cr
  ."     declarations skipped, as Lean's replay skips them (5.2.7); several of" cr
  ."     these are merged but their review gates are open" cr
  ."     (docs/project/PROJECT_PROGRESS.md)" cr ;
: cli-text-check. ( -- )
  ."   check [--env EXPORT | --snapshot FILE] FILE.lf: a LeanForth text, its" cr
  ."     declarations built by LeanForth's words and checked as an export's" cr
  ."     (plan tasks 8.2.1c-d), one at a time (--jobs does not apply yet); not" cr
  ."     with --json, --record or --save-snapshot" cr ;
: cli-other-commands. ( -- )
  ."   check --record, replay: run records 0.3 and their replay (plan task 2.2.5)" cr
  ."   print: a readable proof outline of each accepted declaration, from the" cr
  ."     checker's derivation log (plan tasks 2.4.1, 2.4.4; untrusted presentation)" cr
  ."   count, reexport: exports of any size, up to all of Mathlib" cr ;
\ verify is bin/leanforth's: it starts scripts/program_verify.py, which needs
\ Python 3 and the pinned Lean (the owner's V1 decision of 2026-11-13).
: cli-verify-what. ( -- )
  ."   verify: one Forth word against its contract (plan 8.4.1, V1): pinned Lean" cr
  ."     writes the proofs, this checker re-checks them, a receipt records it;" cr ;
: cli-verify-needs. ( -- )
  ."     needs Python 3 and the pinned Lean 4.35.0 (owner, 2026-11-13: V1 only)" cr ;
: cli-checks. ( -- )
  ." supported:" cr cli-check-input. cli-check-rules. cli-text-check.
  cli-other-commands. cli-verify-what. cli-verify-needs. ;
: cli-lacks. ( -- )
  ." not yet supported (check answers unsupported or unknown, exit 2):" cr
  ."   a block with both safe and unsafe members (5.2.7 part b)," cr
  ."   metadata (mdata) in a term (4.1.3);" cr
  ."   recursor reductions on a variable (a follow-up of 5.2.2)," cr
  ."   so a correct proof can still end unknown;" cr
  ."   check --record and replay (the old reader) refuse inductive types, and" cr
  ."   answer unsupported for let, literals, projections and metadata;" cr ;
\ No measured claim: a count from another build says nothing of this one
\ (review N5); the dated runs are recorded in the progress document.
: cli-mathlib. ( -- )
  ." Mathlib: this build makes no claim; the dated runs on all of Mathlib and" cr
  ."   their builds are in docs/project/PROJECT_PROGRESS.md" cr ;
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
  cli-fuel-most u>decimal type ." )" cr
  ."   memory per check: none but the heap's (--memory-per-check MB)" cr ;
: cli-planned. ( -- )
  ." planned, not built: program, serve and --record on any size," cr
  ."   every axiom name of each accepted declaration, as #print axioms" cr
  ."     (plan task 5.3.2; today: the allowlist's names and NOT PROVED's)" cr ;
: capabilities-command ( -- code )
  ." leanforth " cli-version-text type ." : what this build can do" cr
  cli-checks. cli-mathlib. cli-lacks. cli-limits. cli-planned. exit-accepted ;

\ ---------------------------------------------------------------------------
\ help, one part per kind of command.
: cli-check-usage. ( -- )
  ."   check [--no-manifest] [--fuel N] [--resources] [--json] [--fast]" cr
  ."         [--strict-axioms] [--any-lean-version] [--jobs N] [--progress[=SECONDS]]" cr
  ."         [--memory-per-check MB] [--save-snapshot FILE] EXPORT" cr
  ."       check every declaration of a Lean export, in file order, any size;" cr
  ."       --jobs N checks with N workers at once (default 1), same output;" cr
  ."       --memory-per-check MB makes a check whose scratch passes MB full;" cr
  ."       --progress writes a status line to stderr every SECONDS (default 60);" cr
  ."       the text report's lines are written as declarations are final;" cr
  ."       --resources adds time, memory and fuel, --json prints it all as JSON;" cr
  ."       --strict-axioms makes a NOT PROVED declaration exit 6;" cr
  ."       --any-lean-version (check, print) reads an export of another Lean or" cr
  ."       exporter version in format 3.1.0, its verdicts still Lean 4.35.0's;" cr
  ."       --save-snapshot FILE writes the checked environment to FILE" cr
  ."   check --snapshot FILE [--fuel N] [--resources] [--json] [--fast]" cr
  ."         [--no-manifest] [--jobs N] [--snapshot LAYER]... [--snapshot-stale-ok]" cr
  ."         [EXPORT]" cr
  ."       the verdicts a snapshot holds, labelled, not re-checked (development" cr
  ."       and research only: a final run re-checks the export); with EXPORT," cr
  ."       its declarations the snapshot holds unchanged taken from it, the rest" cr
  ."       checked (with --save-snapshot LAYER, written as a layer of FILE;" cr
  ."       without EXPORT, --save-snapshot NEW writes FILE again, upgraded);" cr
  ."       of one of the two verdict versions before this build's, what this" cr
  ."       build's changes can reach is checked again, the rest carried;" cr
  ."       --snapshot-stale-ok shows instead what is not carried, or every" cr
  ."       result of an older one, labelled stale, never this build's verdict" cr
  ."   check [--no-manifest] [--fuel N] [--fast] [--strict-axioms]" cr
  ."         --record RECORD EXPORT" cr
  ."       the same for a small export, and write its run record to RECORD" cr
  ."   check [--env EXPORT | --snapshot FILE] [--fuel N] [--resources] [--jobs N]" cr
  ."         [--strict-axioms] [--no-manifest] [--memory-per-check MB]" cr
  ."         [--elab-data DATA] [--elab-fuel N] [--steps FILE|-] FILE.lf" cr
  ."       check a LeanForth text, against Lean's library EXPORT or a snapshot" cr
  ."       FILE of one: its declarations built by the words, checked as an export's;" cr
  ."       DATA: the library's elaboration data (scripts/export-elab.sh); N: the" cr
  ."       elaborator's steps per declaration (default 100000000; out of them:" cr
  ."       exit 3); a text of only #check lines checks nothing and exits 0" cr ;
: cli-engine-usage. ( -- )
  ."   check, replay and print run on gforth-fast, the default engine; --checked" cr
  ."       runs Gforth's checking engine instead, about 2.4 times slower, which" cr
  ."       stops at a stack or memory fault where it happens (same verdicts);" cr
  ."       --fast is accepted and changes nothing" cr ;
: cli-other-usage. ( -- )
  ."   replay [--no-manifest] [--fuel N] [--fast] EXPORT RECORD" cr
  ."       check the export again and compare the run record with RECORD" cr
  ."   print [--no-manifest] [--fuel N] [--fast] [--detail] [--name NAME]" cr
  ."         [--latex] [--statement FORMS] [--kernel] [--any-lean-version] EXPORT" cr
  ."       check the export and print each accepted declaration's proof outline;" cr
  ."       FORMS: lean, text, mathematics, leanforth, all (default), joined by commas" cr
  ."   print --lf [--no-manifest] [--fuel N] [--fast] [--any-lean-version] EXPORT" cr
  ."       write every declaration as one LeanForth text, unchecked; what the" cr
  ."       words cannot write is listed on stderr and stubbed, and then the" cr
  ."       exit status is 2 (the text is not the export)" cr
  ."   count [--no-manifest] EXPORT     count the export's records by kind" cr
  ."   reexport [--no-manifest] EXPORT COPY" cr
  ."       write the export again, byte for byte as Lean's exporter writes it" cr ;
: cli-verify-usage. ( -- )
  ."   verify SOURCE.fs --contract CONTRACT [--out DIR] [--json] [--detail]" cr
  ."         [--write-ir]" cr
  ."   verify --replay RECEIPT [--rerun] [--json]" cr ;
: cli-verify-meaning. ( -- )
  ."       check one Forth word against its contract; needs Python 3 and the" cr
  ."       pinned Lean 4.35.0 (V1 only); leanforth verify --help lists its options" cr ;
: cli-info-usage. ( -- )
  ."   version        versions of LeanForth, its Forth host and the format read" cr
  ."   capabilities   what this build supports, what it does not, and its limits" cr
  ."   help           this text" cr ;
: cli-usage. ( -- )
  ." usage: leanforth COMMAND [OPTION]... [FILE]..." cr
  cli-check-usage. cli-other-usage. cli-verify-usage. cli-verify-meaning. cli-info-usage.
  cli-engine-usage. ;
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
\ A command of two files: the first as file 0, the second as file 1.
: cli-two-files ( c-addr0 u0 c-addr1 u1 command -- code )
  >r 1 cli-file! 0 cli-file! r> cli-guard ;
: cli-replay ( export-addr export-u record-addr record-u -- code )
  ['] replay-command cli-two-files ;
: cli-print ( c-addr u -- code ) 0 cli-file! ['] print-command cli-guard ;
\ print's options: every step (--detail), one declaration (--name; the
\ name must stay unchanged meanwhile).
: cli-detail ( -- ) true cli-state opt-detail ! ;
: cli-name! ( c-addr u -- ) cli-state opt-name 2! ;
: cli-count ( c-addr u -- code ) 0 cli-file! ['] count-command cli-guard ;
: cli-reexport ( in-addr in-u out-addr out-u -- code )
  ['] reexport-command cli-two-files ;
: cli-version ( -- code ) ['] version-command cli-guard ;
: cli-capabilities ( -- code ) ['] capabilities-command cli-guard ;
: cli-help ( -- code ) ['] help-command cli-guard ;

\ ---------------------------------------------------------------------------
\ Reading the command line. The arguments after the command are the
\ options it takes and its file names; the first mistake is kept with its
\ argument and reported before anything runs.
[defined] next-arg [if]
: cli-arg ( -- c-addr u true | false )
  next-arg over if cli-seen+ true else 2drop false then ;
[else]
: cli-arg ( -- false ) false ;
[then]

\ Tables of names (lib/name-table.fs): each entry's data is a /cli-entry
\ record, which cli-entry, lays down after the name that follows it.
begin-structure /cli-entry
  field: cli-entry-run          \ the entry's word
  field: cli-entry-first        \ an option's bit; a command's number of file names
  field: cli-entry-second       \ a command's options, as bits; 0 for an option
end-structure
: cli-entry, ( xt first second table "name" -- ) parse-name rot name-entry rot , swap , , ;
\ The record of the entry named c-addr u, or 0.
: cli-entry-find ( c-addr u table -- entry | 0 ) name-table-find dup if name-entry-data then ;

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
131072 constant takes-checked
8192 constant takes-jobs
16384 constant takes-save
32768 constant takes-snapshot
65536 constant takes-progress
262144 constant takes-stale
524288 constant takes-memory
1048576 constant takes-kernel
2097152 constant takes-env
4194304 constant takes-elab
: cli-value ( c-addr u -- c-addr' u' true | false )
  cli-arg if 2swap 2drop true else c" an option without its value" cli-wrong false then ;
\ A decimal number from 0 to max-n with nothing else: (n true) or false.
: cli-digits ( c-addr u -- ud rest ) decimal>number nip ;
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
\ An option's text kept at addr, when it has one.
: cli-text! ( c-addr u addr -- ) >r cli-value if r> 2! else r> drop then ;
: cli-env-option ( c-addr u -- ) cli-state opt-env cli-text! ;
: cli-elab-option ( c-addr u -- ) cli-state opt-elab cli-text! ;
\ --elab-fuel N (plan S1, S1_INTERFACE.md 8): the front end's steps per
\ declaration (elaboration, synthesis, unification, whnf, tactic steps),
\ at most cli-fuel-most; --fuel stays the kernel's.
: cli-elab-fuel-value ( c-addr u n -- )
  dup cli-fuel-most > if drop c" an elaboration fuel above 9007199254740991" cli-wrong
    exit then
  cli-state opt-elab-fuel ! 2drop true cli-state opt-elab-fuel-given ! ;
: cli-steps-option ( c-addr u -- ) cli-state opt-steps cli-text! ;
: cli-elab-fuel-option ( c-addr u -- )
  cli-value 0= if exit then 2dup cli-decimal
  if cli-elab-fuel-value else c" not an elaboration fuel amount" cli-wrong then ;
\ The first --snapshot names the base, each further one a layer on it, in
\ order (plan step SN4); their names are kept in a heap block that grows.
: cli-layers-room ( n -- outcome ) 2* cells cli-state opt-layers block-resize ;
: cli-layer+ ( c-addr u -- )
  cli-state opt-layers# @ 1+ cli-layers-room ok? 0=
  if c" no room for the layers" cli-wrong exit then
  cli-state opt-layers @ cli-state opt-layers# @ 2* cells + 2!
  1 cli-state opt-layers# +! ;
: cli-snapshot-option ( c-addr u -- )
  cli-value if cli-snapshot? if cli-layer+ else cli-snapshot! then then ;
: cli-stale-option ( c-addr u -- ) 2drop true cli-state opt-stale ! ;
: cli-manifest-option ( c-addr u -- ) 2drop cli-no-manifest ;
: cli-detail-option ( c-addr u -- ) 2drop true cli-state opt-detail ! ;
: cli-name-option ( c-addr u -- ) cli-state opt-name cli-text! ;
: cli-resources-option ( c-addr u -- ) 2drop cli-resources ;
: cli-json-option ( c-addr u -- ) 2drop cli-json ;
: cli-latex-option ( c-addr u -- ) 2drop true cli-state opt-latex ! ;
\ --statement FORMS: lean, text, mathematics, leanforth (or all), separated by commas.
: cli-statement-option ( c-addr u -- )
  cli-value 0= if exit then 2dup pr-forms
  if cli-state opt-forms ! 2drop else c" not a list of statement forms" cli-wrong then ;
: cli-strict-option ( c-addr u -- ) 2drop cli-strict ;
\ --fast, --checked: bin/leanforth chose the engine before Forth ran (by
\ any argument --checked); both together are a mistake (cli-engines).
: cli-engine-option ( c-addr u bit -- ) cli-state opt-engines tuck @ or swap ! 2drop ;
: cli-fast-option ( c-addr u -- ) 1 cli-engine-option ;
: cli-checked-option ( c-addr u -- ) 2 cli-engine-option ;
: cli-engines ( -- )
  cli-state opt-engines @ 3 = if s" " c" --fast and --checked together" cli-wrong then ;
: cli-lf-option ( c-addr u -- ) 2drop true cli-state opt-lf ! ;
: cli-kernel-option ( c-addr u -- ) 2drop true cli-state opt-kernel ! ;
: cli-any-lean-option ( c-addr u -- ) 2drop cli-any-lean ;
\ --jobs N, N at least 1; check-run.fs cuts it to the cores. The workers share
\ one input; each holds its own scratch and caches.
: cli-jobs-value ( c-addr u n -- )
  dup 1 < if drop c" not a number of jobs" cli-wrong exit then
  cli-state opt-jobs ! 2drop ;
: cli-jobs-option ( c-addr u -- )
  cli-value 0= if exit then 2dup cli-decimal
  if cli-jobs-value else c" not a number of jobs" cli-wrong then ;
\ --memory-per-check MB, MB at least 1 and small enough that its bytes
\ fit a cell (2^43 - 1 on a 64-bit host).
max-n 20 rshift constant cli-per-check-most
: cli-per-check-value ( c-addr u n -- )
  dup 1 cli-per-check-most 1+ within 0=
  if drop c" a number of megabytes out of range" cli-wrong exit then
  cli-per-check! 2drop ;
: cli-per-check-option ( c-addr u -- )
  cli-value 0= if exit then 2dup cli-decimal
  if cli-per-check-value else c" not a number of megabytes" cli-wrong then ;
\ --progress, or --progress=SECONDS (a number from 0, the lines after every
\ report): see cli-progress!. The second form is handled by cli-option.
: cli-progress-option ( c-addr u -- ) 2drop cli-progress-default cli-progress! ;
: cli-progress-prefix ( -- c-addr u ) s" --progress=" ;
: cli-progress-form? ( c-addr u -- flag )
  cli-progress-prefix nip min cli-progress-prefix compare 0= ;
: cli-progress-value ( c-addr u n -- ) cli-progress! 2drop ;
: cli-progress-equals ( c-addr u -- )
  cli-state arg-set @ takes-progress and 0=
  if c" an option this command does not take" cli-wrong exit then
  cli-progress-prefix nip /string 2dup cli-decimal
  if cli-progress-value else c" not a number of seconds" cli-wrong then ;
name-table: cli-option-table
: cli-option, ( xt bit "name" -- ) 0 cli-option-table cli-entry, ;
' cli-progress-option takes-progress cli-option, --progress
' cli-manifest-option takes-no-manifest cli-option, --no-manifest
' cli-fuel-option takes-fuel cli-option, --fuel
' cli-record-option takes-record cli-option, --record
' cli-detail-option takes-detail cli-option, --detail
' cli-name-option takes-name cli-option, --name
' cli-resources-option takes-resources cli-option, --resources
' cli-json-option takes-json cli-option, --json
' cli-latex-option takes-latex cli-option, --latex
' cli-statement-option takes-statement cli-option, --statement
' cli-strict-option takes-strict cli-option, --strict-axioms
' cli-fast-option takes-fast cli-option, --fast
' cli-checked-option takes-checked cli-option, --checked
' cli-lf-option takes-lf cli-option, --lf
' cli-kernel-option takes-kernel cli-option, --kernel
' cli-any-lean-option takes-any-lean cli-option, --any-lean-version
' cli-jobs-option takes-jobs cli-option, --jobs
' cli-save-option takes-save cli-option, --save-snapshot
' cli-snapshot-option takes-snapshot cli-option, --snapshot
' cli-stale-option takes-stale cli-option, --snapshot-stale-ok
' cli-per-check-option takes-memory cli-option, --memory-per-check
' cli-env-option takes-env cli-option, --env
' cli-elab-option takes-elab cli-option, --elab-data
' cli-elab-fuel-option takes-elab cli-option, --elab-fuel
' cli-steps-option takes-elab cli-option, --steps
: cli-takes? ( entry -- flag ) cli-entry-first @ cli-state arg-set @ and 0<> ;
: cli-taken ( c-addr u entry -- )
  dup cli-takes? if cli-entry-run @ execute exit then
  drop c" an option this command does not take" cli-wrong ;
: cli-option ( c-addr u -- )
  2dup cli-progress-form? if cli-progress-equals exit then
  2dup cli-option-table cli-entry-find ?dup
  if cli-taken else c" an unknown option" cli-wrong then ;
\ A file name, the first or the second.
: cli-positional ( c-addr u -- )
  cli-files @ dup 2 < if cli-file! 1 cli-files +! exit then
  drop c" one file name too many" cli-wrong ;
: cli-option? ( c-addr u -- flag ) 1 min s" -" compare 0= ;
: cli-argument ( c-addr u -- ) 2dup cli-option? if cli-option else cli-positional then ;
: cli-arguments ( set -- )
  cli-state arg-set ! begin cli-arg while cli-argument repeat cli-engines ;


\ The commands: each one's word ( -- code ), the number of file names it
\ needs and the options it takes.
takes-no-manifest takes-fuel or takes-fast or takes-checked or constant checking-set
checking-set takes-record or takes-resources or takes-json or takes-strict or
takes-any-lean or takes-jobs or takes-save or takes-snapshot or takes-progress or takes-stale or
takes-memory or takes-env or takes-elab or constant check-set
checking-set constant replay-set
checking-set takes-detail or takes-name or takes-latex or takes-statement or
takes-lf or takes-any-lean or takes-kernel or constant print-set
name-table: cli-commands
: cli-command, ( xt files set "name" -- ) cli-commands cli-entry, ;
' check-command 1 check-set cli-command, check
' replay-command 2 replay-set cli-command, replay
' print-command 1 print-set cli-command, print
' count-command 1 takes-no-manifest cli-command, count
' reexport-command 2 takes-no-manifest cli-command, reexport
' version-command 0 0 cli-command, version
' version-command 0 0 cli-command, --version
' capabilities-command 0 0 cli-command, capabilities
' help-command 0 0 cli-command, help
' help-command 0 0 cli-command, --help
' help-command 0 0 cli-command, -h

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

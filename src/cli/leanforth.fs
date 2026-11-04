\ The command line (plan tasks 3.4.1-3.4.2, v0): the Forth entry point that
\ bin/leanforth runs as `gforth src/main.fs -e cli-main COMMAND ...`.
\ Commands, documented in docs/user/COMMAND_LINE.md:
\   check [--no-manifest] [--fuel N] [--record RECORD] EXPORT
\       read the Lean export into the checker's input
\       (import/checker-input.fs; its manifest checked unless --no-manifest
\       says not to), check every declaration in file order with
\       check-declaration through the checked environment's publisher
\       (import/run-record.fs's run, rr-check), and print one line per
\       declaration with its verdict, read from its published slot; then a
\       summary; with --record, also write the run record (plan 2.2.5);
\   replay [--no-manifest] [--fuel N] EXPORT RECORD
\       check the export again and compare the new run record with RECORD
\       (import/run-replay.fs): the replay report, exit 0 confirmed, 1
\       refused (a difference), 4 when it cannot be compared;
\   count [--no-manifest] EXPORT          the record counts (ndjson-count.fs);
\   reexport [--no-manifest] EXPORT COPY  the byte-exact copy (ndjson-emit.fs);
\   version, capabilities, help (also --version, --help and -h).
\ Exit codes: 0 all accepted (or the command done), 1 something rejected,
\ 2 unsupported or unknown, 3 a resource limit (out of fuel or room),
\ 4 malformed input (also a malformed command line, or a file that cannot
\ be opened or created), 5 an internal fault (a Forth exception, a check
\ that threw, a publisher fault). When outcomes differ, the most severe
\ wins, in the order 5, 4, 1, 3, 2, 0: a fault or a malformed export puts
\ every verdict in doubt; a rejection is Lean's definite "no"; a limit or
\ a missing feature leaves a declaration undecided. cli-main leaves the
\ host with status 100 + code, so that bin/leanforth tells LeanForth's
\ codes from the host's own failures (Gforth ends with 0 or 1 after an
\ uncaught error), and maps any other status to 5.
\
\ Trust boundary: "accepted" is printed only by lf-check-verdict.
\ (kernel/check-declaration.fs) from a declaration's published slot, and
\ the exit code comes from the slots' outcomes as lf-env-outcome reads
\ them; staging, parsing and printing here can hand the checker a wrong
\ claim or misreport a failure, never make a declaration accepted. Today's
\ check holds small exports only (64 names, levels and term nodes, 32
\ declarations): anything larger ends full, exit 3, and the output says
\ so. Untrusted, like everything in src/ until the review gate.
\
\ The Forth interface, for a Forth session or a test, each ( -- code )
\ after its arguments, printing what the command prints: cli-check
\ ( c-addr u ), cli-replay ( export-addr export-u record-addr record-u ),
\ cli-count ( c-addr u ), cli-reexport ( in-addr in-u out-addr out-u ),
\ cli-version, cli-capabilities, cli-help. They use the options in force:
\ cli-options restores the defaults (manifest checked, fuel
\ cli-default-fuel, no record), cli-no-manifest, cli-fuel! and
\ cli-record! change them. A THROW inside a command is caught and
\ reported: code 5.
\
\ Host words: next-arg (Gforth 0.7.3 and 1.0) reads the command line,
\ where a host without it reads none; (bye) leaves with a status, where a
\ host without it ends with an uncaught THROW, which the wrapper reports
\ as an internal fault; version-string names the host when it exists;
\ getenv reads the commit bin/leanforth found for the run record
\ (LEANFORTH_COMMIT, LEANFORTH_MODIFIED), where a host without it records
\ none.
\ State: one record in the checker context, cli-state (the options, the
\ command line's file names and first mistake, the exit code so far and
\ the declarations counted by verdict), set up with the defaults in every
\ context; and one manifest record, cli-manifest, for re-exports, shared
\ because it owns heap buffers. The run itself is in run-record.fs's
\ shared record. One command runs at a time.

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
require ../present/print-names.fs

\ Exit codes, and the code of each outcome.
0 constant exit-accepted     \ every declaration accepted, or the command done
1 constant exit-rejected     \ something rejected
2 constant exit-undecided    \ unsupported or unknown
3 constant exit-limit        \ a resource limit: out of fuel or room
4 constant exit-malformed    \ malformed input or command line
5 constant exit-fault        \ an internal fault
\ Indexed by outcome: ok, invalid, exhausted, unknown, rejected,
\ unsupported, full; the table must end at HERE, otherwise the load stops.
create cli-codes
  exit-accepted , exit-malformed , exit-limit , exit-undecided , exit-rejected ,
  exit-undecided , exit-limit ,
here cli-codes - outcome-full 1+ cells <>
[if] .( leanforth.fs: one code per outcome) cr abort [then]
: outcome>code ( outcome -- code )
  dup outcome? if cells cli-codes + @ else drop exit-fault then ;
\ Severity, by code: 0 < 2 < 3 < 1 < 4 < 5. The more severe of two codes.
create cli-severity  0 , 3 , 1 , 2 , 4 , 5 ,
: code-severity ( code -- n ) cells cli-severity + @ ;
: worse-code ( code1 code2 -- code )
  2dup code-severity swap code-severity > if nip else drop then ;

100000 constant cli-default-fuel   \ fuel of each declaration's check
7 constant not-checked     \ the count after the outcomes': declarations not reached
begin-structure /cli-run
  field: opt-unchecked          \ true: manifests are not checked (--no-manifest)
  field: opt-fuel               \ fuel each declaration's check starts with (--fuel)
  2 cells +field opt-record     \ the run record's file name (--record), or 0 0
  4 cells +field arg-files      \ the file names given, in order (two c-addr u)
  field: arg-count              \ how many were given
  field: arg-set                \ the options the command takes, as bits
  2 cells +field arg-culprit    \ the argument of the first mistake, or 0 0
  field: arg-mistake            \ counted string: the first mistake, or 0
  field: run-worst              \ the exit code so far
  not-checked 1+ cells +field run-counts   \ declarations by verdict
end-structure
/cli-run context-record: cli-state
manifest: cli-manifest

: cli-unchecked ( -- addr ) cli-state opt-unchecked ;
: cli-fuel ( -- addr ) cli-state opt-fuel ;
: cli-record ( -- addr ) cli-state opt-record ;
: cli-file ( k -- c-addr u ) 2* cells cli-state arg-files + 2@ ;
: cli-files ( -- addr ) cli-state arg-count ;
: cli-worst ( -- addr ) cli-state run-worst ;
: cli-count-of ( k -- addr ) cells cli-state run-counts + ;

\ Options. cli-options also forgets the file names and any mistake.
: cli-options ( -- ) cli-state /cli-run erase cli-default-fuel cli-fuel ! ;
' cli-options context-setup
: cli-no-manifest ( -- ) true cli-unchecked ! ;
: cli-fuel! ( n -- ) cli-fuel ! ;
\ Write the run record of every later check to the file named c-addr u,
\ which must stay unchanged meanwhile.
: cli-record! ( c-addr u -- ) cli-record 2! ;
: cli-record? ( -- flag ) cli-record @ 0<> ;
\ A command's start: nothing counted, nothing failed.
: cli-start ( -- ) exit-accepted cli-worst ! 0 cli-count-of not-checked 1+ cells erase ;
: cli-code! ( code -- ) cli-worst @ worse-code cli-worst ! ;

\ Printing numbers in decimal, whatever BASE is.
: .decimal ( n -- ) base @ >r decimal 0 .r r> base ! ;
\ An internal fault: one line, and code 5.
: cli-fault ( c-addr -- ) ." internal fault: " count type cr exit-fault cli-code! ;
: cli-note ( c-addr -- ) ." note: " count type cr ;

\ ---------------------------------------------------------------------------
\ check. The run is run-record.fs's, rr-check: every declaration in input
\ order, each with lf-env-step and its diagnostic kept, stopping after a
\ THROW in a check (the context spent) or a fault of the publisher, which
\ is an internal fault. The verdicts are printed after the run, each from
\ its published slot, with the diagnostic its check left.
64 constant cli-pool   \ dependencies the run's environment holds, as make run-record's
: cli-name. ( d -- ) lf-input-name ['] type lf-pp-name-to ;
\ The diagnostic declaration d's check left, when it left one.
: cli-at. ( step -- )
  ."  at " dup kept-site @ lf-diag-site. ." : " dup kept-first @ .decimal space
  kept-second @ .decimal ;
: cli-why. ( d -- )
  rr-step-of dup kept-code @ dup lf-diag-none = if 2drop exit then
  ."   " dup lf-diag-name type ." ; diagnostic " .decimal cli-at. cr ;
: cli-tally ( outcome -- ) dup outcome>code cli-code! cli-count-of 1 swap +! ;
\ Declaration d's line: its name and the verdict its slot holds.
: cli-verdict ( d -- )
  dup cli-name. ." : " dup lf-check-verdict. cr
  dup lf-env-outcome dup cli-tally ok? if drop else cli-why. then ;
: cli-skipped ( d -- ) cli-name. ." : not checked" cr 1 not-checked cli-count-of +! ;
\ The declarations whose check began; whether the run stopped on a fault:
\ a THROW spends the context, a publisher's fault leaves a slot open.
: cli-stepped ( -- n ) run-record rr-stepped @ ;
: cli-faulted? ( -- flag ) lf-env-spent? run-record rr-run @ ok? 0= or ;
: cli-stopped ( -- )
  c" the run stopped: a check threw, or publishing failed" cli-fault
  lf-input-count cli-stepped ?do i cli-skipped loop ;
: cli-verdicts ( -- )
  cli-stepped 0 ?do i cli-verdict loop cli-faulted? if cli-stopped then ;

\ The summary: "N declarations: a accepted, r rejected, ...", in this order.
create cli-order
  outcome-ok , outcome-rejected , outcome-unknown , outcome-unsupported ,
  outcome-invalid , outcome-exhausted , outcome-full , not-checked ,
: cli-kind. ( k -- )
  case outcome-ok of ." accepted" endof not-checked of ." not checked" endof
    dup outcome-text type endcase ;
: cli-item ( first? k -- first? )
  dup cli-count-of @ ?dup 0= if drop exit then
  rot 0= if ." , " then .decimal space cli-kind. false ;
: cli-summary ( -- )
  lf-input-count dup .decimal ."  declaration" 1 <> if ." s" then ." : "
  true not-checked 1+ 0 do i cells cli-order + @ cli-item loop drop cr ;

\ Notes after a run: the limits behind full, the fuel behind exhausted.
\ check leaves the stores' capacity settings at their defaults: it reads
\ with import/checker-input.fs and keeps the run record in run-record.fs's
\ tables, both sized for those defaults (import/feed.fs takes any size).
: cli-limits ( -- )
  ." note: today's check holds at most " lf-name-capacity .decimal ."  names, "
  lf-level-capacity .decimal ."  levels, " lf-term-capacity .decimal ."  term nodes and "
  lf-input-capacity .decimal ."  declarations per export," cr
  ." note: so only small exports, such as the test fixtures, fit; larger ones end full"
  cr ;
: cli-fuel-note ( -- )
  ." note: a check ran out of fuel (" cli-fuel @ .decimal
  ."  steps each); --fuel N gives each more" cr ;
: cli-notes ( -- )
  outcome-full cli-count-of @ if cli-limits then
  outcome-exhausted cli-count-of @ if cli-fuel-note then ;

\ After the run: the verdicts, the summary and the notes; or why there was
\ no run, when no environment could be made or used.
: cli-no-room ( -- )
  ." error: no room for the checked environment" cr exit-limit cli-code! ;
: cli-no-env ( -- )
  run-record rr-run @ outcome-full = if cli-no-room exit then
  c" no checked environment could be made or used" cli-fault ;
\ Verdicts only from the run's own environment, by identity (rr-ours?).
: cli-made? ( -- flag ) rr-ours? lf-env-view ok? and ;
: cli-results ( -- )
  cli-made? if cli-verdicts cli-summary cli-notes else cli-no-env then ;

\ A read that failed: the outcome, the reason, the field and the line
\ (0 for the manifest), and for a JSON error the byte within the line.
: cli-field. ( c-addr u -- ) dup if ." field " type ." , " else 2drop then ;
: cli-byte. ( export -- )
  export-json dup json-why @ if ." , byte " json-offset .decimal else drop then ;
: cli-input-error ( outcome -- )
  ." error: " outcome-text type ." : " cin-error type ."  (" cli-field. ." line "
  .decimal cin-export cli-byte. ." )" cr ;
\ A failure about the manifest is at line 0 (the export opened, see
\ cli-opens?): a hint at the export step and the explicit way out.
: manifest-failed? ( outcome -- flag )
  outcome-invalid = cli-unchecked @ 0= and cin-error 2drop 2drop 0= and ;
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
\ The export (file 0) into the checker's input, its manifest checked
\ unless --no-manifest. With a record (--record, replay): the file rr-start
\ kept and hashed, through rr-import, which records the outcome and whether
\ the manifest was enforced. Without one: the file read once
\ (rr-read-once), with no hash, metadata or manifest pass of the record's,
\ so a plain check of a large export reads it only as the checker needs.
: cli-checked? ( -- flag ) cli-unchecked @ 0= ;
: cli-import ( -- outcome ) cli-checked? rr-import ;
: cli-input ( -- outcome )
  cli-record? if cli-import else 0 cli-file cli-checked? rr-read-once then ;
: cli-run ( -- ) cli-input dup ok? if drop rr-check cli-results else cli-unread then ;
: cli-settings ( -- ) rr-release cli-fuel @ cli-pool rr-settings! ;

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
  cli-unchecked-note cli-settings
  cli-recording? if cli-run cli-recorded then rr-release cli-worst @ ;
: check-command ( -- code )
  cli-start cli-opens? 0= if cli-unopened exit then
  cli-over-export? if ." error: RECORD must not be EXPORT" cr exit-malformed exit then
  cli-checks ;

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
\ version and capabilities.
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
: cli-checks. ( -- )
  ." supported:" cr
  ."   check: Lean 4.35.0 exports (lean4export 3.1.0 NDJSON), read in Forth;" cr
  ."     the manifest checked unless --no-manifest" cr
  ."   check: definitions and theorems built from Sort, variables, application, fun," cr
  ."     forall and earlier accepted declarations (the first checker, ADR 0011);" cr
  ."     an accepted one is labelled experimental, not independently audited" cr
  ."   check --record, replay: run records 0.1 and their replay (plan task 2.2.5)" cr
  ."   count, reexport: exports of any size, up to all of Mathlib" cr ;
: cli-lacks. ( -- )
  ." unsupported (check answers unsupported, exit 2):" cr
  ."   axioms, opaque declarations, unsafe and partial definitions;" cr
  ."   let, literals, projections and metadata in a term;" cr
  ."   inductive types, quotients and mutual blocks (refused while reading)" cr
  ."   unfolding definitions: some correct proofs end unknown (exit 2)" cr ;
: cli-limits. ( -- )
  ." limits (check answers full, exit 3; small exports only):" cr
  ."   " lf-name-capacity .decimal ."  names (" lf-name-byte-capacity .decimal
  ."  bytes), " lf-level-capacity .decimal ."  levels, " lf-term-capacity .decimal
  ."  term nodes, " lf-input-capacity .decimal ."  declarations per export" cr
  ."   " lf-param-capacity .decimal ."  universe parameters per declaration, "
  lf-cref-argument-capacity .decimal ."  universe arguments per constant" cr
  ."   " lf-env-dep-capacity .decimal ."  dependencies per declaration, "
  cli-pool .decimal ."  per export" cr
  ."   fuel " cli-default-fuel .decimal ."  steps per declaration (--fuel N)" cr ;
: cli-planned. ( -- )
  ." planned, not built: print, program, serve, --json receipts," cr
  ."   larger stores (plan task 3.3.1)" cr ;
: capabilities-command ( -- code )
  ." leanforth " cli-version-text type ." : what this build can do" cr
  cli-checks. cli-lacks. cli-limits. cli-planned. exit-accepted ;

\ ---------------------------------------------------------------------------
\ help.
: cli-usage. ( -- )
  ." usage: leanforth COMMAND [OPTION]... [FILE]..." cr
  ."   check [--no-manifest] [--fuel N] [--record RECORD] EXPORT" cr
  ."       check every declaration of a Lean export, in file order" cr
  ."   replay [--no-manifest] [--fuel N] EXPORT RECORD" cr
  ."       check the export again and compare the run record with RECORD" cr
  ."   count [--no-manifest] EXPORT     count the export's records by kind" cr
  ."   reexport [--no-manifest] EXPORT COPY" cr
  ."       write the export again, byte for byte as Lean's exporter writes it" cr
  ."   version        versions of LeanForth, its Forth host and the format read" cr
  ."   capabilities   what this build supports, what it does not, and its limits" cr
  ."   help           this text" cr ;
: cli-codes. ( -- )
  ." exit status: 0 all accepted (or done), 1 something rejected," cr
  ."   2 unsupported or unknown, 3 a resource limit, 4 malformed input or" cr
  ."   command line, 5 an internal fault; the most severe of 5, 4, 1, 3, 2 wins" cr ;
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
: cli-value ( c-addr u -- c-addr' u' true | false )
  cli-arg if 2swap 2drop true else c" an option without its value" cli-wrong false then ;
\ A decimal number from 0 to max-n with nothing else: (n true) or false.
: cli-digits ( c-addr u -- ud rest ) base @ >r decimal 0 0 2swap >number r> base ! nip ;
: cli-in-range? ( ud -- n true | false ) 0= over 0< 0= and if true else drop false then ;
: cli-decimal ( c-addr u -- n true | false )
  dup 0= if 2drop false exit then cli-digits if 2drop false else cli-in-range? then ;
: cli-fuel-option ( c-addr u -- )
  cli-value 0= if exit then 2dup cli-decimal
  if cli-fuel! 2drop else c" not a fuel amount" cli-wrong then ;
: cli-record-option ( c-addr u -- ) cli-value if cli-record! then ;
: cli-manifest-option ( c-addr u -- ) 2drop cli-no-manifest ;
create cli-option-table
  ' cli-manifest-option takes-no-manifest 0 cli-entry, --no-manifest
  ' cli-fuel-option takes-fuel 0 cli-entry, --fuel
  ' cli-record-option takes-record 0 cli-entry, --record
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
takes-no-manifest takes-fuel or takes-record or constant check-set
takes-no-manifest takes-fuel or constant replay-set
create cli-commands
  ' check-command 1 check-set cli-entry, check
  ' replay-command 2 replay-set cli-entry, replay
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

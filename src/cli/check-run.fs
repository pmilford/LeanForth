\ The whole-library check behind `leanforth check` (plan tasks 3.4.1 and
\ 3.4.3, and the command line's part of 6.5.2): a Lean export staged by
\ the importer stage (import/stage.fs, its manifest checked unless the
\ caller says not to), fed to the checker (import/feed.fs, which raises
\ the stores' capacities to fit, so there is no fixed size limit), and
\ every declaration checked in file order, one at a time, in a new
\ checked environment, by check-declaration through the publisher's
\ serial step (lf-env-step). The members of an inductive block after its
\ first are published with it (ADR 0015 B5) and are not checked again, as
\ the publisher's own run skips them (lf-env-published?). After each
\ check it keeps the outcome published, the diagnostic, the step reached
\ and the fuel the check used; it times each phase and reads the
\ process's peak resident memory. Untrusted: printing is the command
\ line's (cli/leanforth.fs, cli/check-json.fs), which reads every
\ verdict from the environment's slots, never from what is kept here.
\ LeanForth-specific (it drives the checker).
\
\ One run, in this order (cli/leanforth.fs drives it):
\ - ck-start ( fuel -- ) frees what the last run left (ck-release),
\   forgets its facts, keeps the fuel each check starts with and starts
\   the clock;
\ - ck-any-version! ( flag -- ), after ck-start: true lets the stage read
\   an export of any exporter and Lean version, only its format pinned
\   (stage-any-version!; --any-lean-version), false (ck-start's) not;
\ - ck-jobs! ( n -- ), after ck-start: n is cut to the cores and the pool's
\   queue size (ck-jobs-most); with n above 1 (--jobs), ck-load
\   also makes n worker contexts, each fed the same stage, and ck-check
\   checks in parallel (kernel/env-schedule.fs), keeping exactly the facts
\   the serial run keeps (see "The parallel run" below); 0 or 1, ck-start's,
\   checks one declaration at a time in this context;
\ - ck-load ( c-addr u checked? -- outcome ) stages the export file
\   c-addr u, its manifest checked when checked? is true, frees the
\   stage's loading aids (stage-unmap), then feeds it to this context's
\   input; the outcome is the stage's or the feed's, kept
\   (ck-read-outcome, ck-loaded?), and ck-phase-failed tells which phase
\   failed (ck-staging, ck-feeding), -1 for none; or, for an export that
\   does not open, ck-unopened instead (ck-opening);
\ - ck-check ( -- ) checks every declaration in a new environment, kept
\   current, its dependency pool starting with room for lf-env-pool-start
\   (it grows); ck-outcome is then ok when every slot ended final and the run
\   did not stop, else the first failure: full when the facts
\   (ck-facts-made? false) or the environment (ck-made? false) found no
\   room, invalid when the environment could not be used or the run
\   stopped on a fault (ck-faulted?: a check threw, which spends the
\   context, or publishing failed; ck-steps-begun tells how far it came);
\   ck-stopped?, which the text and JSON reports both read, is true when
\   the run's verdicts can be read and it stopped or did not end ok;
\ - ck-progress! ( seconds -- ) and ck-lines! ( xt -- ), after ck-start: a
\   progress line on stderr every that many seconds (0: after every report;
\   the cli's --progress), and xt ( d -- ), the cli's text line of declaration
\   d, called in file order as each declaration is final, in the serial run
\   and (from the scheduler's tick, lf-sched-tick!) the parallel one, so
\   that a stopped run keeps the lines so far (see "Progress lines" below);
\   ck-done tells how many were given out;
\ - ck-finish ( -- ) takes the run's total time so far (phase ck-total);
\   a run with workers also times its plan and its jobs (ck-plan-clock,
\   ck-run-clock, ck-run-wall) and, through the scheduler's clock
\   (lf-sched-clock!), what each worker and the driving task spent busy
\   and waiting in the jobs' run (lf-sched-busy, ck-waiting, ck-busy-all,
\   ck-waiting-all, ck-driver-busy, ck-driver-waiting: read before
\   ck-release, the workers still there); ck-snapshot-save is timed as the
\   phase ck-saving, shown only when a save was asked (ck-phase-shown?);
\ - then, before ck-release, the verdicts are read in a snapshot of the
\   run's own environment (ck-verdicts?, then lf-env-outcome), and the
\   facts with ck-kept (a run-record.fs /rr-step: outcome, diagnostic,
\   step; then the fuel), ck-fuel-of, ck-fuel-total, ck-fuel-unknowns,
\   ck-top@ (ck-tops of them), the times (ck-phase-wall, ck-phase-cpu,
\   ck-phase-name), ck-peak, ck-engine, ck-staged-bytes and the input's
\   sizes;
\ - ck-release ( -- ) frees the environment (only while it is the
\   current one with the run's identity, as run-record.fs's rr-release
\   does), detaches the names from the stage and frees it, empties the
\   stores and gives them back the capacities they had before the feed
\   (ck-restored: ok, or the first refusal), and frees the facts.
\   ck-start does it too. A caller that catches a THROW out of ck-load or
\   ck-check calls it before passing the THROW on.
\
\ Fuel. A check's fuel used is its budget less the fuel its last counter
\ left, read after the check from the checker's own counters, as the
\ tests of mixed-infer read lf-minfer-fuel: an inductive block's
\ (lf-ind-fuel) once the block began its steps, the audit's
\ (lf-check-left) up to step 3 of check-declaration and in every step of
\ a quotient record, inference's (lf-minfer-fuel) from step 4 on, an
\ axiom's step 7 included; a check that began no step used none.
\ So a declaration accepted with fuel used u is accepted with a budget of
\ u and exhausted with u - 1 (tests/cli/leanforth.fs and
\ test_leanforth.py check it), and one exhausted used the budget: that
\ is what it reports, whichever counter ran out (ck-spent-all?). A
\ failed inference gives its counter up (mixed-infer's lf-minfer-failed
\ leaves zero): a check that failed with no fuel left but not exhausted
\ used an amount not known, kept as ck-fuel-unknown (-1), counted apart
\ (ck-fuel-unknowns) and in no total. The members after a block's first
\ count no fuel of their own. A report only: nothing reads it back into a
\ check.
\
\ Host words: utime and cputime (Gforth 0.7.3 and 1.0) give wall and CPU
\ time in microseconds, where a host without them reports none
\ (ck-timed? false); the peak resident memory is the VmHWM line of
\ /proc/self/status (Linux), where a host without that file reports none;
\ getenv reads the engine bin/leanforth ran, where a host without it
\ reports none.
\ State: four shared globals, ck-stage (/stage), ck-feeding-record and
\ ck-worker-feed (/feed) and ck-state (the run's facts and settings), not
\ context records, because they own heap blocks, as checker-input.fs's
\ records do: one run at a time, in any context, its input and environment
\ landing in the context current while it runs (a parallel run's workers
\ are the scheduler's, lf-sched). Only the driving task writes them. The command line's own
\ options and counts are context records (cli/leanforth.fs, tally.fs).

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/slab.fs
require ../lib/bytes.fs
require ../lib/decimal.fs
require ../lib/bits.fs
require ../lib/sha256.fs
require ../lib/xt-table.fs
require ../lib/name-table.fs
require ../lib/find.fs
require ../core/input.fs
require ../core/diagnostics.fs
require ../kernel/environment.fs
require ../kernel/env-publish.fs
require ../kernel/check-declaration.fs
require ../kernel/env-schedule.fs
require ../import/stage.fs
require ../import/feed.fs
require ../import/run-record.fs
require ../kernel/env-snapshot.fs
require ../kernel/env-import.fs
require ../kernel/env-layers.fs

\ What a check left, kept after its step: run-record.fs's layout
\ (kept-outcome, kept-code, kept-first, kept-second, kept-site,
\ kept-step: check-block's step for a block, else check-declaration's),
\ then the fuel used. One layout for both runs' diagnostics.
begin-structure /ck-step
  /rr-step +field ck-step-kept
  field: cks-fuel
end-structure

\ The stores' capacity settings the feed raises: each row its reader
\ ( -- n ) and its writer ( n -- outcome ).
begin-structure /ck-capacity
  field: capacity-get
  field: capacity-set
end-structure
create ck-capacities
  ' lf-term-capacity , ' lf-term-capacity! ,  ' lf-level-capacity , ' lf-level-capacity! ,
  ' lf-cref-capacity , ' lf-cref-capacity! ,  ' lf-input-capacity , ' lf-input-capacity! ,
here ck-capacities - /ck-capacity / constant ck-capacities#

\ The checker's switches in the context a run starts in, each a cell
\ ( -- addr ): term sharing, the scratch room, the audit memo's mode,
\ the caches, each check's memory limit (core/scratch-meter.fs). A
\ parallel check copies them into each worker, so that its checks run as
\ the serial run's would. (The switch that copied the input was retired
\ with the copy, compact-store plan step S5's parts 4-5.)
: ck-memo-mode ( -- addr ) lf-audit-state lf-aud-mode ;
: ck-caches-off ( -- addr ) lf-caches lf-caches-off ;
: ck-per-check ( -- addr ) lf-meter lf-meter-setting ;
create ck-switches
  ' lf-term-share-off , ' lf-input-room-cell , ' ck-memo-mode , ' ck-caches-off ,
  ' ck-per-check ,
here ck-switches - 1 cells / constant ck-switches#

\ A clock reading: wall and CPU time, doubles.
begin-structure /ck-clock
  2 cells +field clock-wall
  2 cells +field clock-cpu
end-structure
\ The phases timed: staging, feeding, checking, saving the snapshot, and
\ the run's total.
0 constant ck-staging  1 constant ck-feeding  2 constant ck-checking  3 constant ck-saving
4 constant ck-total  5 constant ck-phases
\ Not a timed phase: the export did not open (ck-unopened).
ck-phases constant ck-opening
10 constant ck-top-room   \ declarations in the list of the most fuel used
320 constant ck-pline-room   \ bytes of a progress line

\ What workers reading this context's input in place depend on (ck-lent!):
\ each part they read (import/feed.fs's lf-feed-shared), as its block's
\ address and its count, a pair that changes when a record is made there
\ or its block moves -- the view's three tables and its leaves, the
\ declarations, their name index and inductive data, and the references'
\ store, pairs and table. ck-parts lists a word ( -- addr n ) per part.
: ck-store@ ( store -- addr n ) dup store-records swap store-count @ ;
: ck-htab@ ( htab -- addr n ) dup htab-base swap htab-count ;
: ck-nodes@ ( -- addr n ) lf-term-view lf-tview-nodes ck-htab@ ;
: ck-fields@ ( -- addr n ) lf-term-view lf-tview-fields ck-htab@ ;
: ck-binders@ ( -- addr n ) lf-term-view lf-tview-binders ck-htab@ ;
: ck-leaves@ ( -- addr n ) lf-term-view lf-tview-leaves slab-data ;
: ck-decls@ ( -- addr n ) lf-inputs ck-store@ ;
: ck-names@ ( -- addr n ) lf-input-names slab-data ;
: ck-more@ ( -- addr n ) lf-input-more slab-data ;
: ck-refs@ ( -- addr n ) lf-crefs ck-store@ ;
: ck-ref-pairs@ ( -- addr n ) lf-cref-pool slab-data ;
: ck-ref-table@ ( -- addr n ) lf-cref-table ck-htab@ ;
create ck-parts  ' ck-nodes@ , ' ck-fields@ , ' ck-binders@ , ' ck-leaves@ ,
  ' ck-decls@ , ' ck-names@ , ' ck-more@ ,
  ' ck-refs@ , ' ck-ref-pairs@ , ' ck-ref-table@ ,
here ck-parts - 1 cells / constant ck-parts#
ck-parts# 2* cells constant /ck-lend

begin-structure /ck
  field: ck-budget               \ fuel each check starts with
  field: ck-failed               \ the phase that failed, or -1
  field: ck-loaded               \ ck-load's outcome; invalid before it
  field: ck-run                  \ the run's outcome; invalid before ck-check
  field: ck-facts-made           \ true once the facts had room
  field: ck-checked              \ true once ck-check made its environment
  field: ck-env-id               \ the run's environment's identity, or 0
  field: ck-stepped              \ declarations whose check began
  field: ck-binder-hook          \ the feed's binder hook, or 0 (ck-hooks!)
  field: ck-decl-hook            \ the feed's declaration hook, or 0
  field: ck-faulted              \ true when the run stopped on a fault
  field: ck-began-feed           \ true once the feed began: names attached
  field: ck-any-lean             \ true: an export of any Lean version (ck-any-version!)
  field: ck-jobs-asked           \ workers of a parallel check (ck-jobs!); 0, 1: serial
  field: ck-serial-why           \ why workers were asked for but not used (ck-why-*), or 0
  field: ck-pool-made            \ workers the pool ran with (ck-pool-started?)
  field: ck-pool-lacked          \ and those it started without: the host refused them
  field: ck-print                \ the fed input's fingerprint: every worker's must be it
  /ck-lend +field ck-lent       \ the input the workers read (ck-lent!)
  /ck-lend +field ck-lend-now   \ and as it is now (ck-moved?)
  field: ck-remade               \ times the workers were made again (ck-relent)
  field: ck-shifted              \ true: it moved during the run (ck-shift?)
  field: ck-shifted-at           \ every slot below it was final then
  field: ck-clean-at             \ the same at the last comparison that found no change
  field: ck-pre-xt               \ ( d -- n ) the decision on readiness (ck-pre-word!)
  field: ck-checker              \ the check word ( -- ) (ck-check-word!)
  ck-switches# cells +field ck-switched    \ the checker's switches, for each worker
  ck-capacities# cells +field ck-saved   \ capacities before the feed
  field: ck-restored-outcome     \ giving them back: ok, or the first refusal
  field: ck-stage-bytes          \ heap bytes the stage holds once staged
  field: ck-declarations#        \ the input as fed: declarations,
  field: ck-terms#               \ term nodes,
  field: ck-levels#              \ levels,
  field: ck-references#          \ constant references,
  field: ck-names#               \ and the stage's names
  2 cells +field ck-fuel-sum     \ fuel used by every check whose use is known, a double
  field: ck-unknowns             \ checks whose fuel used is not known
  field: ck-top-count            \ entries in ck-top
  ck-top-room cells +field ck-top          \ declarations by fuel used, most first
  /ck-clock +field ck-phase-mark           \ the clock when the phase began
  /ck-clock +field ck-sub-mark             \ and when a part of the check phase began
  /ck-clock +field ck-plan-time            \ the scheduler's plan (lf-sched-plan)
  /ck-clock +field ck-jobs-time            \ the jobs' run (lf-sched-run)
  field: ck-save-tried                     \ true once ck-snapshot-save ran
  /ck-clock +field ck-run-mark             \ and when the run began
  ck-phases /ck-clock * +field ck-times    \ each phase's time
  /slab +field ck-steps          \ the kept steps, /ck-step each
  2 cells +field ck-export       \ the export file's name, as ck-load was given it
  field: ck-checked-read         \ true: its manifest was checked
  field: ck-snapped              \ true: a run of a loaded snapshot (ck-snapshot-load)
  field: ck-snap-saved           \ the snapshot save's outcome, invalid before it
  2 cells +field ck-snap-file
  \ the snapshot file's name, as ck-snapshot-load was given it
  field: ck-prog-on              \ true: progress lines on stderr (ck-progress!)
  field: ck-prog-secs            \ seconds between them; 0: after every report
  2 cells +field ck-prog-mark    \ wall time (us) of the last one
  field: ck-line-xt              \ ( d -- ) the line of a final declaration, or 0 (ck-lines!)
  field: ck-cursor               \ declarations given out: all below it, in file order
  field: ck-accepted             \ of them, those the check accepted
  field: ck-others               \ and the others
  field: ck-unflushed            \ lines given out since the last flush
  2 cells +field ck-flush-mark   \ wall time (us) of the last flush
  field: ck-pline#               \ bytes in the progress line
  ck-pline-room +field ck-pline  \ the progress line, built here
  field: ck-importing            \ true: an export checked against it (ck-snapshot-import)
  field: ck-snap-bad             \ true: the snapshot was refused
  field: ck-layers               \ layers loaded on the base
  field: ck-lay-ids              \ per layer loaded, its identity (ck-layer-id), or 0
  field: ck-jobs-kept            \ the workers asked for, kept while a snapshot loads
  field: ck-carry-xt             \ ( -- ) run after the carry pass, or 0 (ck-carried!)
end-structure
create ck-state /ck allot  ck-state /ck erase
create ck-snap /snap allot  ck-snap snap-init   \ the snapshot loaded (a base)
create ck-out /snap allot  ck-out snap-init     \ the snapshot written
create ck-import /imp allot  ck-import /imp erase   \ what an import pass takes from it
create ck-stage /stage allot  ck-stage /stage erase
create ck-feeding-record /feed allot  ck-feeding-record /feed erase
create ck-worker-feed /feed allot  ck-worker-feed /feed erase

: ck-fuel-budget ( -- n ) ck-state ck-budget @ ;
: ck-outcome ( -- outcome ) ck-state ck-run @ ;
: ck-outcome! ( outcome -- ) ck-state ck-run ! ;
: ck-phase-failed ( -- phase|-1 ) ck-state ck-failed @ ;
: ck-read-outcome ( -- outcome ) ck-state ck-loaded @ ;
: ck-loaded? ( -- flag ) ck-read-outcome ok? ;
\ Whether the export was staged: it opened and staging did not fail.
: ck-staged? ( -- flag ) ck-phase-failed dup ck-staging <> swap ck-opening <> and ;
\ The export did not open: nothing was read (invalid, ck-opening).
: ck-unopened ( -- )
  outcome-invalid ck-state ck-loaded ! ck-opening ck-state ck-failed ! ;
: ck-steps-begun ( -- n ) ck-state ck-stepped @ ;
: ck-facts-made? ( -- flag ) ck-state ck-facts-made @ ;
: ck-made? ( -- flag ) ck-state ck-checked @ ;
: ck-faulted? ( -- flag ) ck-state ck-faulted @ ;
: ck-restored ( -- outcome ) ck-state ck-restored-outcome @ ;
: ck-fuel-total ( -- ud ) ck-state ck-fuel-sum 2@ ;
: ck-fuel-unknowns ( -- n ) ck-state ck-unknowns @ ;
-1 constant ck-fuel-unknown   \ a check's fuel used, when it is not known
\ The stage's heap bytes, and the input as fed.
: ck-staged-bytes ( -- u ) ck-state ck-stage-bytes @ ;
\ Workers of a parallel check (--jobs): set after ck-start, before
\ ck-load; 0 or 1 checks one declaration at a time in this context.
\ At most one worker per core and per queued job: more could not run at once
\ (the workers share one input, but each holds its own scratch and caches).
: ck-jobs-most ( -- n ) task-cores task-queue-jobs min ;
: ck-jobs! ( n -- ) ck-jobs-most min ck-state ck-jobs-asked ! ;
\ Why the run is serial though workers were asked for: 1, or the pool's
\ (negative) refusal.
1 constant ck-why-host         \ threads here need an x86-64 host (ADR 0009)
: ck-why ( -- n ) ck-state ck-serial-why @ ;
\ Workers the pool ran with, and those it started without because the
\ host refused them (it then runs with those it made, lib/task.fs): 0
\ when it made all, and always on the serial host, which makes none.
: ck-made ( -- n ) ck-state ck-pool-made @ ;
: ck-lacked ( -- n ) ck-state ck-pool-lacked @ ;
: ck-jobs ( -- n ) ck-state ck-jobs-asked @ ;
: ck-parallel? ( -- flag ) ck-jobs 1 > ;
: ck-staged-names ( -- n ) ck-state ck-names# @ ;
: ck-input-declarations ( -- n ) ck-state ck-declarations# @ ;
: ck-input-terms ( -- n ) ck-state ck-terms# @ ;
: ck-input-levels ( -- n ) ck-state ck-levels# @ ;
: ck-input-references ( -- n ) ck-state ck-references# @ ;

\ ---- Clocks, in microseconds (doubles).
[defined] utime [defined] cputime and [if]
true constant ck-timed?
: ck-wall-now ( -- d ) utime ;
: ck-cpu-now ( -- d ) cputime d+ ;
[else]
false constant ck-timed?
: ck-wall-now ( -- d ) 0 0 ;
: ck-cpu-now ( -- d ) 0 0 ;
[then]
: ck-clock! ( clock -- ) >r ck-wall-now r@ clock-wall 2! ck-cpu-now r> clock-cpu 2! ;
\ The time since the mark at addr; 0, never negative, when the wall clock
\ (utime is gettimeofday, not monotonic) was set back in between, as
\ WSL's clock sync does several times a day.
: ck-since ( d addr -- d' ) 2@ d- 0 0 dmax ;
\ Clock gets the time since mark.
: ck-wall-lap ( mark clock -- ) >r clock-wall ck-wall-now rot ck-since r> clock-wall 2! ;
: ck-cpu-lap ( mark clock -- ) >r clock-cpu ck-cpu-now rot ck-since r> clock-cpu 2! ;
: ck-lap ( mark clock -- ) 2dup ck-wall-lap ck-cpu-lap ;
: ck-time ( k -- clock ) /ck-clock * ck-state ck-times + ;
: ck-phase-begin ( -- ) ck-state ck-phase-mark ck-clock! ;
: ck-clock-start ( -- ) ck-state ck-run-mark ck-clock! ;
\ Phase k took the time since ck-phase-begin; the run, since ck-start.
: ck-phase-end ( k -- ) ck-state ck-phase-mark swap ck-time ck-lap ;
: ck-finish ( -- ) ck-state ck-run-mark ck-total ck-time ck-lap ;
: ck-phase-wall ( k -- d ) ck-time clock-wall 2@ ;
: ck-phase-cpu ( k -- d ) ck-time clock-cpu 2@ ;
\ Phase k is in the report: every one but the save, which only when asked;
\ xt ( k -- ) run on each such phase in order.
: ck-save-tried? ( -- flag ) ck-state ck-save-tried @ ;
: ck-phase-shown? ( k -- flag ) ck-saving <> ck-save-tried? or ;
: ck-shown-phases ( xt -- )
  ck-phases 0 do i ck-phase-shown? if i over execute then loop drop ;
\ Parts of the check phase of a run with workers (see the header): the
\ clock gets the time since ck-sub-begin.
: ck-sub-begin ( -- ) ck-state ck-sub-mark ck-clock! ;
: ck-sub-end ( clock -- ) ck-state ck-sub-mark swap ck-lap ;
: ck-plan-clock ( -- clock ) ck-state ck-plan-time ;
: ck-run-clock ( -- clock ) ck-state ck-jobs-time ;
: ck-run-wall ( -- d ) ck-run-clock clock-wall 2@ ;
: ck-phase-name ( k -- c-addr u )
  case ck-staging of s" stage" endof ck-feeding of s" feed" endof
    ck-checking of s" check" endof ck-saving of s" save" endof s" total" rot endcase ;

\ ---- Peak resident memory: the VmHWM line of /proc/self/status, a
\ number of kB, in bytes; false where the host has no such file or line.
128 constant ck-line-room
create ck-line ck-line-room 2 + allot
: ck-hwm-key ( -- c-addr u ) s" VmHWM:" ;
: ck-blank? ( c-addr u -- flag )
  0= if drop false exit then 1 2dup s"  " compare 0= -rot s\" \t" compare 0= or ;
: ck-skip ( c-addr u -- c-addr' u' ) begin 2dup ck-blank? while 1 /string repeat ;
\ The number after the key: (u true) when digits follow the blanks.
: ck-kb ( c-addr u -- u true | false )
  ck-skip dup >r 0 0 2swap >number nip r> = if 2drop false else drop true then ;
\ The number of kB on a line that begins with the key.
: ck-key-kb ( c-addr u key-addr key-u -- u true | false )
  2>r dup r@ < if 2drop 2r> 2drop false exit then
  over r@ 2r@ compare if 2drop 2r> 2drop false exit then
  2r> nip /string ck-kb ;
: ck-line-read ( fid -- u more? )
  ck-line ck-line-room rot read-line if 2drop 0 false then ;
: ck-key-scan ( fid key-addr key-u -- u true | false )
  2>r begin dup ck-line-read while
    ck-line swap 2r@ ck-key-kb if nip 2r> 2drop true exit then
  repeat 2drop 2r> 2drop false ;
: ck-status ( -- c-addr u ) s" /proc/self/status" ;
\ The kB of the status line with the key, in bytes.
: ck-status-bytes ( key-addr key-u -- u true | false )
  ck-status r/o open-file if drop 2drop false exit then
  dup >r -rot ck-key-scan r> close-file drop dup if swap 1024 * swap then ;
\ The process's peak resident memory, in bytes.
: ck-peak ( -- u true | false ) ck-hwm-key ck-status-bytes ;
\ Its resident memory now, in bytes.
: ck-resident ( -- u true | false ) s" VmRSS:" ck-status-bytes ;

\ ---- The engine: the program bin/leanforth ran (LEANFORTH_ENGINE, the
\ last part of its file name: gforth, or gforth-fast with --fast), empty
\ when it is not known (not run by bin/leanforth, or a host without
\ getenv). How the run was made, not what it found: reports keep it with
\ the times.
[defined] getenv [if]
: ck-engine ( -- c-addr u ) s" LEANFORTH_ENGINE" getenv ;
[else]
: ck-engine ( -- c-addr u ) 0 0 ;
[then]

\ ---- The kept steps: one record per declaration of the input, each
\ invalid until its step publishes.
: ck-kept ( d -- addr ) ck-state ck-steps slab-at ;
: ck-fuel-of ( d -- n ) ck-kept cks-fuel @ ;
: ck-unkept ( n -- )
  0 ?do i ck-kept dup /ck-step erase outcome-invalid swap kept-outcome ! loop ;
: ck-steps-init ( -- outcome ) /ck-step dup slab-limit-max ck-state ck-steps slab-init ;
: ck-steps-claim ( n -- outcome )
  dup ck-state ck-steps slab-claim ok-then? if drop ck-unkept outcome-ok else nip then ;
\ Room for n records: ok, or full.
: ck-steps-make ( n -- outcome ) ck-steps-init ok-then? if ck-steps-claim then ;

\ ---- Capacities: kept before the feed raises them, given back after.
: ck-capacity ( k -- row ) /ck-capacity * ck-capacities + ;
: ck-saved-cell ( k -- addr ) cells ck-state ck-saved + ;
: ck-save ( -- )
  ck-capacities# 0 do i ck-capacity capacity-get @ execute i ck-saved-cell ! loop ;
\ Give capacity k back; the first refusal stays.
: ck-give-back ( outcome k -- outcome )
  dup ck-saved-cell @ swap ck-capacity capacity-set @ execute outcome-and ;
: ck-restore ( -- outcome ) outcome-ok ck-capacities# 0 do i ck-give-back loop ;
\ Capacity k raised to the most a store may hold; the first refusal stays.
\ ck-rooms keeps them all and raises them, for a LeanForth text's words
\ (cli/check-lf.fs), which give them back with ck-restore before the feed
\ keeps them again.
: ck-raise ( outcome k -- outcome )
  feed-most swap ck-capacity capacity-set @ execute outcome-and ;
: ck-rooms ( -- outcome ) ck-save outcome-ok ck-capacities# 0 do i ck-raise loop ;
\ The stores emptied, as the feed starts them.
: ck-empty ( -- )
  lf-input-reset lf-term-reset lf-level-reset lf-cref-reset lf-lscope-context-reset ;

\ ---- Staging and feeding. The expression table is pre-sized from the
\ file: about 59 bytes per expression, half of the slots used.
29 constant ck-bytes-per-slot
12 constant ck-log2-least  28 constant ck-log2-most
: ck-size ( c-addr u -- ud )
  r/o bin open-file if drop 0 0 exit then
  dup >r file-size r> close-file drop if 2drop 0 0 then ;
: ck-slots ( ud -- u ) if drop max-n else 0 ck-bytes-per-slot um/mod nip then ;
: ck-log2 ( u -- log2 ) 1 max log2-ceiling ck-log2-least max ck-log2-most min ;
: ck-read ( c-addr u checked? -- outcome )
  if ck-stage stage-load else ck-stage stage-load-unchecked then ;
\ Whether the export may be of any Lean version, only its format pinned
\ (--any-lean-version): set after ck-start, before ck-load.
: ck-any-version! ( flag -- ) ck-state ck-any-lean ! ;
: ck-any-version? ( -- flag ) ck-state ck-any-lean @ ;
\ An export checked against a snapshot (ck-snapshot-import) is read on
\ into the snapshot's tier, then sealed.
: ck-importing? ( -- flag ) ck-state ck-importing @ ;
\ A carry run (plan step 6.2.5c3; kernel/env-import.fs, "The carry
\ pass"): the snapshot is a base of an older verdict version inside the
\ window, so its results are carried where the steps since cannot reach
\ and the rest checked again. The import pass runs in a carry run of a
\ snapshot alone as with an export, over the snapshot's own declarations.
: ck-carrying? ( -- flag ) ck-state ck-snapped @ ck-snap snap-carry @ and ;
: ck-passing? ( -- flag ) ck-importing? ck-carrying? or ;
\ Not after a refused snapshot (ck-snapshot-import's outcome not ok).
: ck-continued ( c-addr u checked? -- outcome )
  ck-state ck-snap-bad @ if drop 2drop outcome-invalid exit then
  if ck-stage stage-continue else ck-stage stage-continue-unchecked then
  dup ok? if drop ck-stage stage-seal then ;
: ck-staged ( c-addr u checked? -- outcome )
  ck-importing? if ck-continued exit then
  >r 2dup ck-size ck-slots ck-log2 ck-stage stage-init
  dup ok? 0= if nip nip r> drop exit then drop
  ck-any-version? ck-stage stage-any-version! r> ck-read ;
\ Whether the staged export's metadata names another exporter or Lean
\ version (stage-meta-text gives what it names).
: ck-other-lean? ( -- flag ) ck-staged? ck-stage stage-other? and ;
\ The sealed stage without its loading aids (the export-index maps, which
\ the feed does not read), and its size and names.
: ck-stage-facts ( -- )
  ck-stage stage-unmap ck-stage stage-allocated ck-state ck-stage-bytes !
  ck-stage stage-tier tier-names cons-numbers ck-state ck-names# ! ;
\ The terms: the input's term numbers, those read in place from the
\ stage (core/terms.fs) and the store's (the feed's copies).
: ck-input-facts ( -- )
  lf-input-count ck-state ck-declarations# !
  lf-term-base lf-term-count @ + ck-state ck-terms# !
  lf-level-count @ ck-state ck-levels# ! lf-cref-count @ ck-state ck-references# ! ;
\ The feed, after the capacities are kept: from here on the names are
\ attached to the stage (feed.fs's first step), whatever its outcome.
\ The feed's hooks (import/feed.fs, lf-feed-hooked), set after ck-start and
\ before ck-load by a caller that reads what the feed drops: print's
\ binder names and declaration lines (cli/print.fs).
: ck-hooks! ( binder-xt decl-xt -- ) ck-state ck-decl-hook ! ck-state ck-binder-hook ! ;
: ck-fed ( -- outcome )
  ck-save true ck-state ck-began-feed ! ck-stage ck-feeding-record
  ck-state ck-binder-hook @ ck-state ck-decl-hook @ lf-feed-hooked ;
\ The workers of a parallel check (plan task 7.3.1; kernel/env-schedule.fs),
\ made after the feed: each a new context with this context's switches,
\ fed by sharing this context's input (import/feed.fs's lf-feed-shared;
\ ADR 0016 S8): it reads this context's declarations, view tables and
\ references in place and keeps only its levels, its scratch, caches,
\ memos and marks; its input's fingerprint must be this context's (so the
\ run's environment is valid in it), and it gets the check's budget. So
\ this context must outlive the workers and make nothing in its input's
\ stores while they run: it publishes, and every check runs in a worker.
\ Making a worker gives full (no heap) or invalid (another fingerprint,
\ or an input that cannot be shared); every context made is freed with
\ the scheduler (ck-release, lf-sched-free).
: ck-switch ( k -- addr ) cells ck-switches + @ execute ;
: ck-switch-saved ( k -- addr ) cells ck-state ck-switched + ;
: ck-switched! ( -- ) ck-switches# 0 ?do i ck-switch @ i ck-switch-saved ! loop ;
: ck-switches! ( -- ) ck-switches# 0 ?do i ck-switch-saved @ i ck-switch ! loop ;
: ck-print! ( -- ) lf-input-fingerprint ck-state ck-print ! ck-switched! ;
: ck-worker-fed ( source -- outcome )
  ck-stage ck-worker-feed rot lf-feed-shared ck-worker-feed feed-free ;
: ck-worker-fill ( context -- outcome )
  lf-context @ swap context-use ck-switches! ck-worker-fed dup ok? 0= if exit then drop
  ck-fuel-budget lf-check-budget lf-input-fingerprint ck-state ck-print @ = flag>outcome ;
: ck-worker-filled ( context -- outcome )
  ['] ck-worker-fill context-catch ?dup if 2drop outcome-invalid then ;
\ A new worker, filled: (context 0), or (0 ior) with nothing kept: the
\ scheduler's maker too, for a worker replaced after a THROW.
: ck-worker-new ( -- context ior )
  context-new ?dup if exit then
  dup ck-worker-filled ok? if 0 exit then context-free drop 0 -1 ;
: ck-worker-add ( -- outcome )
  context-new if drop outcome-full exit then
  dup ck-worker-filled dup ok? 0= if swap context-free drop exit then drop
  dup lf-sched-add dup ok? if nip exit then swap context-free drop ;
\ Workers that cannot all be made -- no heap, or a context whose input's
\ fingerprint is not this context's (this context's stores were used
\ before, so their identities and generations moved on, as in a Forth
\ session's main context; bin/leanforth's never was) -- are all freed,
\ and the run checks one declaration at a time (ck-jobs-run?), as the
\ resource report then says: the same output, only slower.
: ck-worker-next ( k -- outcome ) drop ck-worker-add ;
: ck-workers-made ( -- outcome ) ck-jobs ['] ck-worker-next ok-each ;
\ The workers read this context's input in place; so that none reads a
\ block given back or a record made after they began, the input as the
\ workers began to read it is kept (ck-lent!: each part's block and
\ count) and, when it moved before the run (a pass that made references
\ here, as the import pass of a run against a snapshot may), the workers
\ are made again (ck-relent; ck-remades counts it). During the run this
\ context makes nothing there (the decision on readiness and the ticks
\ only read it, publish into the environment and roll their own scratch
\ back); that is checked after each (ck-shift?), and a run in which it
\ moved is stopped as a fault, its verdicts read only below the slots
\ final before the move (ck-final), never one a worker reached after it.
\ Each part's pair stored from addr on (/ck-lend bytes).
: ck-lend+ ( addr xt -- addr' ) swap >r execute r@ 2! r> 2 cells + ;
: ck-lent-part ( k -- xt ) cells ck-parts + @ ;
: ck-lending ( addr -- ) ck-parts# 0 ?do i ck-lent-part ck-lend+ loop drop ;
: ck-lent! ( -- ) ck-state ck-lent ck-lending ;
: ck-now ( -- addr ) ck-state ck-lend-now ;
: ck-moved? ( -- flag )
  ck-now dup ck-lending /ck-lend ck-state ck-lent /ck-lend compare 0<> ;
\ Each comparison that finds no change keeps the slots final then
\ (ck-clean-at); once one finds a change, the run is stopped as a fault at
\ the last such slots (ck-shifted-at): what became final since may come
\ from a check that read the changed input.
: ck-shifted? ( -- flag ) ck-state ck-shifted @ ;
: ck-clean! ( -- ) lf-sched-final ck-state ck-clean-at ! ;
: ck-clean@ ( -- n ) ck-state ck-clean-at @ ;
: ck-shifted-at! ( -- ) ck-clean@ ck-state ck-shifted-at ! ;
: ck-shifted! ( -- )
  true ck-state ck-shifted ! true ck-state ck-faulted ! ck-shifted-at! ;
: ck-look ( -- ) ck-moved? if ck-shifted! exit then ck-clean! ;
: ck-shift? ( -- flag ) ck-shifted? 0= if ck-look then ck-shifted? ;
\ What a stopped run's verdicts are read below: n, or the slots final
\ when the input moved.
: ck-final ( n -- n' ) ck-shifted? if ck-state ck-shifted-at @ min then ;
: ck-remades ( -- n ) ck-state ck-remade @ ;
: ck-workers ( -- )
  ck-parallel? 0= if exit then
  lf-sched-host-ok 0= if ck-why-host ck-state ck-serial-why ! exit then
  lf-sched-init ok? if ck-workers-made ok? if ck-lent! exit then then lf-sched-free ;
: ck-relent ( -- )
  lf-sched-workers 0> ck-moved? and 0= if exit then
  1 ck-state ck-remade +! lf-sched-free ck-workers ;
\ A failed phase is kept as the one that failed.
: ck-fail ( outcome phase -- outcome ) over ok? if drop else ck-state ck-failed ! then ;
\ Staging an export checked against a snapshot goes on in the phase that
\ loaded the snapshot (ck-snapshot-import), so the time is both's.
: ck-stage-phase ( c-addr u checked? -- outcome )
  ck-importing? 0= if ck-phase-begin then
  ck-staged ck-staging ck-phase-end ck-staging ck-fail ;
\ After an import's feed: the input as the import pass reads it.
: ck-import-input ( -- outcome )
  ck-passing? if ck-import imp-input else outcome-ok then ;
: ck-fed-all ( -- outcome )
  ck-fed dup ok? if drop ck-import-input then dup ok? if ck-print! ck-workers then ;
: ck-feed-phase ( -- outcome )
  ck-phase-begin ck-fed-all ck-feeding ck-phase-end ck-feeding ck-fail ;
\ Stage and feed the export c-addr u (see the header).
: ck-loading ( c-addr u checked? -- outcome )
  ck-stage-phase dup ok? 0= if exit then drop ck-stage-facts
  ck-feed-phase dup ok? if ck-input-facts then ;
: ck-export! ( c-addr u checked? -- c-addr u checked? )
  dup ck-state ck-checked-read ! >r 2dup ck-state ck-export 2! r> ;
: ck-load ( c-addr u checked? -- outcome ) ck-export! ck-loading dup ck-state ck-loaded !
  ;

\ ---- Fuel used (see the header). Step 4 of check-declaration, the
\ declared type's type, is the first that runs inference.
4 constant ck-inference-step
: ck-block-left ( d -- n )
  lf-ind-first@ = lf-block-step@ 0> and if lf-ind-fuel @ else ck-fuel-budget then ;
\ A quotient record runs no inference: its steps all use the audit's.
: ck-quot? ( d -- flag ) lf-input-decl lf-idecl-kind @ lf-kind-quotient = ;
: ck-decl-left ( d -- n )
  ck-quot? lf-check-step@ ck-inference-step < or
  if lf-check-left @ else lf-minfer-fuel @ then ;
: ck-member? ( d -- flag ) lf-input-decl lf-ind-member? ;
: ck-left ( d -- n ) dup ck-member? if ck-block-left else ck-decl-left then ;
\ No fuel left by a check that failed without running out: a failure gave
\ the counter up (an accepted one used exactly its budget).
: ck-ran-out? ( outcome -- flag ) dup ok? swap outcome-exhausted = or ;
: ck-gave-up? ( outcome left -- flag ) 0= swap ck-ran-out? 0= and ;
: ck-left-used ( outcome d -- n )
  ck-left tuck ck-gave-up? if drop ck-fuel-unknown else ck-fuel-budget swap - 0 max then ;
\ A block member after the first counts no fuel of its own.
: ck-later-member? ( d -- flag ) dup ck-member? swap lf-ind-first@ <> and ;
\ An exhausted check used its whole budget, whichever counter ran out:
\ one that ran out in step 1 (lf-cterm-check) spent none of the counters
\ ck-left reads (review B1, 2026-11-18).
: ck-spent-all? ( outcome d -- flag ) ck-later-member? 0= swap outcome-exhausted = and ;
: ck-used ( outcome d -- n )
  2dup ck-spent-all? if 2drop ck-fuel-budget else ck-left-used then ;
: ck-step-reached ( d -- step ) ck-member? if lf-block-step@ else lf-check-step@ then ;

\ ---- Checking, one declaration at a time.
: ck-diag! ( addr -- )
  >r lf-diag@ r@ kept-code ! r@ kept-site ! r@ kept-second ! r> kept-first ! ;
\ Keep what declaration d's check left, with the outcome it published;
\ in a carry run, whether d (and its block) answers as the snapshot's
\ slot it was judged against (env-import.fs imp-same, I3).
: ck-keep-facts ( outcome d -- )
  2dup ck-used over ck-kept cks-fuel ! dup ck-step-reached over ck-kept kept-step !
  ck-kept dup ck-diag! kept-outcome ! ;
\ A carry run that checks what it does not carry; with --snapshot-stale-ok
\ that rest is published from the snapshot instead (stale), so no slot is
\ checked here and none may answer as a saved one (review of snap-compat
\ M1: a stale slot compared with itself would let its users be carried).
: ck-rechecking? ( -- flag ) ck-carrying? snap-stale-allowed @ 0= and ;
: ck-same ( d -- ) ck-rechecking? if ck-import imp-same else drop then ;
: ck-keep ( outcome d -- ) dup ck-same ck-keep-facts ;
\ Check declaration d: whether the run must stop, after a fault of the
\ publisher or a THROW in the check (the context is then spent); a stop
\ is kept (ck-faulted?).
: ck-stop! ( stop? -- stop? ) dup if true ck-state ck-faulted ! then ;
\ The check word ( -- ): lf-check-declaration, which ck-start sets; a
\ test may set another after ck-start (ck-check-word!), such as one that
\ throws for a chosen declaration.
: ck-check-word ( -- xt ) ck-state ck-checker @ ;
: ck-check-word! ( xt -- ) ck-state ck-checker ! ;
: ck-step ( d -- stop? )
  dup >r ck-check-word swap lf-env-step swap r> ck-keep lf-env-spent? or ck-stop! ;
\ A member after its block's first, published with it: the first's facts,
\ no fuel of its own.
: ck-first-member ( d -- first )
  lf-input-decl lf-idecl-header lf-hdr-first lf-more-field ;
: ck-trailing ( d -- )
  dup ck-first-member ck-kept over ck-kept /ck-step move 0 swap ck-kept cks-fuel ! ;
\ A declaration taken from a snapshot before the run (ck-import-pass): its
\ slot is final, its facts the snapshot's.
: ck-taken? ( d -- flag )
  ck-passing? if ck-import imp-source 0< 0= else drop false then ;
\ A carry run's declaration not taken before the run for its answers is
\ judged again on its turn (plan step 6.2.5c4; env-import.fs imp-decide):
\ taken now, with its block, their facts the snapshot's (ck-span-facts);
\ a failure to take stops the run. ck-pre is the same decision before a
\ parallel run hands d out (env-schedule.fs lf-sched-pre!).
: ck-deferred? ( d -- flag )
  ck-rechecking? if dup lf-env-published? 0= swap ck-import imp-deferred? and
  else drop false then ;
: ck-fact-of ( k -- )
  dup ck-import imp-source over ck-kept snap-fact swap ck-kept cks-fuel ! ;
: ck-span-facts ( d -- ) begin dup ck-fact-of 1+ dup member-here? 0= until drop ;
: ck-turn ( d -- stop? )
  dup ck-deferred? 0= if drop false exit then
  dup ck-import imp-decide 1 = if drop ck-span-facts false exit then ok? 0= nip ck-stop! ;
\ A failure to take stops the parallel run at d, as the serial run stops
\ there (the hook's answer 3; review of snap-compat L4).
: ck-pre-failed ( d outcome -- n ) 2drop true ck-state ck-faulted ! 3 ;
: ck-pre ( d -- n )
  dup ck-deferred? 0= if drop 0 exit then
  dup ck-import imp-decide over ok? 0= if drop ck-pre-failed exit then
  nip dup 1 = if drop ck-span-facts 1 else nip then ;
\ The decision a parallel run asks before handing d out: ck-pre, which
\ ck-start sets; a test may set another after ck-start.
: ck-pre-word! ( xt -- ) ck-state ck-pre-xt ! ;
: ck-next ( d -- stop? )
  dup 1+ ck-state ck-stepped ! dup ck-turn if drop true exit then
  dup ck-taken? if drop false exit then
  dup lf-env-published? if ck-trailing false else ck-step then ;

\ The run's own environment, by identity (never another one that happens
\ to be current), and a snapshot of every slot of it.
: ck-ours? ( -- flag ) ck-state ck-env-id @ lf-env-is? ;
: ck-viewed? ( -- flag ) ck-state ck-env-id @ lf-env-viewed? ;
\ Ok when every slot is final and the run did not stop on a fault.
: ck-confirm ( -- outcome )
  ck-viewed? 0= if outcome-invalid exit then
  lf-env-all-final? ck-faulted? 0= and flag>outcome ;
\ After the run: whether its verdicts can be read, in a new snapshot of
\ the run's own environment.
: ck-verdicts? ( -- flag ) ck-ours? if lf-env-view ok? else false then ;
\ Whether a run whose verdicts can be read stopped short: a fault stopped
\ it (a check threw, or publishing failed), or it did not end ok (a slot
\ left open). The one word both reports read; false when no verdict can
\ be read.
: ck-stopped? ( -- flag )
  ck-verdicts? if ck-faulted? ck-outcome ok? 0= or else false then ;
\ A new environment for the run, current: ok, or why not; one that
\ cannot be made current is freed at once.
: ck-own ( env -- ) lf-envh-identity @ ck-state ck-env-id ! true ck-state ck-checked ! ;
: ck-unusable ( env outcome -- outcome ) swap lf-env-free drop 0 ck-state ck-env-id ! ;
\ The run's environment freed while it is ours (ck-release, a refused
\ snapshot).
: ck-env-free ( -- ) ck-ours? if lf-env lf-env-free drop then 0 ck-state ck-env-id ! ;
\ A run of a loaded snapshot (ck-snapshot-load) is a development run (ADR
\ 0012 E8, ADR 0020 D4).
: ck-snapped? ( -- flag ) ck-state ck-snapped @ ;
: ck-develop ( env -- ) ck-snapped? if lf-env-develop else drop then ;
: ck-env ( -- outcome )
  ck-fuel-budget lf-check-budget lf-env-pool-start lf-env-new ok-then? 0= if exit then
  dup ck-develop dup ck-own dup lf-env-use dup ok? if nip else ck-unusable then ;

\ ---- The fuel used in all, and the declarations that used the most,
\ most first, those of equal fuel in file order; none that used none or
\ an amount not known.
: ck-top-cell ( k -- addr ) cells ck-state ck-top + ;
: ck-top@ ( k -- d ) ck-top-cell @ ;
: ck-tops ( -- n ) ck-state ck-top-count @ ;
\ The first place whose declaration used less than fuel.
: ck-rank ( fuel -- k )
  ck-tops 0 ?do dup i ck-top@ ck-fuel-of > if drop i unloop exit then loop drop ck-tops ;
\ Places k and on move down one; the last falls off a full list.
: ck-shift ( k -- )
  ck-tops 1+ ck-top-room min dup ck-state ck-top-count !
  1- begin 2dup < while dup 1- ck-top@ over ck-top-cell ! 1- repeat 2drop ;
: ck-offer ( d -- )
  dup ck-fuel-of dup 0> 0= if 2drop exit then ck-rank
  dup ck-top-room < if dup ck-shift ck-top-cell ! else 2drop then ;
: ck-add ( d -- )
  ck-fuel-of dup 0< if drop 1 ck-state ck-unknowns +! exit then
  ck-state ck-fuel-sum 2@ rot m+ ck-state ck-fuel-sum 2! ;
: ck-tally ( -- ) lf-input-count 0 ?do i ck-add i ck-offer loop ;

\ ---- Progress lines and results kept as the run goes. Declarations are
\ given out in file order, each once final (the serial run: as its step
\ ends; the parallel one: below the scheduler's frontier, after each job):
\ ck-advance ( n -- ) gives out those below n, counting each one's outcome
\ (accepted or other) and passing it to the line word (ck-lines!), which
\ writes its line and gives true, or gives false for a declaration whose
\ line needs the finished environment (a NOT PROVED one: the axiom
\ dependencies are tabulated once, over all slots); from there on the run
\ writes no line and the report writes the rest; then flushes stdout when 2000 lines or ten seconds (the
\ progress interval, if less) have passed since, so that a stopped run
\ keeps the lines of every declaration up to its last flush; and writes
\ a progress line on stderr when the interval (ck-progress!) has passed
\ since the last one. Nothing is done unless one of the two is set, and
\ neither changes a verdict, a fuel or the output a finished run has.
\ A parallel run's stopping rule (a THROW) is the scheduler's: nothing at
\ or beyond lf-sched-stop is given out while it runs (lf-sched-final), and
\ the stop is lowered at the faulting declaration's hand-over, before the
\ frontier can pass its slot, so the lines written are always a prefix of
\ the serial run's; the faulting declaration's own line is written by the
\ report (cli-verdicts), as the serial run's is, and nothing after it.
: ck-marks! ( -- ) ck-wall-now 2dup ck-state ck-prog-mark 2! ck-state ck-flush-mark 2! ;
: ck-lines! ( xt -- ) ck-state ck-line-xt ! ck-marks! ;
: ck-progress! ( seconds -- )
  ck-state ck-prog-secs ! true ck-state ck-prog-on ! ck-marks! ;
: ck-done ( -- n ) ck-state ck-cursor @ ;
: ck-lines-on? ( -- flag ) ck-state ck-line-xt @ 0<> ;
: ck-watching? ( -- flag ) ck-lines-on? ck-state ck-prog-on @ or ;
: ck-jobs-run? ( -- flag ) ck-parallel? lf-sched-workers 0> and ;
: ck-jobs-trail ( d -- )
  dup ck-taken? if drop exit then
  dup lf-env-published? over lf-sched-checked? 0= and if ck-trailing else drop then ;
: ck-counted ( d -- )
  ck-kept kept-outcome @ ok? if ck-state ck-accepted else ck-state ck-others then
  1 swap +! ;
: ck-lined ( d -- )
  ck-lines-on? 0= if drop exit then
  ck-state ck-line-xt @ execute if 1 ck-state ck-unflushed +! else 0 ck-state ck-line-xt ! then ;
: ck-take ( d -- )
  ck-jobs-run? if dup ck-jobs-trail then dup ck-counted ck-lined 1 ck-state ck-cursor +! ;
\ Whether secs seconds have passed since the wall time kept at addr.
: ck-after? ( secs addr -- flag )
  >r 1000000 m* ck-wall-now r> ck-since 2swap d< 0= ;
10 constant ck-flush-secs  2000 constant ck-flush-lines
: ck-flush-secs@ ( -- secs )
  ck-flush-secs ck-state ck-prog-on @ if ck-state ck-prog-secs @ min then ;
: ck-flush-due? ( -- flag )
  ck-state ck-unflushed @ ?dup 0= if false exit then
  ck-flush-lines < 0= if true exit then
  ck-flush-secs@ ck-state ck-flush-mark ck-after? ;
: ck-flush ( -- )
  stdout flush-file drop 0 ck-state ck-unflushed !
  ck-wall-now ck-state ck-flush-mark 2! ;
\ The progress line, built in ck-pline (a cell-counted buffer: ck-pline#,
\ then its bytes): texts and decimal numbers, a piece that does not fit
\ dropped.
: ck-pl+ ( c-addr u -- ) ck-state ck-pline# ck-pline-room cell-counted+? drop ;
: ck-n+ ( u -- ) u>decimal ck-pl+ ;
: ck-elapsed-s ( -- s )
  ck-wall-now ck-state ck-run-mark clock-wall ck-since 1000000 um/mod nip ;
: ck-percent ( -- n ) ck-done 100 * lf-input-count 1 max / ;
: ck-rate ( -- n ) ck-done ck-elapsed-s 1 max / ;
\ The seconds still to go at the rate so far, rough: none before a first one.
: ck-eta ( -- s true | false )
  ck-done 0= if false exit then
  lf-input-count ck-done - 0 max ck-elapsed-s 1 max um* ck-done um/mod nip true ;
: ck-eta+ ( -- ) ck-eta if ck-n+ s"  s" else s" unknown" then ck-pl+ ;
: ck-resident+ ( -- )
  ck-resident if 1000000 / ck-n+ s"  MB" else s" ? MB" then ck-pl+ ;
\ Its parts after "progress: ", read-only (lib/name-table.fs): an entry
\ each, named by the text that follows the part, its data the word ( -- )
\ that adds the part, a number or a text.
: ck-elapsed+ ( -- ) ck-elapsed-s ck-n+ ;
: ck-done+ ( -- ) ck-done ck-n+ ;
: ck-count+ ( -- ) lf-input-count ck-n+ ;
: ck-percent+ ( -- ) ck-percent ck-n+ ;
: ck-accepted+ ( -- ) ck-state ck-accepted @ ck-n+ ;
: ck-others+ ( -- ) ck-state ck-others @ ck-n+ ;
: ck-rate+ ( -- ) ck-rate ck-n+ ;
name-table: ck-pline-parts
: ck-part, ( xt c-addr u -- ) ck-pline-parts name-entry , ;
' ck-elapsed+ s"  s elapsed; " ck-part,
' ck-done+ s" /" ck-part,
' ck-count+ s"  declarations final (" ck-part,
' ck-percent+ s" %); " ck-part,
' ck-accepted+ s"  accepted, " ck-part,
' ck-others+ s"  other; " ck-part,
' ck-rate+ s"  declarations/s; eta " ck-part,
' ck-eta+ s" ; resident " ck-part,
' ck-resident+ s" " ck-part,
: ck-part+ ( entry -- ) dup name-entry-data @ execute name-entry-name ck-pl+ ;
: ck-progress-line ( -- )
  0 ck-state ck-pline# ! s" progress: " ck-pl+
  ck-pline-parts ['] ck-part+ name-table-each s\" \n" ck-pl+ ;
\ Written to stderr, whatever stdout holds, and the interval started again.
: ck-report ( -- )
  ck-progress-line ck-state ck-pline ck-state ck-pline# @ stderr write-file drop
  ck-wall-now ck-state ck-prog-mark 2! ;
: ck-reported ( -- )
  ck-state ck-prog-on @ 0= if exit then
  ck-state ck-prog-secs @ ck-state ck-prog-mark ck-after? if ck-report then ;
\ Lines are written against the run's own environment: its snapshot taken.
: ck-ready? ( -- flag ) ck-lines-on? if ck-verdicts? else true then ;
: ck-give ( n -- ) ck-done ?do i ck-take loop ;
: ck-advance ( n -- )
  ck-watching? 0= over ck-done > 0= or if drop exit then
  ck-ready? 0= if drop exit then ck-give
  ck-flush-due? if ck-flush then ck-reported ;
\ After the run: what is left is given out, and one last progress line.
: ck-finished ( -- )
  ck-faulted? 0= if ck-steps-begun ck-advance then
  ck-state ck-prog-on @ if ck-report then ;
\ The parallel run's tick: the input checked before the lines are given
\ out and after them (ck-shift?), as the line word runs here too.
: ck-tick ( -- )
  ck-shift? drop lf-sched-final ck-final ck-advance ck-shift? drop ;
: ck-steps-run ( n -- ) 0 ?do i ck-next if unloop exit then i 1+ ck-advance loop ;

\ ---- The parallel run (--jobs; kernel/env-schedule.fs): the same checks,
\ each in a worker, kept by ck-keep in its worker's context after its
\ hand-over and rollback, as ck-step keeps a serial one. Then the facts
\ are made the serial run's: where the serial run would have stopped (a
\ THROW, a publisher's fault), the declarations after it are unkept and
\ the run stopped there; a block's members published with their first
\ take its facts. A run the scheduler could not finish (a job refused, no
\ worker left) stops at the first slot not final. A scheduler that cannot
\ make its plan (no heap) leaves the run to the serial one.
: ck-unkeep ( n -- ) lf-input-count swap ?do i ck-kept dup /ck-step erase
  outcome-invalid swap kept-outcome ! loop ;
: ck-jobs-reached ( -- n )
  lf-sched-stop lf-input-count < if lf-sched-stop 1+ exit then
  lf-sched-broken? if lf-sched-reached else lf-input-count then ;
: ck-jobs-stepped ( -- n ) ck-jobs-reached ck-final ;
: ck-jobs-facts ( -- )
  ck-jobs-stepped dup ck-state ck-stepped ! dup lf-input-count < ck-stop! drop
  dup 0 ?do i ck-jobs-trail loop ck-unkeep ;
\ A tick after each job checks the input and gives out what became final
\ (ck-advance); before each declaration is handed out the input is
\ checked, and once it moved every answer is a stop (3), so that no
\ worker starts a check after it.
: ck-guarded ( n -- n' ) ck-shift? if drop 3 then ;
: ck-pre-word ( -- xt ) ck-state ck-pre-xt @ ;
: ck-pre-guarded ( d -- n ) ck-shift? if drop 3 else ck-pre-word execute ck-guarded then ;
: ck-tick! ( -- ) ['] ck-tick lf-sched-tick! ;
: ck-pre! ( -- ) ['] ck-pre-guarded lf-sched-pre! ;
\ What each worker and the driving task spent in the jobs' run, in
\ microseconds: worker k's checks (lf-sched-busy) and the rest of the run
\ (waiting: no job to run); the driving task's wait for a job to end and
\ the rest (busy: handing out, publishing, rolling back, the ticks).
\ Never negative.
: ck-less ( d -- d' ) dnegate ck-run-wall d+ 0 0 dmax ;
: ck-waiting ( k -- d ) lf-sched-busy ck-less ;
: ck-busy-all ( -- d ) 0 0 lf-sched-workers 0 ?do i lf-sched-busy d+ loop ;
: ck-waiting-all ( -- d ) 0 0 lf-sched-workers 0 ?do i ck-waiting d+ loop ;
: ck-driver-waiting ( -- d ) lf-sched-waited ;
: ck-driver-busy ( -- d ) ck-driver-waiting ck-less ;
\ The plan and the jobs' run timed; the scheduler given the clock.
: ck-planned ( -- outcome ) ck-sub-begin lf-sched-plan ck-state ck-plan-time ck-sub-end ;
: ck-sched-words! ( -- ) ck-tick! ck-pre! ['] ck-wall-now lf-sched-clock! ;
: ck-sched-run ( -- )
  ck-check-word ['] ck-keep ['] ck-worker-new ['] lf-sched-run context-catch throw ;
: ck-sched-timed ( -- ) ck-sub-begin ck-sched-run ck-state ck-jobs-time ck-sub-end ;
: ck-jobs-run ( -- ) ck-sched-words! ck-sched-timed ck-jobs-facts ;
\ The pool is started before the run, so that a refusal (no threads, as
\ near the process limit) leaves the whole run to the serial one, with the
\ workers freed and the cause kept for the report. A pool the host made
\ only some workers of runs the checks on those; the shortfall is kept.
: ck-lacked! ( -- )
  workers-running dup ck-state ck-pool-made ! pool-size swap - ck-state ck-pool-lacked ! ;
: ck-pool-started? ( -- flag )
  lf-sched-pool-start ?dup if ck-state ck-serial-why ! lf-sched-free false exit then
  ck-lacked! true ;
: ck-steps-any ( n -- )
  ck-relent ck-jobs-run? if ck-planned ok? if ck-pool-started? if
    drop ck-jobs-run ck-finished exit then then then
  ck-steps-run ck-finished ;

\ Check every declaration (see the header): the facts, the environment,
\ the run.
: ck-facts ( -- outcome ) lf-input-count ck-steps-make dup ok? ck-state ck-facts-made ! ;
\ After a snapshot's run: every slot as saved (snap-same?), and each
\ declaration's fuel and diagnostic the saved ones; else the snapshot is
\ refused as if loading had failed, and the run stopped.
: ck-snap-facts ( -- ) lf-input-count 0 ?do i dup ck-kept snap-fact i ck-kept cks-fuel !
  loop ;
\ A refused snapshot leaves no verdict to read: its environment is freed
\ (review rvSN3 M2).
: ck-snap-refused ( outcome -- )
  ck-state ck-loaded ! ck-staging ck-state ck-failed ! true ck-state ck-faulted !
  true ck-state ck-snap-bad ! ck-env-free ;
\ Only where every slot not taken was published from the snapshot
\ (snap-fill): a snapshot alone, not carried or carried with
\ --snapshot-stale-ok (the rest shown stale).
: ck-filled? ( -- flag )
  ck-snapped? ck-importing? 0= and ck-check-word ['] snap-fill = and ;
: ck-snap-after ( -- )
  ck-filled? 0= if exit then
  ck-snap snap-same? dup ok? if drop ck-snap-facts else ck-snap-refused then ;
\ An export checked against a snapshot: first the import pass
\ (kernel/env-import.fs), whose taken declarations keep the snapshot's
\ fuel and diagnostic; a pass that fails refuses the snapshot, the run
\ stopped before any check. True when the run goes on.
: ck-import-facts ( -- ) lf-input-count 0 ?do i ck-taken? if i ck-fact-of then loop ;
: ck-import-refused ( outcome -- )
  c" a slot taken from it was published otherwise" ck-import imp-k @ ck-snap snap-note
  ck-snap-refused ;
: ck-import-pass ( -- flag )
  ck-passing? 0= if true exit then
  ck-import imp-pass dup ok? if drop ck-import-facts true exit then
  ck-import-refused false ;
\ After a carry run's pass, before any check: the caller's word, which
\ says how many it carried and will check again (the owner, 2026-11-12).
: ck-carried! ( xt -- ) ck-state ck-carry-xt ! ;
: ck-carried. ( -- ) ck-carrying? if ck-state ck-carry-xt @ ?execute then ;
: ck-run-all ( -- outcome )
  ck-import-pass if ck-carried. lf-input-count ck-steps-any ck-snap-after then
  ck-confirm ck-tally ;
: ck-checking-run ( -- outcome )
  ck-facts dup ok? if drop ck-env then dup ok? if drop ck-run-all then ;
: ck-check ( -- ) ck-phase-begin ck-checking-run ck-outcome! ck-checking ck-phase-end ;

\ ---- Releasing (see the header): the environment while it is ours and
\ current, then the names detached before the stage they point into is
\ freed, the stores emptied and their capacities given back.
: ck-unfeed ( -- )
  ck-state ck-began-feed @ 0= if exit then
  lf-name-detach ck-empty ck-restore ck-state ck-restored-outcome !
  false ck-state ck-began-feed ! ;
: ck-release ( -- )
  lf-sched-free ck-env-free ck-unfeed ck-feeding-record dup feed-free /feed erase
  ck-worker-feed dup feed-free /feed erase ck-stage stage-free
  ck-state ck-steps slab-free ck-snap snap-close ck-snap snap-free ck-out snap-free
  ck-import imp-free ck-state ck-lay-ids heap-release ;
: ck-start ( fuel -- )
  ck-release ck-state /ck erase ck-state ck-budget ! -1 ck-state ck-failed !
  outcome-invalid dup ck-outcome! dup ck-state ck-loaded ! ck-state ck-snap-saved !
  ['] lf-check-declaration ck-check-word! ['] ck-pre ck-pre-word! ck-clock-start ;

\ ---- Snapshots (ADR 0020; plan task 6.2.5, step SN3; kernel/env-snapshot.fs).
\ ck-snapshot-save ( file-addr file-u info-addr info-u -- outcome ), after
\ ck-check and before ck-release, writes the run's snapshot to the file:
\ only after a run that ended ok, every slot final (else invalid); the
\ export's identity is the manifest check's digest and bytes, or, without
\ a manifest, the file hashed now; its manifest's bytes are read again.
\ ck-snapshot-load ( c-addr u fuel -- outcome ), after ck-start in place of
\ ck-load, loads the snapshot file (fuel per declaration, or -1 for the
\ snapshot's) into the stage, feeds it (one context: the run is serial)
\ and keeps the snapshot's fuel as the budget; ck-check then publishes its
\ slots (snap-fill) and compares them with it. Kept facts: ck-snapped?,
\ ck-snap-saved (the save's outcome). The snapshot record, ck-snap, is
\ freed by ck-release.
\ The export's SHA-256 and bytes, with its manifest checked as the manifest
\ check computed them; without, hashed here.
create ck-hash /sha256 allot
create ck-digest sha-digest-bytes allot
65536 constant ck-chunk
begin-structure /ck-file
  field: ckf-fid
  field: ckf-buf
  2 cells +field ckf-bytes
end-structure
create ck-file /ck-file allot
: ck-file-more ( -- u ior ) ck-file ckf-buf @ ck-chunk ck-file ckf-fid @ read-file ;
: ck-file-count ( u -- ) ck-file ckf-bytes 2@ rot m+ ck-file ckf-bytes 2! ;
: ck-file-hash ( -- outcome )
  begin ck-file-more ?dup if 2drop outcome-invalid exit then dup while
    ck-file ckf-buf @ over ck-hash sha256-update ck-file-count
  repeat drop outcome-ok ;
: ck-file-buffered ( -- outcome )
  ck-chunk allocate if drop outcome-full exit then ck-file ckf-buf !
  ck-file-hash ck-file ckf-buf @ free drop ;
: ck-sha-file ( c-addr u -- outcome )
  ck-file /ck-file erase ck-hash sha256-init
  r/o bin open-file if drop outcome-invalid exit then ck-file ckf-fid !
  ck-file-buffered ck-file ckf-fid @ close-file drop ck-digest ck-hash sha256-final ;
: ck-checked-digest ( -- addr bytes )
  ck-stage stage-manifest dup manifest-digest swap manifest-count 2@ d>s ;
: ck-export-sha ( -- addr bytes outcome )
  ck-state ck-checked-read @ if ck-checked-digest outcome-ok exit then
  ck-state ck-export 2@ ck-sha-file ck-digest ck-file ckf-bytes 2@ d>s rot ;
: ck-snap-flags ( -- u )
  ck-state ck-checked-read @ snap-enforced and ck-any-version? snap-any-lean and or
  ck-other-lean? snap-other and or ;
: ck-export-lines ( -- n ) ck-stage stage-export export-at @ ;
: ck-snap-export ( -- outcome )
  ck-export-sha ok-then2? 0= if exit then
  ck-export-lines ck-snap-flags ck-out snap-export! outcome-ok ;
\ The manifest's bytes, read again from the file the manifest check read
\ ("<export>.manifest.json"), and their SHA-256; none without a check.
create ck-manifest-path manifest-name-room 16 + allot
2variable ck-manifest-text
: ck-manifest-name ( -- c-addr u )
  ck-state ck-export 2@ manifest-name-room min ck-manifest-path swap 2dup 2>r move
  s" .manifest.json" 2r@ + swap move 2r> 14 + ;
: ck-whole ( fid -- addr u outcome )
  >r r@ file-size if r> drop 2drop 0 0 outcome-invalid exit then d>s
  dup 1 max allocate if r> drop 2drop 0 0 outcome-full exit then
  swap 2dup r> read-file nip if drop free drop 0 0 outcome-invalid exit then outcome-ok ;
: ck-manifest-read ( -- outcome )
  0 0 ck-manifest-text 2! ck-manifest-name r/o bin open-file if drop outcome-invalid exit
  then
  dup ck-whole >r ck-manifest-text 2! close-file drop r> ;
: ck-manifest-sha ( -- )
  ck-hash sha256-init ck-manifest-text 2@ ck-hash sha256-update ck-digest ck-hash
  sha256-final ;
: ck-snap-manifest ( -- outcome )
  ck-state ck-checked-read @ 0= if outcome-ok exit then
  ck-manifest-read dup ok? 0= if exit then drop ck-manifest-sha
  ck-digest ck-out snap-manifest-sha! ck-manifest-text 2@ ck-out snap-manifest!
  outcome-ok ;
: ck-manifest-free ( -- )
  ck-manifest-text 2@ drop ?dup if free drop then 0 0 ck-manifest-text 2! ;
\ A declaration's facts for the snapshot: its fuel used and kept step.
: ck-fact ( d -- fuel step ) dup ck-fuel-of swap ck-kept ;
\ A snapshot is written after a final run (a base), after an export
\ checked against a base alone (a layer of that base: ADR 0020 amendment
\ 1, F5; plan step SN4), or after a run of a base alone (the base written
\ again with this build's versions, plan step 6.2.5c5, R8: the upgrade of
\ an older one, its carried results marked taken); never after a run of
\ layers or one that shows results stale.
: ck-layers# ( -- n ) ck-state ck-layers @ ;
: ck-unstale? ( -- flag ) ck-snap snap-stale @ ck-carrying? ck-filled? and or 0= ;
\ An export checked against a snapshot of an older verdict version would
\ write a layer of this build's version on a base no build loads it on:
\ refused until plan step 6.2.5c7 (review of snap-compat L7).
: ck-carry-import? ( -- flag ) ck-importing? ck-carrying? and ;
: ck-save-kind? ( -- flag )
  ck-snapped? 0= ck-layers# 0= ck-unstale? and ck-carry-import? 0= and or ;
: ck-saveable? ( -- flag )
  ck-loaded? ck-outcome ok? and ck-stopped? 0= and ck-save-kind? and ;
\ A layer: what was not taken, numbered on from the base's.
: ck-layer-set ( -- outcome )
  ck-import imp-layer dup ok? 0= if exit then drop
  ck-snap snap-sum ck-import imp-firsts@ ck-out snap-layer-base!
  ck-import imp-layer-slots ck-out snap-layer-slots!
  ck-import imp-layer-decls ck-out snap-layer-decls! outcome-ok ;
\ An upgraded base names the export its snapshot names: the same
\ identity, flags and manifest (no export is read).
: ck-old-export ( -- )
  ck-snap snap-export-sha ck-snap snap-export-bytes ck-snap snap-export-lines
  ck-snap snap-flags ck-out snap-export!
  ck-snap snap-manifest-sha ck-out snap-manifest-sha! ;
: ck-old-manifest ( -- )
  ss-manifest ck-snap snap-block ss-manifest ck-snap snap-size ck-out snap-manifest! ;
: ck-export-id ( -- outcome )
  ck-snapped? ck-importing? 0= and if ck-old-export ck-old-manifest outcome-ok exit then
  ck-snap-export dup ok? 0= if exit then drop ck-snap-manifest ;
: ck-snap-prepared ( info-addr info-u -- outcome )
  ck-out snap-begin ok-then2? 0= if exit then ck-out snap-info!
  ['] ck-fact ck-out snap-facts! ck-export-id dup ok? ck-importing? and
  if drop ck-layer-set then ;
: ck-snap-written ( file-addr file-u info-addr info-u -- outcome )
  ck-snap-prepared ok-then2? 0= if exit then
  ck-fuel-budget ck-stage ck-out snap-save ;
: ck-snapshot-saving ( file-addr file-u info-addr info-u -- outcome )
  ck-saveable? 0= if 2drop 2drop outcome-invalid else ck-snap-written then
  ck-out snap-free ck-manifest-free dup ck-state ck-snap-saved ! ;
: ck-snapshot-save ( file-addr file-u info-addr info-u -- outcome )
  true ck-state ck-save-tried ! ck-phase-begin ck-snapshot-saving ck-saving ck-phase-end ;
: ck-snap-saved@ ( -- outcome ) ck-state ck-snap-saved @ ;
\ Loading: the snapshot's header, its tier into the stage, its
\ environment's sections read (one slot per declaration but a block
\ record), each layer given loaded on it (kernel/env-layers.fs); then
\ for a snapshot alone the stage sealed and fed, or for an export the
\ import pass's aids kept (ck-snapshot-import).
create ck-firsts 8 cells allot   \ the base's tier counts, sections 1-8
create ck-lay /lay allot  ck-lay /lay erase   \ the layer being loaded
: ck-snap-read ( -- outcome )
  12 ck-stage stage-init dup ok? 0= if exit then drop
  ck-any-version? ck-stage stage-any-version! ck-stage ck-snap snap-tier ;
: ck-slot? ( stage k -- stage flag ) over staged-at over slot-record? ;
: ck-stage-slots ( -- n ) ck-stage dup stage-decls ['] ck-slot? count-index ;
: ck-firsts! ( -- )
  8 0 do i 1+ ck-stage tier-slab slab-count ck-firsts i cells + ! loop ;
\ The layers to load on the base, as (c-addr u) pairs (ck-layers!).
2variable ck-layer-names  0 0 ck-layer-names 2!
: ck-layers! ( addr n -- ) ck-layer-names 2! ;
: ck-layer@ ( k -- c-addr u ) 2* cells ck-layer-names 2@ drop + 2@ ;
\ Why a layer was refused, as the snapshot's refusal.
: ck-lay-why ( -- c-addr at )
  ck-lay lay-why @ ?dup if ck-lay lay-at @ exit then
  ck-lay lay-snap snap-why @ ?dup if ck-lay lay-snap snap-at @ exit then
  ck-lay lay-ly ly-why @ ?dup if ck-lay lay-ly ly-where @ exit then c" layer" -1 ;
: ck-lay-refused ( outcome -- outcome ) ck-lay-why ck-snap snap-note ;
\ Each layer loaded, for the reports (review rvSN4 M1): its header's
\ SHA-256, then its export's (sha-digest-bytes each), then its verdict
\ version (a cell, negated when stale: --snapshot-stale-ok); its base is
\ ck-snap's.
begin-structure /ck-layer-id
  sha-digest-bytes +field ck-lid-sum      \ the layer header's SHA-256
  sha-digest-bytes +field ck-lid-export   \ its export's
  field: ck-lid-verdict                   \ its verdict version, negated when stale
end-structure
: ck-layer-id ( k -- addr ) /ck-layer-id ck-state ck-lay-ids @ record-at ;
: ck-layer-verdict ( k -- n ) ck-layer-id ck-lid-verdict @ abs ;
: ck-layer-stale? ( k -- flag ) ck-layer-id ck-lid-verdict @ 0< ;
: ck-lay-version ( -- n )
  ck-lay lay-snap dup snap-verdict swap snap-stale @ if negate then ;
: ck-lay-kept ( k -- )
  ck-layer-id ck-lay lay-snap snap-sum over ck-lid-sum sha-digest-bytes move
  ck-lay lay-snap snap-export-sha over ck-lid-export sha-digest-bytes move
  ck-lay-version swap ck-lid-verdict ! ;
\ For an export (ck-importing?), a layer keeps a twin of a loaded
\ declaration whose lookups differ (env-layers.fs lay-twins).
: ck-layer ( sn names k -- sn names outcome )
  >r ck-stage ck-snap 2over ck-firsts ck-lay lay-init ck-importing? ck-lay lay-twins !
  r@ ck-layer@ ck-snap snap-fuel ck-lay lay-load
  dup ok? if r@ ck-lay-kept else ck-lay-refused then r> drop ck-lay lay-free ;
: ck-lay-ids-made ( -- outcome )
  ck-layer-names 2@ nip /ck-layer-id * 1 max allocate if drop outcome-full exit then
  ck-state ck-lay-ids ! outcome-ok ;
: ck-layer-loaded ( k -- outcome ) ck-layer dup ok? if 1 ck-state ck-layers +! then ;
: ck-layers-load ( -- outcome )
  ck-lay-ids-made dup ok? 0= if exit then drop
  ck-snap snap-n @ ck-stage stage-tier tier-names cons-numbers
  ck-layer-names 2@ nip ['] ck-layer-loaded ok-each nip nip ;
\ A base of an older verdict version inside the window is carried alone
\ or with an export; with layers (plan step 6.2.5c7), or with an export
\ and --snapshot-stale-ok, it is stale when that flag is given (every
\ result taken labelled stale), else refused (unsupported, "older base
\ with layers"; review of snap-compat L1).
: ck-uncarried? ( -- flag )
  ck-layer-names 2@ nip 0<> ck-importing? snap-stale-allowed @ and or ;
: ck-uncarried ( -- outcome )
  outcome-unsupported c" older base with layers" ck-snap snap-refuse ;
: ck-carry-or-stale ( -- outcome )
  ck-snap snap-carry @ ck-uncarried? and 0= if outcome-ok exit then
  snap-stale-allowed @ 0= if ck-uncarried exit then
  false ck-snap snap-carry ! true ck-snap snap-stale ! outcome-ok ;
: ck-snap-base ( -- outcome )
  ck-snap-read dup ok? 0= if exit then drop ck-firsts!
  ck-stage-slots ck-snap snap-read dup ok? 0= if exit then drop
  ck-carry-or-stale dup ok? 0= if exit then drop ck-layers-load ;
\ The snapshot's declarations kept aside for the import pass (imp-keep),
\ its carry pass set when it is of an older verdict version (imp-carry!).
: ck-older! ( -- )
  ck-snap snap-carry @ if ck-snap snap-verdict ck-import imp-carry! then ;
: ck-keep-aside ( -- outcome )
  ck-stage ck-import imp-keep dup ok? 0= if exit then drop ck-older!
  ck-import imp-sn@ ck-snap snap-n @ = flag>outcome ;
: ck-snap-tier ( -- outcome )
  ck-snap-base dup ok? 0= if exit then drop
  ck-carrying? if ck-keep-aside dup ok? 0= if exit then drop then ck-stage stage-seal ;
: ck-snap-opened ( c-addr u fuel xt -- outcome )
  >r ck-snap snap-open dup ok? 0= if r> drop exit then drop r> execute
  dup ok? if ck-snap snap-fuel ck-state ck-budget ! then ;
\ A refusal while loading is the snapshot's (ck-snap-bad?).
: ck-snap-fails ( outcome -- outcome )
  dup ok? 0= if true ck-state ck-snap-bad ! then ;
: ck-snap-phase ( c-addr u fuel -- outcome )
  ck-phase-begin ['] ck-snap-tier ck-snap-opened ck-snap-fails
  ck-staging ck-phase-end ck-staging ck-fail ;
\ After the feed: one slot read per input declaration, else the
\ snapshot is refused, as staging is.
: ck-snap-slots ( outcome -- outcome' )
  drop lf-input-count ck-snap snap-n @ = flag>outcome ck-snap-fails
  dup ok? 0= if c" slots" -1 ck-snap snap-note ck-staging ck-state ck-failed ! then ;
: ck-snap-file@ ( -- c-addr u ) ck-state ck-snap-file 2@ ;
: ck-snap-bad? ( -- flag ) ck-state ck-snap-bad @ ;
\ A run of a snapshot alone, no export read.
: ck-snap-only? ( -- flag ) ck-snapped? ck-importing? 0= and ;
: ck-snap-named ( c-addr u -- )
  ck-state ck-snap-file 2! true ck-state ck-snapped ! ck-snap snap-loading ! ;
\ Every slot is published from the snapshot (snap-fill), serially; but a
\ carry run checks what it does not carry, with the workers asked for,
\ unless --snapshot-stale-ok shows that rest stale instead.
: ck-jobs-back ( -- ) ck-state ck-jobs-kept @ ck-state ck-jobs-asked ! ;
: ck-filling ( -- )
  ck-rechecking? if ck-jobs-back else ['] snap-fill ck-check-word! then ;
\ A carry run of a snapshot alone after a step that changed the importer
\ (reach-reading; review of snap-compat M2): the snapshot's records are
\ the older build's reading of the export, so nothing is carried or
\ checked again from them: stale with --snapshot-stale-ok, else refused
\ (unsupported, "export reading": check the export, or check it against
\ the snapshot, whose import pass reads it again).
: ck-reread? ( -- flag )
  ck-carrying? ck-importing? 0= and if ck-import imp-rereads? else false then ;
: ck-unread ( -- outcome )
  outcome-unsupported c" export reading" ck-snap snap-refuse ck-snap-fails
  ck-staging ck-state ck-failed ! ;
: ck-reading ( -- outcome )
  ck-reread? 0= if outcome-ok exit then snap-stale-allowed @ 0= if ck-unread exit then
  false ck-snap snap-carry ! true ck-snap snap-stale ! outcome-ok ;
\ After the snapshot's phase: the reading, then the stage fed.
: ck-snap-rest ( -- outcome )
  ck-reading dup ok? 0= if exit then drop ck-filling ck-stage-facts
  ck-feed-phase dup ok? if ck-input-facts ck-snap-slots then ;
: ck-snapshot-load ( c-addr u fuel -- outcome )
  >r 2dup ck-snap-named r> ck-jobs ck-state ck-jobs-kept ! 0 ck-state ck-jobs-asked !
  ck-snap-phase dup ok? if drop ck-snap-rest then dup ck-state ck-loaded ! ;

\ ---- An export checked against a snapshot (ADR 0020 D5; plan step SN4;
\ kernel/env-import.fs). ck-snapshot-import ( c-addr u fuel -- outcome ),
\ after ck-start in place of ck-snapshot-load: the snapshot file c-addr u
\ opened (fuel as there), its tier read into the stage, its environment's
\ sections read and checked, its layers loaded (ck-layers!), the
\ declarations of them all kept aside (imp-keep); a refusal is the
\ snapshot's (ck-snap-bad?), and the staging phase goes on until ck-load
\ reads the export on into the tier (ck-continued), seals and feeds it,
\ after which the input is given to the import pass (ck-import-input).
\ ck-check then runs the pass first (ck-import-pass) and checks the rest,
\ in parallel with --jobs. Kept: ck-importing?, ck-layers#, and in
\ ck-import the counts.
: ck-snap-kept ( -- outcome ) ck-snap-base dup ok? 0= if exit then drop ck-keep-aside ;
: ck-snapshot-import ( c-addr u fuel -- outcome )
  >r 2dup ck-snap-named r> true ck-state ck-importing ! ck-phase-begin
  ['] ck-snap-kept ck-snap-opened ck-snap-fails
  dup ok? 0= if ck-staging ck-phase-end ck-staging ck-fail dup ck-state ck-loaded ! then ;
: ck-taken# ( -- n ) ck-import imp-taken# ;
\ Whether a snapshot loaded (the base or a layer) is stale: of an older
\ verdict version, which --snapshot-stale-ok let load (env-snapshot.fs
\ snap-stale-allowed); its results are then reported as stale.
\ In a carry run with --snapshot-stale-ok, what is not carried is stale.
: ck-stale? ( -- flag )
  ck-snapped? 0= if false exit then
  ck-snap snap-stale @ ck-carrying? ck-filled? and or
  ck-layers# 0 ?do i ck-layer-stale? or loop ;
\ A carry run (plan step 6.2.5c3): d carried, its result of the snapshot's
\ older verdict version taken because this build's changes since cannot
\ affect it; how many; why d was checked again (env-import.fs imp-reason,
\ 0 for none); how many were checked again for one why.
: ck-carried? ( d -- flag ) ck-carrying? if ck-taken? else drop false then ;
: ck-carried# ( -- n ) ck-carrying? if ck-taken# else 0 then ;
: ck-reason ( d -- why ) ck-carrying? if ck-import imp-reason else drop 0 then ;
: ck-again-for? ( why d -- why flag ) ck-reason over = ;
: ck-again# ( why -- n ) lf-input-count ['] ck-again-for? count-index ;
\ How many input declarations pass xt ( d -- flag ); none before verdicts.
: ck-inputs-passing# ( xt -- n )
  ck-verdicts? 0= if drop 0 exit then >r 0 lf-input-count r> count-index ;
\ Declarations checked in an import run (an export checked against a
\ snapshot): final, not taken from the snapshot (a stopped run checked
\ fewer than it did not take; review rvSN4 m3). Outside an import run
\ nothing is taken, so every final slot counts, also of a snapshot read
\ alone; its readers, cli-import. and cj-import, print it only while
\ importing (plan 9.4.8l AM).
: ck-fresh? ( d -- flag ) dup lf-env-final? swap ck-taken? 0= and ;
: ck-checked# ( -- n ) ['] ck-fresh? ck-inputs-passing# ;
\ Verdicts taken from the snapshot (and its layers), not checked here.
: ck-saved? ( d -- flag ) lf-env-origin lf-origin-saved = ;
: ck-saved# ( -- n ) ['] ck-saved? ck-inputs-passing# ;
: ck-other# ( -- n ) ck-import imp-other# ;
\ Results labelled stale: taken from the snapshot, not carried.
: ck-stale# ( -- n ) ck-verdicts? if ck-saved# ck-carried# - else 0 then ;

base !   \ the BASE this file was loaded with

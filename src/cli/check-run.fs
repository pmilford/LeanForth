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
\ - ck-load ( c-addr u checked? -- outcome ) stages the export file
\   c-addr u, its manifest checked when checked? is true, frees the
\   stage's loading aids (stage-unmap), then feeds it to this context's
\   input; the outcome is the stage's or the feed's, kept
\   (ck-read-outcome, ck-loaded?), and ck-phase-failed tells which phase
\   failed (ck-staging, ck-feeding), -1 for none; or, for an export that
\   does not open, ck-unopened instead (ck-opening);
\ - ck-check ( -- ) checks every declaration in a new environment, kept
\   current, with room for lf-env-pool-max dependencies (the kernel's
\   most); ck-outcome is then ok when every slot ended final and the run
\   did not stop, else the first failure: full when the facts
\   (ck-facts-made? false) or the environment (ck-made? false) found no
\   room, invalid when the environment could not be used or the run
\   stopped on a fault (ck-faulted?: a check threw, which spends the
\   context, or publishing failed; ck-steps-begun tells how far it came);
\   ck-stopped?, which the text and JSON reports both read, is true when
\   the run's verdicts can be read and it stopped or did not end ok;
\ - ck-finish ( -- ) takes the run's total time so far (phase ck-total);
\ - then, before ck-release, the verdicts are read in a snapshot of the
\   run's own environment (ck-verdicts?, then lf-env-outcome), and the
\   facts with ck-kept (a run-record.fs /rr-step: outcome, diagnostic,
\   step; then the fuel), ck-fuel-of, ck-fuel-total, ck-fuel-unknowns,
\   ck-top@ (ck-tops of them), the times (ck-phase-wall, ck-phase-cpu,
\   ck-phase-name), ck-peak, ck-staged-bytes and the input's sizes;
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
\ (lf-check-left) up to step 3 of check-declaration, inference's
\ (lf-minfer-fuel) from step 4 on; a check that began no step used none.
\ So a declaration accepted with fuel used u is accepted with a budget of
\ u and exhausted with u - 1 (tests/cli/leanforth.fs and
\ test_leanforth.py check it), and one exhausted used the budget. A
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
\ /proc/self/status (Linux), where a host without that file reports none.
\ State: three shared globals, ck-stage (/stage), ck-feeding-record
\ (/feed) and ck-state (the run's facts and settings), not context
\ records, because they own heap blocks, as checker-input.fs's records
\ do: one run at a time, in any context, its input and environment
\ landing in the context current while it runs. The command line's own
\ options and counts are context records (cli/leanforth.fs, tally.fs).

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/slab.fs
require ../core/input.fs
require ../core/diagnostics.fs
require ../kernel/environment.fs
require ../kernel/env-publish.fs
require ../kernel/check-declaration.fs
require ../import/stage.fs
require ../import/feed.fs
require ../import/run-record.fs

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

\ A clock reading: wall and CPU time, doubles.
begin-structure /ck-clock
  2 cells +field clock-wall
  2 cells +field clock-cpu
end-structure
\ The phases timed: staging, feeding, checking, and the run's total.
0 constant ck-staging  1 constant ck-feeding  2 constant ck-checking  3 constant ck-total
4 constant ck-phases
\ Not a timed phase: the export did not open (ck-unopened).
ck-phases constant ck-opening
10 constant ck-top-room   \ declarations in the list of the most fuel used

begin-structure /ck
  field: ck-budget               \ fuel each check starts with
  field: ck-failed               \ the phase that failed, or -1
  field: ck-loaded               \ ck-load's outcome; invalid before it
  field: ck-run                  \ the run's outcome; invalid before ck-check
  field: ck-facts-made           \ true once the facts had room
  field: ck-checked              \ true once ck-check made its environment
  field: ck-env-id               \ the run's environment's identity, or 0
  field: ck-stepped              \ declarations whose check began
  field: ck-faulted              \ true when the run stopped on a fault
  field: ck-began-feed           \ true once the feed began: names attached
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
  /ck-clock +field ck-run-mark             \ and when the run began
  ck-phases /ck-clock * +field ck-times    \ each phase's time
  /slab +field ck-steps          \ the kept steps, /ck-step each
end-structure
create ck-state /ck allot  ck-state /ck erase
create ck-stage /stage allot  ck-stage /stage erase
create ck-feeding-record /feed allot  ck-feeding-record /feed erase

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
: ck-since ( d addr -- d' ) 2@ d- ;
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
: ck-phase-name ( k -- c-addr u )
  case ck-staging of s" stage" endof ck-feeding of s" feed" endof
    ck-checking of s" check" endof s" total" rot endcase ;

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
: ck-hwm? ( c-addr u -- u true | false )
  dup ck-hwm-key nip < if 2drop false exit then
  over ck-hwm-key nip ck-hwm-key compare if 2drop false exit then
  ck-hwm-key nip /string ck-kb ;
: ck-line-read ( fid -- u more? )
  ck-line ck-line-room rot read-line if 2drop 0 false then ;
: ck-hwm-scan ( fid -- u true | false )
  begin dup ck-line-read while ck-line swap ck-hwm? if nip true exit then repeat
  2drop false ;
: ck-status ( -- c-addr u ) s" /proc/self/status" ;
\ The process's peak resident memory, in bytes.
: ck-peak ( -- u true | false )
  ck-status r/o open-file if drop false exit then
  dup >r ck-hwm-scan r> close-file drop dup if swap 1024 * swap then ;

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
: ck-first ( outcome outcome2 -- outcome' ) over ok? if nip else drop then ;
: ck-give-back ( outcome k -- outcome )
  dup ck-saved-cell @ swap ck-capacity capacity-set @ execute ck-first ;
: ck-restore ( -- outcome ) outcome-ok ck-capacities# 0 do i ck-give-back loop ;
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
: ck-log2 ( u -- log2 )
  ck-log2-least begin 2dup 1 swap lshift u> over ck-log2-most < and while 1+ repeat nip ;
: ck-read ( c-addr u checked? -- outcome )
  if ck-stage stage-load else ck-stage stage-load-unchecked then ;
: ck-staged ( c-addr u checked? -- outcome )
  >r 2dup ck-size ck-slots ck-log2 ck-stage stage-init
  dup ok? 0= if nip nip r> drop exit then drop r> ck-read ;
\ The sealed stage without its loading aids (the export-index maps, which
\ the feed does not read), and its size and names.
: ck-stage-facts ( -- )
  ck-stage stage-unmap ck-stage stage-allocated ck-state ck-stage-bytes !
  ck-stage stage-tier tier-names cons-numbers ck-state ck-names# ! ;
: ck-input-facts ( -- )
  lf-input-count ck-state ck-declarations# ! lf-term-count @ ck-state ck-terms# !
  lf-level-count @ ck-state ck-levels# ! lf-cref-count @ ck-state ck-references# ! ;
\ The feed, after the capacities are kept: from here on the names are
\ attached to the stage (feed.fs's first step), whatever its outcome.
: ck-fed ( -- outcome )
  ck-save true ck-state ck-began-feed ! ck-stage ck-feeding-record lf-feed ;
\ A failed phase is kept as the one that failed.
: ck-fail ( outcome phase -- outcome ) over ok? if drop else ck-state ck-failed ! then ;
: ck-stage-phase ( c-addr u checked? -- outcome )
  ck-phase-begin ck-staged ck-staging ck-phase-end ck-staging ck-fail ;
: ck-feed-phase ( -- outcome )
  ck-phase-begin ck-fed ck-feeding ck-phase-end ck-feeding ck-fail ;
\ Stage and feed the export c-addr u (see the header).
: ck-loading ( c-addr u checked? -- outcome )
  ck-stage-phase dup ok? 0= if exit then drop ck-stage-facts
  ck-feed-phase dup ok? if ck-input-facts then ;
: ck-load ( c-addr u checked? -- outcome ) ck-loading dup ck-state ck-loaded ! ;

\ ---- Fuel used (see the header). Step 4 of check-declaration, the
\ declared type's type, is the first that runs inference.
4 constant ck-inference-step
: ck-block-left ( d -- n )
  lf-ind-first@ = lf-block-step@ 0> and if lf-ind-fuel @ else ck-fuel-budget then ;
: ck-decl-left ( -- n )
  lf-check-step@ ck-inference-step < if lf-check-left @ else lf-minfer-fuel @ then ;
: ck-member? ( d -- flag ) lf-input-decl lf-ind-member? ;
: ck-left ( d -- n ) dup ck-member? if ck-block-left else drop ck-decl-left then ;
\ No fuel left by a check that failed without running out: a failure gave
\ the counter up (an accepted one used exactly its budget).
: ck-ran-out? ( outcome -- flag ) dup ok? swap outcome-exhausted = or ;
: ck-gave-up? ( outcome left -- flag ) 0= swap ck-ran-out? 0= and ;
: ck-used ( outcome d -- n )
  ck-left tuck ck-gave-up? if drop ck-fuel-unknown else ck-fuel-budget swap - 0 max then ;
: ck-step-reached ( d -- step ) ck-member? if lf-block-step@ else lf-check-step@ then ;

\ ---- Checking, one declaration at a time.
: ck-diag! ( addr -- )
  >r lf-diag@ r@ kept-code ! r@ kept-site ! r@ kept-second ! r> kept-first ! ;
\ Keep what declaration d's check left, with the outcome it published.
: ck-keep ( outcome d -- )
  2dup ck-used over ck-kept cks-fuel ! dup ck-step-reached over ck-kept kept-step !
  ck-kept dup ck-diag! kept-outcome ! ;
\ Check declaration d: whether the run must stop, after a fault of the
\ publisher or a THROW in the check (the context is then spent); a stop
\ is kept (ck-faulted?).
: ck-stop! ( stop? -- stop? ) dup if true ck-state ck-faulted ! then ;
: ck-step ( d -- stop? )
  dup >r ['] lf-check-declaration swap lf-env-step swap r> ck-keep lf-env-spent? or
  ck-stop! ;
\ A member after its block's first, published with it: the first's facts,
\ no fuel of its own.
: ck-first-member ( d -- first )
  lf-input-decl lf-idecl-header lf-hdr-first lf-more-field ;
: ck-trailing ( d -- )
  dup ck-first-member ck-kept over ck-kept /ck-step move 0 swap ck-kept cks-fuel ! ;
: ck-next ( d -- stop? )
  dup 1+ ck-state ck-stepped !
  dup lf-env-published? if ck-trailing false else ck-step then ;
: ck-steps-run ( n -- ) 0 ?do i ck-next if unloop exit then loop ;

\ The run's own environment, by identity (never another one that happens
\ to be current), and a snapshot of every slot of it.
: ck-ours? ( -- flag ) ck-state ck-env-id @ dup if lf-env-id = else drop false then ;
: ck-viewed? ( -- flag )
  ck-ours? if lf-env-view ok? lf-name-storage-valid? and else false then ;
: ck-final? ( d -- flag ) lf-env-readable dup if nip then ;
: ck-all-final? ( -- flag ) true lf-input-count 0 ?do i ck-final? and loop ;
\ Ok when every slot is final and the run did not stop on a fault.
: ck-confirm ( -- outcome )
  ck-viewed? if ck-all-final? ck-faulted? 0= and flag>outcome else outcome-invalid then ;
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
: ck-env ( -- outcome )
  ck-fuel-budget lf-check-budget lf-env-pool-max lf-env-new ok-then? 0= if exit then
  dup ck-own dup lf-env-use dup ok? if nip else ck-unusable then ;

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

\ Check every declaration (see the header): the facts, the environment,
\ the run.
: ck-facts ( -- outcome ) lf-input-count ck-steps-make dup ok? ck-state ck-facts-made ! ;
: ck-run-all ( -- outcome ) lf-input-count ck-steps-run ck-confirm ck-tally ;
: ck-checking-run ( -- outcome )
  ck-facts dup ok? if drop ck-env then dup ok? if drop ck-run-all then ;
: ck-check ( -- ) ck-phase-begin ck-checking-run ck-outcome! ck-checking ck-phase-end ;

\ ---- Releasing (see the header): the environment while it is ours and
\ current, then the names detached before the stage they point into is
\ freed, the stores emptied and their capacities given back.
: ck-env-free ( -- ) ck-ours? if lf-env lf-env-free drop then 0 ck-state ck-env-id ! ;
: ck-unfeed ( -- )
  ck-state ck-began-feed @ 0= if exit then
  lf-name-detach ck-empty ck-restore ck-state ck-restored-outcome !
  false ck-state ck-began-feed ! ;
: ck-release ( -- )
  ck-env-free ck-unfeed ck-feeding-record dup feed-free /feed erase ck-stage stage-free
  ck-state ck-steps slab-free ;
: ck-start ( fuel -- )
  ck-release ck-state /ck erase ck-state ck-budget ! -1 ck-state ck-failed !
  outcome-invalid dup ck-outcome! ck-state ck-loaded ! ck-clock-start ;

base !   \ the BASE this file was loaded with

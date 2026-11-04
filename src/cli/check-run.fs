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
\   c-addr u, its manifest checked when checked? is true, then feeds it
\   to this context's input; the outcome is the stage's or the feed's,
\   kept (ck-read-outcome, ck-loaded?), and ck-phase-failed tells which
\   phase failed (ck-staging, ck-feeding), -1 for none; or, for an export
\   that does not open, ck-unopened instead (ck-opening);
\ - ck-check ( -- ) checks every declaration in a new environment, kept
\   current, with room for lf-env-pool-max dependencies (the kernel's
\   most); ck-outcome is then ok when every slot ended final, else the
\   first failure: full or invalid when the environment could not be
\   made or used (ck-made? false) or the facts found no heap, invalid
\   after a fault (a check that threw, a failed publication), when the
\   run stopped (ck-steps-begun tells how far it came);
\ - then, before ck-release, the verdicts are read in a snapshot of the
\   run's own environment (ck-verdicts?, then lf-env-outcome), and the
\   facts with ck-kept (/ck-step: outcome, diagnostic, step), ck-fuel-of,
\   ck-fuel-total, ck-fuel-unknowns, ck-top@ (ck-tops of them), the
\   times (ck-phase-wall, ck-phase-cpu, ck-total-wall, ck-total-cpu),
\   ck-peak, ck-staged-bytes, ck-staged-names and ck-count;
\ - ck-release ( -- ) frees the environment (only while it is the
\   current one with the run's identity, as run-record.fs's rr-release
\   does), detaches the names from the stage and frees it, empties the
\   stores and gives them back the capacities they had before the feed,
\   and frees the facts. ck-start does it too. A caller that catches a
\   THROW out of ck-load or ck-check calls it before passing the THROW on.
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
\ State: three shared records, ck-stage (/stage), ck-feeding-record
\ (/feed) and ck-state (the run's facts and settings), which own heap
\ blocks, as checker-input.fs's records do: one run at a time, in any
\ context, its input landing in the context current while it runs.

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

\ What a check left, kept after its step.
begin-structure /ck-step
  field: cks-outcome    \ the outcome lf-env-step published
  field: cks-code       \ the diagnostic: its code, two numbers and site
  field: cks-first
  field: cks-second
  field: cks-site
  field: cks-step       \ the step reached: check-block's for a block, else
                        \ check-declaration's
  field: cks-fuel       \ fuel used
end-structure

\ The phases timed: staging, feeding, checking.
0 constant ck-staging  1 constant ck-feeding  2 constant ck-checking
3 constant ck-phases
\ Not a timed phase: the export did not open (ck-unopened).
ck-phases constant ck-opening
10 constant ck-top-room   \ declarations in the list of the most fuel used
begin-structure /ck
  field: ck-budget               \ fuel each check starts with
  field: ck-failed               \ the phase that failed, or -1
  field: ck-loaded               \ ck-load's outcome; invalid before it
  field: ck-run                  \ the run's outcome; invalid before ck-check
  field: ck-checked              \ true once ck-check made its environment
  field: ck-env-id               \ the run's environment's identity, or 0
  field: ck-stepped              \ declarations whose check began
  field: ck-began-feed           \ true once the feed began: names attached
  4 cells +field ck-saved        \ capacities before the feed: terms, levels,
                                 \ references, input
  field: ck-stage-bytes          \ heap bytes of the stage, once staged
  4 cells +field ck-counts       \ after the feed: declarations, terms, levels, references
  field: ck-names                \ names of the stage's input tier
  2 cells +field ck-fuel-sum     \ fuel used by every check whose use is known, a double
  field: ck-unknowns             \ checks whose fuel used is not known
  field: ck-top-count            \ entries in ck-top
  ck-top-room cells +field ck-top   \ declarations by fuel used, most first
  2 cells +field ck-wall-mark    \ the clock when the phase began, doubles
  2 cells +field ck-cpu-mark
  2 cells +field ck-wall-start   \ and when the run began
  2 cells +field ck-cpu-start
  ck-phases 2* cells +field ck-walls   \ each phase's wall time, doubles
  ck-phases 2* cells +field ck-cpus    \ and its CPU time
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
: ck-made? ( -- flag ) ck-state ck-checked @ ;
: ck-fuel-total ( -- ud ) ck-state ck-fuel-sum 2@ ;
: ck-fuel-unknowns ( -- n ) ck-state ck-unknowns @ ;
-1 constant ck-fuel-unknown   \ a check's fuel used, when it is not known
\ The stage's heap bytes and the stage's names; the input's declarations
\ (k 0), term nodes (1), levels (2) and constant references (3).
: ck-staged-bytes ( -- u ) ck-state ck-stage-bytes @ ;
: ck-staged-names ( -- n ) ck-state ck-names @ ;
: ck-count-cell ( k -- addr ) cells ck-state ck-counts + ;
: ck-count ( k -- n ) ck-count-cell @ ;

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
: ck-since ( d addr -- d' ) 2@ d- ;
: ck-phase-begin ( -- )
  ck-wall-now ck-state ck-wall-mark 2! ck-cpu-now ck-state ck-cpu-mark 2! ;
: ck-wall-cell ( k -- addr ) 2* cells ck-state ck-walls + ;
: ck-cpu-cell ( k -- addr ) 2* cells ck-state ck-cpus + ;
\ Phase k took the time since ck-phase-begin.
: ck-phase-end ( k -- )
  ck-wall-now ck-state ck-wall-mark ck-since 2 pick ck-wall-cell 2!
  ck-cpu-now ck-state ck-cpu-mark ck-since rot ck-cpu-cell 2! ;
\ Phase k's times, and the run's so far.
: ck-phase-wall ( k -- d ) ck-wall-cell 2@ ;
: ck-phase-cpu ( k -- d ) ck-cpu-cell 2@ ;
: ck-total-wall ( -- d ) ck-wall-now ck-state ck-wall-start ck-since ;
: ck-total-cpu ( -- d ) ck-cpu-now ck-state ck-cpu-start ck-since ;
: ck-clock-start ( -- )
  ck-wall-now ck-state ck-wall-start 2! ck-cpu-now ck-state ck-cpu-start 2! ;

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

\ ---- The kept steps: one record per declaration of the input.
: ck-kept ( d -- addr ) ck-state ck-steps slab-at ;
: ck-fuel-of ( d -- n ) ck-kept cks-fuel @ ;
: ck-unkept ( n -- )
  0 ?do i ck-kept dup /ck-step erase outcome-invalid swap cks-outcome ! loop ;
\ Room for n records, each invalid until its step publishes: ok, or full.
: ck-steps-make ( n -- outcome )
  /ck-step dup slab-limit-max ck-state ck-steps slab-init dup ok? 0= if nip exit then
  drop dup ck-state ck-steps slab-claim nip dup ok? if swap ck-unkept else nip then ;

\ ---- Capacities: kept before the feed raises them, given back after.
create ck-capacities
  ' lf-term-capacity , ' lf-term-capacity! , ' lf-level-capacity , ' lf-level-capacity! ,
  ' lf-cref-capacity , ' lf-cref-capacity! , ' lf-input-capacity , ' lf-input-capacity! ,
: ck-saved-cell ( k -- addr ) cells ck-state ck-saved + ;
: ck-capacity-xt ( k j -- xt ) swap 2* + cells ck-capacities + @ ;
: ck-save ( -- ) 4 0 do i 0 ck-capacity-xt execute i ck-saved-cell ! loop ;
: ck-restore ( -- )
  4 0 do i ck-saved-cell @ i 1 ck-capacity-xt execute drop loop ;
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
: ck-stage-facts ( -- )
  ck-stage stage-allocated ck-state ck-stage-bytes !
  ck-stage stage-tier tier-names cons-numbers ck-state ck-names ! ;
: ck-input-facts ( -- )
  lf-input-count 0 ck-count-cell ! lf-term-count @ 1 ck-count-cell !
  lf-level-count @ 2 ck-count-cell ! lf-cref-count @ 3 ck-count-cell ! ;
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
  >r lf-diag@ r@ cks-code ! r@ cks-site ! r@ cks-second ! r> cks-first ! ;
\ Keep what declaration d's check left, with the outcome it published.
: ck-keep ( outcome d -- )
  2dup ck-used over ck-kept cks-fuel ! dup ck-step-reached over ck-kept cks-step !
  ck-kept dup ck-diag! cks-outcome ! ;
\ Check declaration d: whether the run must stop, after a fault or a
\ THROW in the check (the context is then spent).
: ck-step ( d -- stop? )
  dup >r ['] lf-check-declaration swap lf-env-step swap r> ck-keep lf-env-spent? or ;
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
: ck-confirm ( -- outcome )
  ck-viewed? if ck-all-final? flag>outcome else outcome-invalid then ;
\ After the run: whether its verdicts can be read, in a new snapshot of
\ the run's own environment.
: ck-verdicts? ( -- flag ) ck-ours? if lf-env-view ok? else false then ;
\ A new environment for the run, current: ok, or why not.
: ck-own ( env -- ) lf-envh-identity @ ck-state ck-env-id ! true ck-state ck-checked ! ;
: ck-env ( -- outcome )
  ck-fuel-budget lf-check-budget lf-env-pool-max lf-env-new dup ok? 0= if nip exit then
  drop dup ck-own lf-env-use ;

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

\ Check every declaration (see the header).
: ck-run-all ( -- outcome ) lf-input-count ck-steps-run ck-confirm ck-tally ;
: ck-check ( -- )
  ck-phase-begin lf-input-count ck-steps-make dup ok? if drop ck-env then
  dup ok? if drop ck-run-all then ck-outcome! ck-checking ck-phase-end ;

\ ---- Releasing (see the header): the environment while it is ours and
\ current, then the names detached before the stage they point into is
\ freed, the stores emptied and their capacities given back.
: ck-env-free ( -- ) ck-ours? if lf-env lf-env-free drop then 0 ck-state ck-env-id ! ;
: ck-unfeed ( -- )
  ck-state ck-began-feed @ 0= if exit then
  lf-name-detach ck-empty ck-restore false ck-state ck-began-feed ! ;
: ck-release ( -- )
  ck-env-free ck-unfeed ck-feeding-record dup feed-free /feed erase ck-stage stage-free
  ck-state ck-steps slab-free ;
: ck-start ( fuel -- )
  ck-release ck-state /ck erase ck-state ck-budget ! -1 ck-state ck-failed !
  outcome-invalid dup ck-outcome! ck-state ck-loaded ! ck-clock-start ;

base !   \ the BASE this file was loaded with

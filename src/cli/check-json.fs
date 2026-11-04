\ The JSON report of `leanforth check --json` (plan tasks 3.4.3 and, the
\ command line's part, 6.5.2): one JSON text in the format
\ leanforth-check-report, version 0.1 (schemas/check-report-0.1.schema.json;
\ docs/user/COMMAND_LINE.md, "JSON output"), then a line feed, written to
\ standard output with the project's JSON writer after a run of
\ cli/check-run.fs and before ck-release. Every verdict is read from the
\ slots of the run's own environment (ck-verdicts?), never from what the
\ run kept, which gives only each check's diagnostic, step and fuel; the
\ counts and the exit status are cli/tally.fs's, which the command line
\ fills before it writes the report. Every member but "measured" is
\ deterministic: the same for every run of the same export with the same
\ options and build; "measured" holds the times and memory.
\ LeanForth-specific and untrusted: a report, never a source of verdicts.
\
\ cj-report ( c-addr u checked? -- outcome ) writes the report of the run
\ of the export file named c-addr u, its manifest checked when checked? is
\ true: ok, or the writer's failure (invalid for a text it refuses, full
\ when a name finds no heap), after which standard output holds a text
\ cut short, never a whole report.
\ State: two shared records, the writer cj-writer and the byte slab
\ cj-name that holds a name while it is written (heap, freed at the end).

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/slab.fs
require ../lib/json-write.fs
require ../core/diagnostics.fs
require ../core/input.fs
require ../kernel/environment.fs
require ../kernel/check-declaration.fs
require ../import/manifest.fs
require ../import/stage.fs
require ../import/feed.fs
require ../present/print-names.fs
require ./tally.fs
require ./check-run.fs

8 0 json-writer: cj-writer
create cj-name /slab allot  cj-name /slab erase
: cj-schema ( -- c-addr u ) s" leanforth-check-report" ;
: cj-version ( -- c-addr u ) s" 0.1" ;
: cj-label ( -- c-addr u ) s" experimental, not independently audited" ;

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

\ A declaration's name, as the term printer writes it, gathered in
\ cj-name; a name the heap cannot hold fails the text as full.
: cj-name-sink ( c-addr u -- )
  dup cj-name slab-claim ok? if cj-name slab-at swap move exit then
  drop 2drop outcome-full cj-writer jw-fail ;
\ An empty inductive block has no name: Lean's anonymous name, which Lean
\ prints as [anonymous] (and cli/leanforth.fs too).
: cj-name-text ( d -- c-addr u )
  lf-input-name ?dup 0= if s" [anonymous]" exit then
  cj-name slab-clear ['] cj-name-sink lf-pp-name-to 0 cj-name slab-at cj-name slab-count ;
: cj-names-make ( -- )
  cj-name slab-free 1 chars dup slab-limit-max cj-name slab-init drop ;

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
: cj-where ( -- )
  ck-phase-failed case ck-staging of cj-staging endof ck-feeding of cj-feeding endof
    ck-opening of cj-unopened endof cj-ok-read endcase ;
: cj-read ( -- )
  s" read" cj-key cj-object ck-read-outcome outcome-text s" outcome" cj-text cj-where
  cj-end-object ;

\ ---- The run and its declarations, in input order.
: cj-run ( -- )
  ck-loaded? if ck-outcome outcome-text else s" not-run" then s" run" cj-text ;
\ Whether the run stopped on an internal fault, as the text's line "the
\ run stopped" says: a check threw (the context spent) or publishing
\ failed (the run invalid), in a run whose verdicts can be read.
: cj-stopped? ( -- flag )
  ck-verdicts? if lf-env-spent? ck-outcome ok? 0= or else false then ;
: cj-stopped ( -- ) cj-stopped? s" stopped" cj-flag ;
: cj-began? ( d -- flag ) ck-steps-begun < ;
\ The verdict as a run record writes it: accepted for ok.
: cj-verdict-text ( d -- c-addr u )
  dup cj-began? 0= if drop s" not-checked" exit then
  lf-env-outcome dup ok? if drop s" accepted" else outcome-text then ;
: cj-site ( site -- c-addr u ) ?dup if count else s" " then ;
: cj-numbers ( step -- )
  s" numbers" cj-key cj-array dup cks-first @ cj-n cks-second @ cj-n cj-end-array ;
: cj-reason ( step -- )
  cj-object dup cks-code @ dup s" code" cj-number lf-diag-name s" reason" cj-text
  dup cks-site @ cj-site s" site" cj-text dup cj-numbers cks-step @ s" step" cj-number
  cj-end-object ;
: cj-diagnostic ( d -- )
  s" diagnostic" cj-key ck-kept dup cks-code @ lf-diag-none =
  if drop cj-null else cj-reason then ;
: cj-axioms ( d -- )
  lf-env-axioms drop dup s" axiomBits" cj-number 0<> s" notProved" cj-flag ;
: cj-accepted ( d -- ) cj-label s" label" cj-text cj-axioms ;
\ What follows the verdict: the label and axioms of an accepted one, the
\ diagnostic of any other that began.
: cj-detail ( d -- )
  dup cj-began? 0= if drop exit then
  dup lf-env-outcome ok? if cj-accepted else cj-diagnostic then ;
\ A check's fuel used, null when it is not known (cli/check-run.fs).
: cj-fuel-used ( d -- ) s" fuel" cj-key ck-fuel-of dup 0< if drop cj-null else cj-n then ;
: cj-decl ( d -- )
  cj-object dup s" index" cj-number dup cj-name-text s" name" cj-text
  dup cj-verdict-text s" verdict" cj-text dup cj-detail cj-fuel-used cj-end-object ;
: cj-decls ( -- )
  s" declarations" cj-key cj-array
  ck-verdicts? if lf-input-count 0 ?do i cj-decl loop then cj-end-array ;

\ ---- The counts (cli/tally.fs), null when no verdict could be read.
: cj-count ( k c-addr u -- ) cj-key cli-count-of @ cj-n ;
: cj-tallies ( -- )
  outcome-ok s" accepted" cj-count outcome-rejected s" rejected" cj-count
  outcome-unknown s" unknown" cj-count outcome-unsupported s" unsupported" cj-count
  outcome-invalid s" invalid" cj-count outcome-exhausted s" exhausted" cj-count
  outcome-full s" full" cj-count not-checked s" notChecked" cj-count ;
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
  cj-object 0 ck-count s" declarations" cj-number 1 ck-count s" terms" cj-number
  2 ck-count s" levels" cj-number 3 ck-count s" references" cj-number
  ck-staged-names s" names" cj-number cj-end-object ;

\ ---- Measured: times in microseconds (null on a host without clocks),
\ the peak resident memory in bytes (null where the host does not say)
\ and the stage's heap bytes (null when nothing was staged).
: cj-time ( wall cpu c-addr u -- )
  cj-key cj-object 2swap s" wall" cj-key cj-ud s" cpu" cj-key cj-ud cj-end-object ;
: cj-phase ( k c-addr u -- ) 2>r dup ck-phase-wall rot ck-phase-cpu 2r> cj-time ;
: cj-phases ( -- )
  ck-staging s" stage" cj-phase ck-feeding s" feed" cj-phase
  ck-checking s" check" cj-phase ck-total-wall ck-total-cpu s" total" cj-time ;
: cj-times ( -- )
  s" microseconds" cj-key ck-timed? 0= if cj-null exit then
  cj-object cj-phases cj-end-object ;
: cj-peak ( -- ) s" peakResidentBytes" cj-key ck-peak if cj-n else cj-null then ;
: cj-stage-bytes ( -- )
  s" stageBytes" cj-key ck-staged? if ck-staged-bytes cj-n else cj-null then ;
: cj-measured ( -- )
  s" measured" cj-key cj-object cj-times cj-peak cj-stage-bytes cj-end-object ;

\ ---- The report.
: cj-head ( c-addr u checked? -- )
  cj-schema s" schema" cj-text cj-version s" schemaVersion" cj-text
  >r s" export" cj-text r> if s" checked" else s" not-checked" then s" manifest" cj-text
  cj-label s" label" cj-text ;
: cj-settings ( -- )
  s" settings" cj-key cj-object ck-fuel-budget s" fuel" cj-number
  lf-env-pool-max s" dependencyPool" cj-number cj-end-object ;
: cj-status ( -- ) cli-worst @ s" exitStatus" cj-number ;
: cj-body ( c-addr u checked? -- )
  cj-object cj-head cj-settings cj-read cj-run cj-stopped cj-decls cj-counts cj-fuel
  cj-input cj-status cj-measured cj-end-object ;
: cj-report ( c-addr u checked? -- outcome )
  cj-names-make ['] type cj-writer jw-start cj-body cj-writer jw-end
  dup ok? if cr then cj-name slab-free ;

base !   \ the BASE this file was loaded with

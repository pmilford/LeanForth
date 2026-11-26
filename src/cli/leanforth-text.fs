\ The command line's LeanForth text (plan tasks 8.2.1c-d; cli/check-lf.fs):
\ check [--env EXPORT | --snapshot FILE] [--elab-data DATA] [--elab-fuel N]
\ [--steps FILE|-] FILE.lf, as docs/user/COMMAND_LINE.md and cli/leanforth.fs
\ (cli-text?, cli-text-command) describe it. The words here use the front end
\ (the reader and the LeanForth words through cli/check-lf.fs, the
\ elaboration data and fuel, the step log): its loading (cli-text-load,
\ cli-text-loaded, with the elaboration fuel), its report (the elaboration
\ data's counts and refusal, a text's error, a text of only #check lines,
\ the open parts, the step log written) and its run, which sets
\ cli/leanforth.fs's deferred cli-text-run. They were cli/leanforth.fs's
\ until 2026-11-19 (branch layered-loads) and are the same words, moved so
\ that the command line of exports and snapshots loads no front end
\ (src/load/cli-checker.fs, bin/leanforth-checker); src/main.fs loads this
\ file after cli/leanforth.fs. Untrusted, like the rest of the command line.
require ../lib/lib.fs
require ../lib/decimal.fs
require ../lib/outcome.fs
require ./tally.fs
require ./check-run.fs
require ../front/simp-data.fs
require ./check-lf.fs
require ../front/meta-config.fs
require ../front/elab-decl.fs
require ../front/step-log.fs
require ./leanforth.fs

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end

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
\ Format 4's simp data (front/simp-data.fs): congruence lemmas, defeq tags.
: cli-elab-format4 ( -- )
  simp-data? 0= if exit then ." , " simp-congr-kind cli-elab-count.
  ."  congruence lemmas, " simp-defeq-count .decimal ."  defeq tags" ;
\ Format 4.1's realized congruence theorems.
: cli-elab-format41 ( -- )
  elab-format41? 0= if exit then
  ." , " simp-realized-count .decimal ."  realized congruence theorems" ;
\ Format 4.1's default simp set (front/simp-set-data.fs), when it has one.
: cli-elab-simp-set ( -- )
  simp-default? 0= if exit then ." , " simp-lemma-kind cli-elab-count.
  ."  default simp lemmas, " simp-left-kind cli-elab-count. ."  left out, "
  simp-proc-kind cli-elab-count. ."  simprocs, " simp-unfold-kind cli-elab-count.
  ."  definitions to unfold" ;
: cli-elab-note ( -- )
  cli-elab-file nip 0= if exit then ." elaboration data: " cli-elab-format1
  cli-elab-format2 cli-elab-format3 cli-elab-format4 cli-elab-format41
  cli-elab-simp-set cr ;
: cli-text-error ( -- )
  ." error: " lf-author-code lf-author-outcome dup cli-author-outcome.
  ." : the LeanForth text was not checked: " lf-author-error. cr outcome>code cli-code! ;
\ After the verdicts, in the text report, the open parts by-sorry left
\ (front/tactic-run.fs; ADR 0021 Amendment 1: the JSON report's fields
\ wait for the owner's [format] decision).
: cli-open-parts ( -- ) cli-json? 0= if lf-open-parts. then ;
\ True for a text of only #check lines (the comment above cli-checks-only in
\ cli/leanforth.fs: error 49 there, exit 0 here).
: cli-checks-only? ( -- flag )
  lfc-failed? lf-author-code lfa-e-nothing = and lf-elab-checks 0> and ;
: cli-steps-to ( sink -- outcome )
  ['] cli-step-find ['] cli-step-axioms lf-steps-write cli-steps-bad ;
: cli-steps-file ( -- outcome )
  cli-steps w/o create-file if drop outcome-full exit then cli-state run-steps-fid !
  0 0 cli-state run-steps-whole 2! ['] cli-steps-put cli-steps-to cli-steps-cut
  cli-steps-closed ;
: cli-steps-out ( -- outcome )
  cli-stdout? if ['] type cli-steps-to else cli-steps-file then ;
: cli-steps-write ( -- )
  cli-steps? 0= if exit then cli-steps-out ok? if exit then
  ." error: the step log could not be written: " cli-steps type cli-steps-left. cr
  outcome-full outcome>code cli-code! ;
: cli-text-report ( -- )
  lfc-elab-failed? if cli-elab-error exit then
  cli-checks-only? if cli-checks-only exit then
  lfc-failed? if cli-text-error exit then lfc-refused? if cli-records-error exit then
  cli-fed-tally cli-fed-report cli-open-parts cli-steps-write ;
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
:noname ( -- )
  cli-steps? lf-steps-record! cli-elab-fuel-set
  lfc-fresh cli-text-loaded ok? if cli-elab-note cli-text-lines ck-check
  then cli-text-report ;
is cli-text-run

base !   \ the BASE this file was loaded with

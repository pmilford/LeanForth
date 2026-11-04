\ The derivation log (src/core/derivation-log.fs; ADR 0013, plan task
\ 2.4.1). Off by default; the log of composition, step by step as the
\ ADR's golden table has it; each pinned export and broken copy checked
\ with the log off, on (levels steps and terms) and full at every step and
\ at every bound (records, open rules, term and level copies), each run
\ giving the same outcomes, check steps, diagnostics and fuel as the log
\ off, and every log passing the structural check (tests/support/log-check.fs);
\ an unreadable input and a THROW out of a check; the log after a check
\ that failed. Test-only.
\ This test sets the log's options itself: under the test preset
\ (tests/support/gforth-log.sh) it has nothing to add and is skipped.
[defined] lf-log-preset-level [if] .( derivation-log: skipped under the log preset) cr bye [then]
include ../support/tester.fs
include ../support/checks.fs
require ../../src/import/checker-input.fs
require ../../src/kernel/check-declaration.fs
require ../../src/present/log-view.fs
require ../support/log-check.fs

: must ( flag -- ) 0= abort" derivation-log: refused" ;
100000 constant fuel

\ A run: every declaration of file checked through lf-env-step with the
\ options' log level and limits, each step's results folded into a digest
\ (published outcome, fault, check step, the diagnostic's code and
\ numbers, the fuel left in inference and in the audit), and each
\ declaration's log checked as it stands after its step.
variable digest
variable logs-valid
variable logs-cut
variable steps-seen
: mix ( x -- ) digest @ 31 * + 2147483647 and digest ! ;
: mix-step ( outcome fault? -- )
  mix mix lf-check-step@ mix lf-diag@ mix drop mix mix lf-minfer-fuel @ mix lf-check-left @ mix ;
: log-note ( -- )
  lc-valid? 0= if 0 logs-valid ! then lf-log-complete? 0= if 1 logs-cut +! then
  lf-log-count steps-seen +! ;
: run-steps ( -- ) lf-input-count 0 ?do ['] lf-check-declaration i lf-env-step mix-step log-note
  loop ;
: run ( c-addr u -- digest )
  cin-read ok? must 0 digest ! true logs-valid ! 0 logs-cut ! 0 steps-seen !
  fuel lf-check-budget 64 lf-env-new ok? must dup lf-env-use ok? must run-steps
  lf-env-free ok? must digest @ ;
\ The options: a level and the four limits; ample restores the capacities.
: ample ( -- ) lf-log-capacities lf-log-limits ;
: level! ( level -- ) lf-log-set ample ;

\ The five pinned exports and the four broken copies of composition.
: case-file ( k -- c-addr u )
  case 0 of s" composition-wrong-argument" endof 1 of s" composition-postulate" endof
    2 of s" composition-literal" endof >r s" composition-loose" r> endcase ;
: pinned ( k -- c-addr u )
  case 0 of s" composition" endof 1 of s" identity" endof 2 of s" type-identity" endof
    3 of s" poly-identity" endof >r s" constant-fixture" r> endcase ;
create path 128 allot
: path-add ( c-addr u -- ) path count + swap dup path c@ + path c! move ;
: file ( k -- c-addr u )
  0 path c! dup 5 < if s" tests/reference/" path-add pinned
  else s" tests/core/check-declaration-cases/" path-add 5 - case-file then
  path-add s" .ndjson" path-add path count ;
9 constant files#
create baseline files# cells allot
: baseline@ ( k -- x ) cells baseline + @ ;

\ Off by default: no level, nothing recorded, in a new context too.
T{ lf-log-options lf-logopt-level @ lf-log? -> 0 0 }T
T{ 0 file run 0= lf-log-count lf-log-level -> false 0 0 }T
: new-context-off ( -- flag flag )
  context-new throw dup context-use lf-log? 0= lf-log-level 0=
  context-main context-use rot context-free throw ;
T{ new-context-off -> true true }T

\ The baselines, with the log off.
: baselines ( -- ) files# 0 ?do i file run i cells baseline + ! loop ;
baselines

\ composition with the log at level terms: 51 steps (the ADR's golden
\ table without its 14 shift steps: since free variables, plan task
\ 4.2.2a, a variable's type is its local-context entry's, as in Lean's
\ infer_fvar), complete, valid, nothing changed.
lf-log-terms level!
T{ 0 file run 0 baseline@ = logs-valid @ lf-log-count lf-log-complete? -> true true 51 true }T
: rule@ ( s -- rule ) lf-log-record logrec-rule @ ;
: depth@ ( s -- depth ) lf-log-record logrec-depth @ ;
T{ 1 rule@ 2 rule@ 3 rule@ 6 rule@ 8 rule@ -> lf-rule-fresh-name
  lf-rule-distinct-parameters lf-rule-sort lf-rule-variable lf-rule-pi }T
T{ 20 rule@ 34 rule@ 35 rule@ 36 rule@ 45 rule@ 46 rule@ -> lf-rule-proposition
  lf-rule-defeq lf-rule-instantiate lf-rule-application lf-rule-lambda lf-rule-level-eq }T
T{ 49 rule@ 50 rule@ 51 rule@ 36 depth@ 40 depth@ 50 depth@ -> lf-rule-defeq
  lf-rule-declaration lf-rule-publish 6 5 0 }T
\ Premises from start alone: application s36 used s32, s33, s34, s35;
\ the declaration s50 used s1, s2, s20, s45, s49; publish s51 used s50.
: premises ( s -- p1 .. pn ) dup lf-log-record logrec-start @ swap 1-
  begin 2dup < while dup >r lf-log-premise r> -rot repeat 2drop ;
T{ 36 premises -> 35 34 33 32 }T
T{ 50 premises -> 49 45 20 2 1 }T
T{ 51 premises -> 50 }T
\ References: s36's subject is the input node f value, its type a copy;
\ s6's subject (A) and type (Prop) are input nodes. The instantiate s35's
\ body, B as a free variable in the type of f, is copied as the bound
\ variable it stands for under the record's 6 binders and the body's
\ own: B's binder lies at depth 1, so 7 - 1 - 1 = 5; its result, the same
\ node, under the record's 6 alone: 4.
: copy-node ( ref -- tag first second ) lf-log-copy-index lf-log-term-slot node@ ;
T{ 36 lf-log-record logrec-a @ 0< 36 lf-log-record logrec-out @ lf-log-copy? -> false true }T
T{ 6 lf-log-record dup logrec-a @ 0< swap logrec-out @ 0< -> false false }T
T{ 35 lf-log-record logrec-a @ copy-node -> lf-tag-bvar 5 0 }T
T{ 35 lf-log-record logrec-out @ copy-node -> lf-tag-bvar 4 0 }T
T{ 20 lf-log-record logrec-out @ 0< -> false }T

\ Level steps: the same records, no copies, scratch results unkept.
lf-log-steps level!
T{ 0 file run 0 baseline@ = logs-valid @ lf-log-count lf-log-term-copies -> true true 51 0 }T
T{ 36 lf-log-record logrec-out @ lf-log-unkept = 36 rule@ -> true lf-rule-application }T

\ Every file at both levels: nothing changed, every log valid.
: same-at ( level -- flag )
  level! true files# 0 ?do i file run i baseline@ = logs-valid @ and and loop ;
T{ lf-log-steps same-at lf-log-terms same-at -> true true }T

\ Full at every step and every bound: for each file, each limit from 0 up
\ to what the file's checks needed (and then some), with nothing changed
\ and every truncated log a valid prefix. The total of logs truncated
\ shows that the sweeps reached the bounds.
variable truncations
: log-limits ( records marks terms levels -- ) lf-log-terms lf-log-set lf-log-limits ;
: limit-at ( n xt -- ) execute log-limits ;
: same-run? ( k -- flag )
  dup file run swap baseline@ = logs-valid @ and logs-cut @ truncations +! ;
: sweep-file ( k xt n -- flag )
  true swap 0 ?do >r i over limit-at over same-run? r> and loop nip nip ;
: at-records ( n -- records marks terms levels )
  lf-log-mark-capacity lf-log-term-capacity lf-log-level-capacity ;
: at-marks ( n -- records marks terms levels )
  lf-log-record-capacity swap lf-log-term-capacity lf-log-level-capacity ;
: at-terms ( n -- records marks terms levels )
  >r lf-log-record-capacity lf-log-mark-capacity r> lf-log-level-capacity ;
: at-levels ( n -- records marks terms levels )
  >r lf-log-record-capacity lf-log-mark-capacity lf-log-term-capacity r> ;
: sweep ( xt n -- flag )
  true files# 0 ?do i 3 pick 3 pick sweep-file and loop nip nip ;
0 truncations !
T{ ' at-records 140 sweep -> true }T
T{ ' at-marks 24 sweep -> true }T
T{ ' at-terms 40 sweep -> true }T
T{ ' at-levels 12 sweep -> true }T
." derivation-log: logs truncated by the sweeps: " truncations @ . cr
T{ truncations @ 500 > -> true }T
ample

\ A truncated log: composition with room for 30 records stops at step 31
\ (records), its 30 steps a valid prefix; with no room for term copies, at
\ the first step whose result is scratch (s3, the type of Prop).
30 at-records log-limits
T{ 0 file run 0 baseline@ = lf-log-count lf-log-cut -> true 30 31 lf-bound-records }T
0 at-terms log-limits
T{ 0 file run 0 baseline@ = lf-log-count lf-log-cut lc-valid? -> true 2 3 lf-bound-terms true }T
ample

\ A failed check: composition with g applied to value (rejected, step 7)
\ ends with the chain of rules that failed, each recorded with rejected;
\ the declaration step is last before the publication.
lf-log-terms level!
: last-rules ( -- outcome rule outcome ) lf-log-count 1- dup lf-log-record logrec-outcome @
  swap rule@ lf-log-count lf-log-record logrec-outcome @ ;
T{ 5 file run 5 baseline@ = logs-valid @ last-rules
  -> true true outcome-rejected lf-rule-declaration outcome-rejected }T

\ Outside the checked environment: lf-log-start logs direct calls; an
\ input that is no live node truncates the log (a node it cannot read),
\ and the call's outcome is the same as with the log off.
: shift-stale ( -- index id outcome ) 63 12345 0 1 100 lf-mixed-shift ;
lf-log-stop
T{ shift-stale -> -1 0 outcome-invalid }T
lf-log-terms lf-log-start
T{ shift-stale lf-log-cut lf-log-count -> -1 0 outcome-invalid 1 lf-bound-unreadable 0 }T
lf-log-stop
T{ lf-log? lf-log-level -> 0 0 }T

\ A constant whose reference lies above the input marks, with one universe
\ argument (the zero level): its copy keeps the name and the argument's
\ level reference, and log-view rebuilds it as a reference with that name
\ and one argument. The shift's input and result (the same node) are
\ copied in their own contexts (the input under one binder fewer, as
\ log-view reads it; lf-log-a-inner), so the reference is copied twice.
create one-pair 2 cells allot
: c-name ( -- id ) 0 s" c" lf-name-str must ;
: scratch-constant ( -- term id )
  c-name lf-name-generation @ 0 lf-level-identity must 0 one-pair 2!
  one-pair 1 lf-cref-new must lf-cterm-new must ;
: copied-ref ( -- slot ) 0 lf-log-cref-slot ;
: rebuilt ( -- name count )
  lf-lv-open must
  1 lf-log-record logrec-a @ lf-lv-term must dup lf-term-first@ swap lf-term-second@
  lf-cref-read must nip lf-lv-release lf-lv-close throw ;
lf-log-terms lf-log-start
T{ scratch-constant 0 1 100 lf-mixed-shift nip nip lf-log-count lf-log-cref-copies
  -> outcome-ok 1 2 }T
T{ copied-ref logcref-name @ c-name = copied-ref logcref-count @ -> true 1 }T
T{ copied-ref logcref-args @ lf-log-arg-ref lc-valid? -> 0 true }T
T{ rebuilt -> c-name 1 }T
lf-log-stop lf-input-rollback drop

\ Store capacities far above 64 records (heap stores, settings of each
\ context): a chain of applications, each over the one before and a
\ variable, built above the input marks and given to a shift, whose
\ outcome, result and fuel are the same with the log off and on. 200
\ deep, the shift succeeds (its stack grows: plan task 6.2.0) and the
\ chain and its shifted copy are copied whole (201 and 401 copies, the
\ log complete and valid); 300 deep it needs more stack than one copy may
\ use, so the log is truncated (work) and the shift's answer stands.
T{ 1000 lf-term-capacity! -> outcome-ok }T
: chain ( n -- term id )
  0 lf-term-bvar must dup rot 0 ?do over lf-term-app must loop nip dup lf-term-identity must ;
: shift-chain ( n -- index outcome fuel )
  chain 0 1 1000 lf-mixed-shift nip lf-mshift-fuel @ ;
: run-off ( n -- index outcome fuel ) lf-log-stop shift-chain lf-input-rollback drop ;
: run-on ( n -- index outcome fuel )
  lf-log-terms lf-log-start shift-chain lf-input-rollback drop ;
T{ 200 run-off -> 200 run-on }T
T{ lf-log-complete? lf-log-term-copies lc-valid? -> true 602 true }T
T{ 300 run-off -> 300 run-on }T
T{ lf-log-cut nip lf-log-count -> lf-bound-work 0 }T
lf-log-stop

\ A check that throws with rules open (in a new context, which it spends;
\ M2 of the review of 2026-11-03): after writing two records with its
\ declaration rule open, its log is truncated (interrupted) where the
\ publish step would be, not reported complete, and passes the validator
\ as a prefix; the header keeps the published slot and outcome; the next
\ check's lf-log-begin starts afresh. The validator refuses a publish step
\ whose premise is not a declaration step.
lf-log-terms level!
variable env
: thrower ( -- )
  1 2 lf-rule-declaration lf-log-open
  3 lf-log-none lf-rule-fresh-name lf-log-open outcome-ok lf-log-decided drop
  4 lf-log-none lf-rule-distinct-parameters lf-log-open outcome-ok lf-log-decided drop
  -77 throw ;
: fresh-env ( -- )
  0 file cin-read ok? must fuel lf-check-budget 64 lf-env-new ok? must
  dup env ! lf-env-use ok? must ;
: opens ( -- n ) lf-log-state lf-logs-opens @ ;
: interrupted ( -- complete? count step bound valid? slot outcome )
  lf-log-complete? lf-log-count lf-log-cut lc-valid? lf-log-published ;
: thrown-run ( -- outcome complete? n step bound valid? slot outcome opens n' )
  context-new throw dup context-use >r fresh-env
  ['] thrower 0 lf-env-step drop interrupted opens
  ['] thrower 0 lf-env-step 2drop lf-log-count
  env @ lf-env-free ok? must context-main context-use r> context-free throw ;
T{ thrown-run -> outcome-invalid false 2 3 lf-bound-interrupted true 0 outcome-invalid 1 0 }T
\ A publish step right after a step that is not a declaration step (the
\ inputs 1 and 2 are input terms of composition).
0 file cin-read ok? must
: published-after ( rule -- valid? )
  lf-log-terms lf-log-start 1 2 rot lf-log-open outcome-invalid lf-log-decided drop
  0 0 outcome-invalid lf-log-publish lc-valid? lf-log-stop ;
T{ lf-rule-declaration published-after lf-rule-fresh-name published-after -> true false }T
\ Premise kinds: a declaration step that is ok without its premises (no
\ fresh-name, formation or defeq step) fails part 9; one that failed is
\ not checked.
: declared ( outcome -- valid? why )
  lf-log-terms lf-log-start 1 2 lf-rule-declaration lf-log-open lf-log-decided drop
  lc-valid? lc-why lf-log-stop ;
T{ outcome-ok declared outcome-rejected declared -> false 9 true 0 }T

\ A corrupted start (at or above its own step) stops the validator at
\ part 2 instead of sending part 9's premise walk round for ever (N3 of
\ the second review): a record is overwritten in place, as the planted
\ fault log-start-one-step-late does.
lf-log-terms level!
: bad-start ( start -- why )
  0 file run drop 26 lf-log-record logrec-start ! lc-valid? drop lc-why ;
T{ 26 bad-start 30 bad-start -> 2 2 }T
\ A test log after a check publishes nothing (N4): lf-log-start forgets
\ the last check's slot.
T{ 0 file run drop lf-log-published drop -1 > lf-log-terms lf-log-start lf-log-published
  drop lf-log-stop -> true -1 }T

\ The printer's walks over a formula keep no depth on the host's stacks
\ (plan task 6.2.0; N5 bounded them at 128 levels before): right-nested
\ chains of 120 and 450 applications, which the copier keeps whole (450
\ overflowed Gforth 0.7.3's return stack at an earlier limit), are rebuilt
\ for printing in the same return-stack cells, painted (the copier's own
\ stacks truncate a log with a deeper copy).
require ../support/stack-paint.fs
T{ 2000 lf-term-capacity! -> outcome-ok }T
: rchain ( n -- term id )
  0 lf-term-bvar must dup rot 0 ?do over swap lf-term-app must loop nip
  dup lf-term-identity must ;
variable chain-rebuilt   variable rebuild-cells
: rebuild ( -- ) 1 lf-log-a@ lf-lv-term dup if nip then chain-rebuilt ! ;
: rebuilt? ( n -- complete? flag return-cells )
  lf-log-terms lf-log-start rchain 0 1 10000 lf-mixed-shift drop 2drop lf-log-complete?
  lf-lv-open must ['] rebuild stack-painted drop chain-rebuilt @ swap
  lf-lv-release lf-lv-close throw lf-log-stop lf-input-rollback drop ;
T{ 120 rebuilt? rebuild-cells ! -> true true }T
T{ 450 rebuilt? rebuild-cells @ - abs 4 < -> true true true }T

\ Inductive blocks (ADR 0015; N1 of the second review): with the log at
\ terms, the check of a block's first member is one inductive-block step,
\ which the publish step follows; every log passes the validator; and the
\ published outcomes are the log-off ones. A block's later members are
\ published by that check and skipped, as the environment's run skips
\ them.
require ../../src/import/feed.fs
create blk-stage /stage allot
create blk-feed /feed allot
variable blk-bad
: blk-path ( c-addr u -- c-addr' u' )
  0 path c! s" tests/core/check-block-cases/" path-add path-add s" .ndjson" path-add
  path count ;
: blk-staged ( c-addr u -- )
  blk-path 16 blk-stage stage-init ok? must blk-stage stage-load-unchecked ok? must
  blk-stage blk-feed lf-feed ok? must ;
: blk-unstage ( -- ) lf-name-viewed? if lf-name-detach then blk-stage stage-free ;
: blk-premise ( -- rule ) lf-log-count 1- ?dup if lf-log-rule@ else 0 then ;
: blk-member? ( -- flag ) lf-log-decl lf-input-decl lf-ind-member? ;
: blk-wrong? ( -- flag )
  lc-valid? 0= blk-member? blk-premise lf-rule-inductive-block <> and or ;
: blk-note ( -- ) lf-log-level if blk-wrong? if 1 blk-bad +! then then ;
: blk-step ( digest i -- digest' )
  ['] lf-check-declaration swap lf-env-step drop blk-note swap 31 * + ;
: blk-steps ( -- digest )
  0 lf-input-count 0 ?do i lf-env-published? 0= if i blk-step then loop ;
: blk-run ( c-addr u -- digest )
  blk-staged 1000000 lf-check-budget 4096 lf-env-new ok? must dup lf-env-use ok? must
  >r blk-steps r> lf-env-free ok? must blk-unstage ;
: blk-same? ( c-addr u -- flag )
  2dup lf-log-off level! blk-run >r lf-log-terms level! blk-run r> = ;
: blocks-same? ( -- flag )
  0 blk-bad ! s" ind.bool" blk-same? s" ind.nat" blk-same? and s" ind.eq" blk-same? and
  s" ind.and" blk-same? and s" ind.or" blk-same? and s" ind.exists" blk-same? and
  s" mutual.single-ctor-props" blk-same? and
  s" replay-bool.constructor-type-changed" blk-same? and
  s" params.constructor-mismatch-sort" blk-same? and ;
T{ blocks-same? blk-bad @ -> true 0 }T
\ A block log whose publish step's start is its own step fails part 2
\ (the printer then prints nothing from it: tests/present/outline-cases.fs).
: blk-cut ( -- part )
  s" ind.bool" blk-staged 1000000 lf-check-budget 4096 lf-env-new ok? must
  dup lf-env-use ok? must >r ['] lf-check-declaration 0 lf-env-step 2drop
  lf-log-count dup lf-log-record logrec-start ! lf-log-flaw r> lf-env-free ok? must
  blk-unstage ;
lf-log-terms level!
T{ blk-cut -> 2 }T

ample 0 lf-log-set
cases-done
bye

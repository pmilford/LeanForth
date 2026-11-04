\ The command line's Forth side (src/cli/leanforth.fs, plan tasks
\ 3.4.1-3.4.3; src/cli/tally.fs, check-run.fs): the exit code of every
\ outcome and their order of severity, and NOT PROVED; every code reached
\ through the Forth interface on the pinned fixtures and the changed
\ copies of composition: 0 accepted (also an inductive type, a larger
\ theorem and 30 declarations of an export with every record kind, all
\ through the importer stage and the feed), 1 rejected, 2 unsupported (a
\ declaration; with --record a record refused while reading), 3 out of
\ fuel, 4 malformed (a declaration, a missing manifest, a file that is
\ not an export or does not open, a copy over its export, --json with
\ --record), 5 an internal fault (a THROW while staging, and one inside a
\ check, each injected at an allocation with tests/support/alloc-fail.fs);
\ the declarations counted by verdict; the fuel each check used (a budget
\ of exactly that much accepts, one less is exhausted); the stage freed,
\ the names detached and the stores' capacities given back after every
\ check; the run record (--record: its text holds the verdicts, a record
\ that cannot be saved is invalid, one that names its export is refused);
\ and the reading of fuel amounts. tests/cli/test_leanforth.py runs the
\ same through bin/leanforth, with the text and JSON printed, and replays
\ records. print's codes, and a THROW at each of its store allocations.
\ Test-only; nothing here accepts a theorem outside the code under test.
include ../support/tester.fs
include ../support/checks.fs
require ../support/alloc-fail.fs
require ../../src/cli/leanforth.fs
decimal

: composition ( -- c-addr u ) s" tests/reference/composition.ndjson" ;
: fixture ( -- c-addr u ) s" tests/reference/constant-fixture.ndjson" ;
: wrong ( -- c-addr u )
  s" tests/core/check-declaration-cases/composition-wrong-argument.ndjson" ;
: postulate ( -- c-addr u )
  s" tests/core/check-declaration-cases/composition-postulate.ndjson" ;
: with-literal ( -- c-addr u )
  s" tests/core/check-declaration-cases/composition-literal.ndjson" ;
: loose ( -- c-addr u ) s" tests/core/check-declaration-cases/composition-loose.ndjson" ;
: kinds ( -- c-addr u ) s" tests/core/reexport/kinds.ndjson" ;
: inductive ( -- c-addr u ) s" tests/cli/inductive.ndjson" ;
: chain ( -- c-addr u ) s" tests/cli/chain.ndjson" ;
: tally ( k -- n ) cli-count-of @ ;

\ Each outcome's code; a value outside the vocabulary is a fault.
T{ outcome-ok outcome>code outcome-rejected outcome>code -> 0 1 }T
T{ outcome-unknown outcome>code outcome-unsupported outcome>code -> 2 2 }T
T{ outcome-exhausted outcome>code outcome-full outcome>code -> 3 3 }T
T{ outcome-invalid outcome>code 7 outcome>code -1 outcome>code -> 4 5 5 }T

\ Severity, as the documentation states it: 0 < 2 < 3 < 1 < 4 < 5. The
\ more severe of two codes is the same both ways round and is the later
\ of the two in that order.
create stated  0 , 2 , 3 , 1 , 4 , 5 ,
: stated-rank ( code -- n )
  6 0 do dup i cells stated + @ = if drop i unloop exit then loop drop 99 ;
: later? ( a b w -- flag ) stated-rank >r stated-rank swap stated-rank max r> = ;
: pair-ok? ( a b -- flag )
  2dup 2dup worse-code >r swap worse-code r@ = -rot r> later? and ;
: all-pairs? ( -- flag ) true 6 0 do 6 0 do i j pair-ok? and loop loop ;
T{ all-pairs? -> true }T

\ NOT PROVED: an accepted declaration with an axiom, and only that; it is
\ counted apart and changes no code.
T{ outcome-ok 0 not-proved? outcome-ok 4 not-proved? -> false true }T
T{ outcome-rejected 4 not-proved? outcome-unknown 0 not-proved? -> false false }T
cli-start
T{ outcome-ok 4 cli-tally-proved outcome-ok 0 cli-tally-proved cli-not-proved @ -> 1 }T
T{ outcome-rejected 1 cli-tally-proved cli-not-proved @ cli-worst @ -> 1 0 }T
\ The summary's line of the accepted, from planted counts (no check can
\ make one NOT PROVED yet); where the host can capture output (Gforth 1.0).
[defined] >string-execute [if]
: accepted-line ( accepted not-proved -- c-addr u )
  cli-start cli-not-proved ! outcome-ok cli-count-of ! ['] cli-accepted. >string-execute ;
: label-text ( -- c-addr u )
  s" accepted: 3 (experimental, not independently audited); axioms: " ;
: after-label ( c-addr u -- c-addr' u' ) label-text search drop label-text nip /string ;
: not-proved-text ( -- c-addr u ) s\" 2 NOT PROVED (they depend on an axiom)\n" ;
T{ 3 0 accepted-line drop label-text tuck compare -> 0 }T
T{ 3 0 accepted-line after-label s\" none\n" compare -> 0 }T
T{ 3 2 accepted-line after-label not-proved-text compare -> 0 }T
T{ 0 0 accepted-line nip -> 0 }T
[then]

\ Fuel amounts: decimal digits only, at most max-n.
T{ s" 0" cli-decimal s" 100000" cli-decimal -> 0 true 100000 true }T
T{ s" " cli-decimal s" -1" cli-decimal s" +1" cli-decimal s" 1x" cli-decimal
  -> false false false false }T
: max-text ( -- c-addr u ) max-n 0 <# #s #> ;
T{ max-text cli-decimal -> max-n true }T
T{ s" 99999999999999999999999999999999999999999" cli-decimal -> false }T

\ The codes of the check, with the declarations counted by verdict.
cli-options
T{ composition cli-check outcome-ok tally -> 0 1 }T
T{ fixture cli-check outcome-ok tally -> 0 3 }T
T{ inductive cli-check outcome-ok tally -> 0 5 }T  \ a block of 4 and a theorem
T{ chain cli-check outcome-ok tally -> 0 1 }T      \ larger than --record holds
T{ wrong cli-check -> 4 }T                          \ no manifest beside it
T{ s" tests/cli/no-such.ndjson" cli-check -> 4 }T
T{ s" tests/cli/leanforth.fs" cli-check -> 4 }T
cli-no-manifest
T{ wrong cli-check outcome-rejected tally outcome-ok tally -> 1 1 0 }T
T{ postulate cli-check outcome-unsupported tally -> 2 1 }T
T{ with-literal cli-check outcome-unsupported tally -> 2 1 }T
\ Every record kind (tests/core/reexport/kinds.lean): 30 accepted, among
\ them inductive blocks; the rest unknown or unsupported (plan phases 4, 5).
T{ kinds cli-check outcome-ok tally outcome-unknown tally outcome-unsupported tally
  -> 2 30 4 72 }T
T{ loose cli-check outcome-invalid tally -> 4 1 }T
T{ s" tests/cli/leanforth.fs" cli-check -> 4 }T
0 cli-fuel!
T{ fixture cli-check outcome-exhausted tally -> 3 3 }T
cli-options

\ Fuel used: composition's one check used u; with a budget of exactly u
\ it is accepted, with u - 1 it runs out.
composition cli-check drop ck-fuel-total drop constant used#
T{ used# 0> used# cli-default-fuel < -> true true }T
used# cli-fuel!
T{ composition cli-check ck-fuel-total -> 0 used# 0 }T
used# 1- cli-fuel!
T{ composition cli-check -> 3 }T
cli-options

\ After every check: no stage, the names detached, the capacities back.
: released? ( -- flag )
  ck-stage stage-state @ 0= lf-name-viewed? 0= and lf-term-capacity lf-term-default = and
  lf-input-capacity lf-input-default = and ;
T{ chain cli-check released? -> 0 true }T
T{ s" tests/cli/no-such.ndjson" cli-check released? -> 4 true }T
cli-no-manifest
T{ s" README.md" cli-check released? -> 4 true }T
cli-options

\ --record keeps the small path: an inductive type is refused while
\ reading; --json and --resources do not go with it.
s" /dev/null" cli-record!
T{ inductive cli-check chain cli-check -> 2 3 }T
cli-json
T{ composition cli-check -> 4 }T
cli-options s" /dev/null" cli-record! cli-resources
T{ composition cli-check -> 4 }T
cli-options

\ The counter and the re-exporter: their codes, without writing a file.
T{ composition cli-count kinds cli-count -> 0 4 }T
T{ cli-no-manifest kinds cli-count cli-options -> 0 }T
T{ composition composition cli-reexport -> 4 }T
T{ s" tests/cli/no-such.ndjson" s" tests/cli/no-such-copy.ndjson" cli-reexport -> 4 }T
T{ composition s" tests/cli/no-such-folder/copy.ndjson" cli-reexport -> 4 }T
T{ cli-version cli-capabilities cli-help -> 0 0 0 }T

\ The run record (--record): written after the run (here to /dev/null; the
\ text stays in rr-text), with every declaration's verdict, the read and
\ the run, and the code unchanged; one that cannot be saved is reported
\ and the code is invalid's; one that names the export is refused before
\ anything is read or written.
: holds? ( c-addr u -- flag ) rr-text 2swap search nip nip ;
cli-options s" /dev/null" cli-record!
T{ fixture cli-check -> 0 }T
T{ s\" {\"index\":2,\"name\":\"fixtureUse\",\"verdict\":\"accepted\"" holds? -> true }T
T{ s\" \"check\":{\"read\":\"ok\",\"run\":\"ok\"" holds? -> true }T
cli-no-manifest
T{ wrong cli-check -> 1 }T
T{ s\" \"name\":\"composition\",\"verdict\":\"rejected\"" holds? -> true }T
cli-options s" tests/cli/no-such-folder/run.json" cli-record!
T{ composition cli-check outcome-ok tally -> 4 1 }T
cli-options composition cli-record!
T{ composition cli-check outcome-ok tally -> 4 0 }T
cli-options

\ Only a check with --record reads the export for the record (rr-start: its
\ digest, metadata and manifest). Without it the export is read once, by
\ the importer stage: the record's facts stay as cleared, and no file is
\ kept, so no record can be written from that run.
: hashed-bytes ( -- ud ) run-record rr-before facts-bytes 2@ ;
: unhashed ( -- ) run-record rr-before /rr-facts erase ;
unhashed
T{ fixture cli-check -> 0 }T
T{ hashed-bytes rr-started? run-record rr-exporter rr-note? -> 0 0 false false }T
T{ rr-write -> outcome-invalid }T
unhashed s" /dev/null" cli-record!
T{ fixture cli-check hashed-bytes d0= rr-started? -> 0 false true }T
cli-options

\ print: the code of each kind of declaration printed (0 an outline; a
\ declaration not accepted its outcome's code; a name no declaration has
\ 4), one declaration by name, every step, and the log options left off.
cli-options
T{ composition cli-print fixture cli-print -> 0 0 }T
T{ s" fixtureUse" cli-name! fixture cli-print -> 0 }T
T{ s" noSuch" cli-name! fixture cli-print -> 4 }T
cli-options cli-detail
T{ composition cli-print -> 0 }T
cli-options
\ wrong has no manifest beside it; unfold's impliesSelf ends unknown.
T{ wrong cli-print s" tests/cli/unfold.ndjson" cli-print -> 4 2 }T
cli-no-manifest
T{ wrong cli-print postulate cli-print loose cli-print -> 1 2 4 }T
cli-options 0 cli-fuel!
T{ fixture cli-print -> 3 }T
cli-options
T{ s" tests/cli/no-such.ndjson" cli-print -> 4 }T
T{ lf-log-options lf-logopt-level @ -> 0 }T

\ A declaration's name as text, and finding it.
T{ fixture true rr-read-once s" fixturePoly" pr-find -> outcome-ok 1 true }T
T{ s" fixture" pr-find 2 pr-name s" fixtureUse" compare -> false 0 }T

\ Internal faults, each in a context of its own (a THROW in a check
\ spends its context for good). Staging and feeding composition in a new
\ context and making the run's environment make n allocations of the
\ stores (the stage's own blocks are not counted): a THROW at the first is
\ one while feeding; at n + 1, one in the check. Either way the stage is
\ freed and the names detached.
: fed-env ( -- env ) cli-default-fuel lf-check-budget lf-env-pool-max lf-env-new drop ;
: fed-allocations ( -- n )
  context-new throw dup >r context-use cli-default-fuel ck-start 0 af-arm
  composition true ck-load drop fed-env af-seen@ af-off swap lf-env-free drop ck-release
  context-main context-use r> context-free throw ;
fed-allocations constant fed#
: in-context ( k -- code spent? released? )
  context-new throw dup >r context-use af-arm-throw composition cli-check af-off
  lf-env-spent? ck-stage stage-state @ 0= lf-name-viewed? 0= and
  context-main context-use r> context-free throw ;
T{ fed# 0> -> true }T
T{ 1 in-context -> 5 false true }T
T{ fed# 1+ in-context -> 5 true true }T
\ The run that stopped is invalid: its slot did not end final.
T{ ck-outcome -> outcome-invalid }T

\ print reads with the checker's input: n allocations stage composition
\ there, fewer than print makes in all.
: staging-allocations ( -- n )
  context-new throw dup >r context-use 0 af-arm composition cin-read drop af-seen@ af-off
  context-main context-use r> context-free throw ;
staging-allocations constant staged#

\ print with a THROW at each of its store allocations in turn (staging,
\ the names' read, a check, the printer's scratch), each in a context of
\ its own: always the code 5, the log switched off again, and no checked
\ environment left current (C2 of the review of 2026-11-03).
: fresh ( -- context ) context-new throw dup context-use cli-options ;
: back ( context -- ) context-main context-use context-free throw ;
: print-allocations ( -- n )
  fresh 0 af-arm composition cli-print drop af-seen@ af-off swap back ;
print-allocations constant printed#
: print-fault ( k -- code level env )
  fresh >r af-arm-throw composition cli-print af-off lf-log-options lf-logopt-level @
  lf-env r> back ;
: print-bad? ( k -- flag ) print-fault 0<> swap 0<> or swap 5 <> or ;
: print-faults ( -- n ) 0 printed# 1+ 1 ?do i print-bad? if 1+ then loop ;
T{ printed# staged# > print-faults -> true 0 }T

cases-done
bye

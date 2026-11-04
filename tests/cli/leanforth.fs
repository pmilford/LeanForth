\ The command line's Forth side (src/cli/leanforth.fs, plan tasks
\ 3.4.1-3.4.2): the exit code of every outcome and their order of
\ severity; every code reached through the Forth interface on the pinned
\ fixtures and the changed copies of composition: 0 accepted, 1 rejected,
\ 2 unsupported (a declaration, and a record refused while reading),
\ 3 out of fuel, 4 malformed (a declaration, a missing manifest, a file
\ that is not an export or does not open, a copy over its export), 5 an
\ internal fault (a THROW while staging, and one inside a check, each
\ injected at an allocation with tests/support/alloc-fail.fs); the
\ declarations counted by verdict; the run record (--record: its text
\ holds the verdicts, a record that cannot be saved is invalid, one that
\ names its export is refused); and the reading of fuel amounts.
\ tests/cli/test_leanforth.py runs the same through bin/leanforth, with
\ the text printed, and replays records. Test-only; nothing here accepts
\ a theorem outside the code under test.
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
T{ wrong cli-check -> 4 }T                          \ no manifest beside it
T{ s" tests/cli/no-such.ndjson" cli-check -> 4 }T
T{ s" tests/cli/leanforth.fs" cli-check -> 4 }T
cli-no-manifest
T{ wrong cli-check outcome-rejected tally outcome-ok tally -> 1 1 0 }T
T{ postulate cli-check outcome-unsupported tally -> 2 1 }T
T{ with-literal cli-check outcome-unsupported tally -> 2 1 }T
T{ kinds cli-check -> 2 }T                          \ an inductive type, while reading
T{ loose cli-check outcome-invalid tally -> 4 1 }T
T{ s" tests/cli/leanforth.fs" cli-check -> 4 }T
0 cli-fuel!
T{ fixture cli-check outcome-exhausted tally -> 3 3 }T
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
\ the checker's input: the record's facts stay as cleared, and no file is
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

\ Internal faults, each in a context of its own (a THROW in a check
\ spends its context for good). Staging composition makes n allocations:
\ a THROW at the first is one while staging; at n + 1, one in the check.
: staging-allocations ( -- n ) 0 af-arm composition cin-read drop af-seen@ af-off ;
staging-allocations constant staged#
: in-context ( k -- code spent? )
  context-new throw dup >r context-use af-arm-throw composition cli-check af-off
  lf-env-spent? context-main context-use r> context-free throw ;
T{ staged# 0> -> true }T
T{ 1 in-context -> 5 false }T
T{ staged# 1+ in-context -> 5 true }T

cases-done
bye

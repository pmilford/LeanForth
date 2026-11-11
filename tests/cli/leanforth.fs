\ The command line's Forth side (src/cli/leanforth.fs, plan tasks
\ 3.4.1-3.4.3; src/cli/tally.fs, check-run.fs): the exit code of every
\ outcome and their order of severity, and NOT PROVED; every code reached
\ through the Forth interface on the pinned fixtures and the changed
\ copies of composition: 0 accepted (also an inductive type, a larger
\ theorem and 30 declarations of an export with every record kind, all
\ through the importer stage and the feed), 1 rejected, 2 unsupported (a
\ declaration; with --record a record refused while reading), 3 out of
\ fuel or room (an allocation refused while feeding, and inside a check),
\ 4 malformed (a declaration, a missing manifest, a file that is not an
\ export or does not open, a copy over its export, --json with --record),
\ 5 an internal fault (a THROW while staging, and one inside a check,
\ each injected at an allocation with tests/support/alloc-fail.fs; the
\ publisher made to throw mid-run), NOT PROVED (an axiom planted in an
\ accepted slot: Lean's 0 by default, 6 under --strict-axioms); the
\ declarations counted by verdict; the fuel each
\ check used (a budget of exactly that much accepts, one less is
\ exhausted); a second run the same as the first; the stage freed, the
\ names detached and every store's capacity given back after every check;
\ the run record (--record: its text holds the verdicts, a record that
\ cannot be saved is invalid, one that names its export is refused); the
\ reading of fuel amounts, at most 2^53 - 1; names shown as Lean shows
\ them, escaped, of any depth. tests/cli/test_leanforth.py runs the same
\ through bin/leanforth, with the text and JSON printed, and replays
\ records. print's codes, and a THROW at each of its store allocations.
\ Test-only; nothing here accepts a theorem outside the code under test.
include ../support/tester.fs
include ../support/checks.fs
require ../support/alloc-fail.fs
\ The publisher's test-only fault hook, lf-env-before-final, to stop a run.
: lf-env-fault-hooks ( -- ) ;
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
\ A block whose check needs a recursor reduction not ported yet: unknown.
: undecided ( -- c-addr u )
  s" tests/core/check-block-cases/after.list-left-out-then-lookup-during-param-block.ndjson" ;
: kinds ( -- c-addr u ) s" tests/core/reexport/kinds.ndjson" ;
: inductive ( -- c-addr u ) s" tests/cli/inductive.ndjson" ;
: chain ( -- c-addr u ) s" tests/cli/chain.ndjson" ;
: tally ( k -- n ) cli-count-of @ ;

\ Each outcome's code; a value outside the vocabulary is a fault.
T{ outcome-ok outcome>code outcome-rejected outcome>code -> 0 1 }T
T{ outcome-unknown outcome>code outcome-unsupported outcome>code -> 2 2 }T
T{ outcome-exhausted outcome>code outcome-full outcome>code -> 3 3 }T
T{ outcome-invalid outcome>code 7 outcome>code -1 outcome>code -> 4 5 5 }T
\ A skipped declaration (plan task 5.2.7) keeps Lean's code 0, is counted
\ as skipped and named so; every outcome keeps its code.
T{ skipped verdict>code outcome-rejected verdict>code not-checked verdict>code -> 0 1 5 }T
cli-start
T{ skipped cli-tally outcome-rejected cli-tally skipped tally outcome-rejected tally -> 1 1 }T
T{ cli-worst @ skipped verdict-name s" skipped" compare -> 1 0 }T

\ Severity, as the documentation states it: 0 < 6 < 2 < 3 < 1 < 4 < 5. The
\ more severe of two codes is the same both ways round and is the later
\ of the two in that order.
create stated  0 , 6 , 2 , 3 , 1 , 4 , 5 ,
: stated-rank ( code -- n )
  7 0 do dup i cells stated + @ = if drop i unloop exit then loop drop 99 ;
: later? ( a b w -- flag ) stated-rank >r stated-rank swap stated-rank max r> = ;
: pair-ok? ( a b -- flag )
  2dup 2dup worse-code >r swap worse-code r@ = -rot r> later? and ;
: all-pairs? ( -- flag ) true 7 0 do 7 0 do i j pair-ok? and loop loop ;
T{ all-pairs? -> true }T

\ NOT PROVED: an accepted declaration with an axiom outside the allowlist
\ (bit 8; 7 holds the three listed ones), and only that; it is
\ counted apart and keeps Lean's code (0) by default; under
\ --strict-axioms it has code 6, which every other failure outranks.
T{ outcome-ok 0 not-proved? outcome-ok 8 not-proved? outcome-ok 7 not-proved? -> false true false }T
T{ outcome-rejected 8 not-proved? outcome-unknown 0 not-proved? -> false false }T
cli-start
T{ outcome-ok 8 cli-tally-proved outcome-ok 0 cli-tally-proved cli-not-proved @ cli-worst @
  -> 1 0 }T
T{ outcome-rejected 1 cli-tally-proved cli-not-proved @ cli-worst @ -> 1 0 }T
cli-start true cli-strict-axioms!
T{ outcome-ok 9 cli-tally-proved cli-not-proved @ cli-worst @ -> 1 6 }T
T{ outcome-unknown cli-tally cli-worst @ -> 2 }T
cli-start
T{ cli-strict-axioms? -> false }T
\ The summary's line of the accepted, from planted counts and axioms used
\ (review rvAX L4: the allowlisted ones named, then the NOT PROVED count);
\ where the host can capture output (Gforth 1.0).
[defined] >string-execute [if]
: accepted-line ( accepted not-proved bits -- c-addr u )
  cli-start cli-axioms-used ! cli-not-proved ! outcome-ok cli-count-of !
  ['] cli-accepted. >string-execute ;
: label-text ( -- c-addr u )
  s" accepted: 3 (experimental, not independently audited); axioms: " ;
: after-label ( c-addr u -- c-addr' u' ) label-text search drop label-text nip /string ;
: not-proved-text ( -- c-addr u ) s\" 2 NOT PROVED (they depend on an axiom)\n" ;
: listed-text ( -- c-addr u )
  s\" propext, Quot.sound (allowlisted); 2 NOT PROVED (they depend on an axiom)\n" ;
: choice-text ( -- c-addr u ) s\" Classical.choice (allowlisted); none NOT PROVED\n" ;
T{ 3 0 0 accepted-line drop label-text tuck compare -> 0 }T
T{ 3 0 0 accepted-line after-label s\" none\n" compare -> 0 }T
T{ 3 2 8 accepted-line after-label not-proved-text compare -> 0 }T
T{ 3 2 13 accepted-line after-label listed-text compare -> 0 }T
T{ 3 0 2 accepted-line after-label choice-text compare -> 0 }T
T{ 0 0 0 accepted-line nip -> 0 }T
[then]

\ Fuel amounts: decimal digits only, at most max-n.
T{ s" 0" cli-decimal s" 100000" cli-decimal -> 0 true 100000 true }T
T{ s" " cli-decimal s" -1" cli-decimal s" +1" cli-decimal s" 1x" cli-decimal
  -> false false false false }T
: max-text ( -- c-addr u ) max-n 0 <# #s #> ;
T{ max-text cli-decimal -> max-n true }T
T{ s" 99999999999999999999999999999999999999999" cli-decimal -> false }T
\ --fuel takes at most 2^53 - 1 (on a 64-bit host): exact in JSON.
: bits64? ( -- flag ) max-n 53 rshift 0<> ;
bits64? [if]
T{ cli-fuel-most 1+ 1 53 lshift = -> true }T
[then]

\ Names as cli/name-text.fs shows them: Lean's Name.toString, with « »
\ always around a component that is not an identifier and escapes for
\ what the text rule bans, for » and for a backslash; names of any depth.
: shows ( c-addr u -- c-addr' u' ) 0 -rot lf-name-str drop nt-name drop ;
: num-shows ( n -- c-addr u ) 0 swap lf-name-num drop nt-name drop ;
T{ s" fixtureUse" shows s" fixtureUse" compare -> 0 }T
T{ s" with space" shows s" «with space»" compare -> 0 }T
T{ s" " shows s" «»" compare -> 0 }T
T{ s\" a\nb" shows s" «a\u{A}b»" compare -> 0 }T
T{ s\" a\rb\x1b[2K" shows s" «a\u{D}b\u{1B}[2K»" compare -> 0 }T
T{ s\" a\xe2\x80\xaeb" shows s" «a\u{202E}b»" compare -> 0 }T
T{ s\" a\\b" shows s" «a\\b»" compare -> 0 }T
\ A component holding »: between « and », the » escaped (Lean shows it
\ bare, so its spaces and colons would pass through).
T{ s\" fake: accepted\xc2\xbb" shows s" «fake: accepted\u{BB}»" compare -> 0 }T
T{ s\" \xce\xb1\xce\xb2\xce\xb3" shows s\" \xce\xb1\xce\xb2\xce\xb3" compare -> 0 }T
T{ s" x'" shows s" x'" compare s" 1x" shows s" «1x»" compare -> 0 0 }T
\ Subscripts as Lean's isSubScriptAlnum: digits and letters, not signs.
T{ s\" x\xe2\x82\x81" shows s\" x\xe2\x82\x81" compare -> 0 }T      \ x₁
T{ s\" x\xe2\x82\x90" shows s\" x\xe2\x82\x90" compare -> 0 }T      \ xₐ
T{ s\" x\xe2\x82\x8a" shows s\" \xc2\xabx\xe2\x82\x8a\xc2\xbb" compare -> 0 }T  \ «x₊»
T{ 7 num-shows s" 7" compare 0 nt-name drop s" [anonymous]" compare -> 0 0 }T
\ Deeper than the term printer's 64 components: every component shown
\ (the name store made larger for it, then given back its default).
: deep ( n -- id ) 0 swap 0 ?do s" a" lf-name-str drop loop ;
: dots ( n -- u ) 2* 1- ;
lf-name-reset 200 lf-name-capacity! drop
T{ 100 deep nt-name -rot nip 100 dots = -> true true }T
lf-name-reset lf-name-default lf-name-capacity! drop
\ Names Lean shows without « » (macro scopes, an inaccessible name,
\ pseudo-syntax): each component that is not an identifier between « ».
: hygienic ( -- id ) 0 s" x" lf-name-str drop s" _@" lf-name-str drop s" _hyg" lf-name-str drop ;
T{ hygienic nt-name drop s" x.«_@»._hyg" compare -> 0 }T
T{ s\" fake: accepted\xe2\x9c\x9d" shows s\" \xc2\xabfake: accepted\xe2\x9c\x9d\xc2\xbb" compare
  -> 0 }T
T{ s" _" shows s" _" compare s" #x y" shows s" «#x y»" compare -> 0 0 }T
\ An export's file name: the same escapes, no « ».
T{ s\" a b\x01\xff" nt-text drop s" a b\u{1}\x{FF}" compare -> 0 }T

\ The codes of the check, with the declarations counted by verdict.
cli-options
T{ composition cli-check outcome-ok tally -> 0 1 }T
T{ fixture cli-check outcome-ok tally -> 0 3 }T
\ An inductive type (a block of 4), a theorem and a definition by its
\ recursor: Lean's verdicts, all accepted, none unsupported.
T{ inductive cli-check outcome-ok tally outcome-unsupported tally -> 0 6 0 }T
T{ chain cli-check outcome-ok tally -> 0 1 }T      \ larger than --record holds
T{ wrong cli-check -> 4 }T                          \ no manifest beside it
T{ s" tests/cli/no-such.ndjson" cli-check -> 4 }T
T{ s" tests/cli/leanforth.fs" cli-check -> 4 }T
cli-no-manifest
T{ wrong cli-check outcome-rejected tally outcome-ok tally -> 1 1 0 }T
\ An axiom (plan task 5.3.1): accepted as Lean accepts it, NOT PROVED.
T{ postulate cli-check outcome-ok tally cli-not-proved @ -> 0 1 1 }T
\ A proof that is a string literal, typed String, which the file does not
\ declare: rejected, as pinned Lean's kernel rejects it (plan task 5.2.3).
T{ with-literal cli-check outcome-rejected tally -> 1 1 }T
\ Every record kind (tests/core/reexport/kinds.lean): 94 accepted, among
\ them inductive blocks, Nat and List (plan task 5.2.1b), projections
\ (plan task 5.2.2), literals (plan task 5.2.3), axioms, opaque
\ declarations and quotients (plan tasks 5.3.1, 4.2.6, 5.2.4), the nested
\ Tree with Tree.rec_1 (plan task 5.2.5b) and what uses them, with Lean's
\ lazy delta reduction (plan task 4.2.2d); the unsafe definition risky
\ skipped (plan task 5.2.7); the rest unsupported (plan phases 4, 5).
T{ kinds cli-check outcome-ok tally skipped tally outcome-unknown tally
  outcome-unsupported tally -> 2 94 1 0 11 }T
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

\ After every check: no stage, the names detached, every capacity back.
: capacities? ( -- flag )
  lf-term-capacity lf-term-default = lf-input-capacity lf-input-default = and
  lf-level-capacity lf-level-default = and lf-cref-capacity lf-cref-default = and ;
: released? ( -- flag )
  ck-stage stage-state @ 0= lf-name-viewed? 0= and capacities? and ck-restored ok? and ;
T{ chain cli-check released? -> 0 true }T
T{ kinds cli-check released? -> 4 true }T            \ no manifest beside it
T{ s" tests/cli/no-such.ndjson" cli-check released? -> 4 true }T
cli-no-manifest
T{ s" README.md" cli-check released? kinds cli-check released? -> 4 true 2 true }T
cli-options

\ A second run in the same process gives the same verdicts and fuel.
: run-facts ( c-addr u -- code ok# fuel )
  cli-check outcome-ok tally ck-fuel-total drop ;
\ (546 since == is Lean's at every pair, plan step S4; 581 since levels
\ and references are hash-consed and equal constants and Sorts are one
\ node, plan step S4, so the audits and == meet fewer distinct nodes; 607
\ since the audits check each node once per check and read V1
\ and U2 from data words, plan step S6 (c) (590 without step S6's other
\ parts); 996 since inference keys a type by the term closed with its
\ scope, as Lean keys it by the opened term, and the substitutions are
\ Lean's replace, plan task 6.5.5; 979 since the audits check each shared
\ node once and a constant without
\ universe arguments has its stored type, agent EX; 1039 with Lean's
\ caches and cached node data, plan task 4.2.7; 1184
\ since the block check uses Lean's whnf, plan task 5.2.1b; 1187 since
\ conversion is Lean's is_def_eq, plan task 4.2.2b; 1520 before.)
T{ inductive run-facts inductive run-facts -> 0 6 546 0 6 546 }T
cli-no-manifest
kinds run-facts constant kinds-fuel drop drop
T{ kinds run-facts -> 2 94 kinds-fuel }T
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
\ wrong has no manifest beside it; irrelevance's theorem is accepted
\ (proof irrelevance, plan task 4.2.5).
T{ wrong cli-print s" tests/cli/irrelevance.ndjson" cli-print -> 4 0 }T
cli-no-manifest
T{ wrong cli-print postulate cli-print loose cli-print -> 1 0 4 }T
T{ undecided cli-print -> 2 }T
cli-options 0 cli-fuel!
T{ fixture cli-print -> 3 }T
cli-options
T{ s" tests/cli/no-such.ndjson" cli-print -> 4 }T
T{ lf-log-options lf-logopt-level @ -> 0 }T

\ A declaration's name as text, and finding it.
T{ fixture true rr-read-once s" fixturePoly" pr-find -> outcome-ok 1 true }T
T{ s" fixture" pr-find s" fixtureUse" pr-find -> false 2 true }T

\ Internal faults, each in a context of its own (a THROW in a check
\ spends its context for good). Staging and feeding composition in a new
\ context and making the run's environment make n allocations of the
\ stores (the stage's own blocks are not counted): a THROW at the first is
\ one while feeding; at n + 1, one in the check. Either way the stage is
\ freed and the names detached.
: fed-env ( -- env ) cli-default-fuel lf-check-budget lf-env-pool-start lf-env-new drop ;
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

\ Allocations refused (full) rather than thrown: at the first, the feed
\ fails, full, before any fact or environment is made; at n + 1, the
\ check has no room: its declaration ends full, a resource limit (3),
\ and the run is whole. Either way everything is given back.
: refused ( k -- code phase made? facts? full# released? )
  context-new throw dup >r context-use af-arm composition cli-check af-off
  ck-phase-failed ck-made? ck-facts-made? outcome-full tally released?
  context-main context-use r> context-free throw ;
T{ 1 refused -> 3 ck-feeding false false 0 true }T
T{ fed# 1+ refused -> 3 -1 true true 1 true }T

\ A run that stops in the publisher: a THROW before declaration 1's slot
\ is final. The run is invalid (that slot is open), the code a fault's;
\ declaration 0 stays accepted, 1 is invalid and 2 was never checked.
: throw-at-1 ( -- ) lf-env-limit 1 = if 4242 throw then ;
: run-tallies ( -- code run ok# invalid# unchecked# )
  fixture cli-check ck-outcome outcome-ok tally outcome-invalid tally not-checked tally ;
: stopped ( -- code run ok# invalid# unchecked# )
  context-new throw >r r@ context-use cli-options run-tallies
  context-main context-use r> context-free throw ;
' throw-at-1 is lf-env-before-final
T{ stopped -> 5 outcome-invalid 1 1 1 }T
' lf-env-no-fault is lf-env-before-final

\ NOT PROVED from a slot: composition checked as check --record checks
\ it, then its accepted slot given the unlisted axiom bit before the
\ verdicts are read (no axiom slot names it): counted, and said in its
\ line and the summary; code 0, Lean's, with a note, or 6 under
\ --strict-axioms.
: planted-run ( strict? -- )
  cli-options composition 0 cli-file! cli-start cli-strict-axioms!
  cli-recorded-ops cli-state run-ops ! cli-settings cli-record-start drop cli-import drop
  rr-check 8 0 lf-env lf-env-slot lf-slot-axioms ! ;
: planted ( strict? -- code not-proved# )
  planted-run cli-results rr-release cli-worst @ cli-not-proved @ ;
T{ false planted true planted -> 0 1 6 1 }T
[defined] >string-execute [if]
: planted-text ( strict? -- c-addr u )
  planted-run ['] cli-results >string-execute rr-release ;
: says? ( c-addr u c-addr2 u2 -- c-addr u flag ) 2over 2swap search nip nip ;
: planted-line ( -- c-addr u )
  s" composition: accepted (experimental, not independently audited); axioms: unlisted; "
  s" NOT PROVED: depends on an axiom" s+ ;
: noted? ( c-addr u -- c-addr u flag )
  s" note: NOT PROVED declarations keep Lean's exit status; --strict-axioms" says? ;
: planted-says ( strict? -- line? summary? note? )
  planted-text planted-line says? >r s" axioms: 1 NOT PROVED" says? >r noted? nip nip
  r> r> swap rot ;
T{ false planted-says true planted-says -> true true true true true false }T
[then]
cli-options

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

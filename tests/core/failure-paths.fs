\ The failure-path suite of the first checker (plan tasks 2.2.4 and
\ 1.4.6): every check step of check-declaration (src/kernel/
\ check-declaration.fs), run through the checked environment's publisher,
\ reaches its outcomes, and nothing that fails is ever stored, published,
\ given a handle or printed as accepted.
\
\ Cases: the five pinned fixtures (tests/reference/*.ndjson, read with the
\ checker-input module src/import/checker-input.fs), all accepted, and
\ cases in the first-checker driver's prefix text (tests/support/
\ first-checker-driver.fs, the rows of tests/core/check-declaration.fs)
\ that end rejected, unknown, unsupported, invalid or full where Lean's
\ kernel stops. For every case:
\ - a baseline run, fuel 100,000 and nothing injected: its outcomes are
\   the expected ones, and its allocations are counted per declaration;
\ - refusals: allocation k is refused as if its store were full
\   (tests/support/alloc-fail.fs, the hook of src/lib/store.fs), for
\   k = 1, 2, ... up to one past the baseline's allocations;
\ - fuel: every check gets fuel 0, 1, 2, ... until the run gives the
\   baseline's outcomes;
\ - THROWs: allocation k throws, for every k the baseline makes, each run
\   in a new context of its own with a maker that loads the same input
\   into another one (G-P6), so that the run goes on after a check
\   throws; and, for two fixtures, a run with no maker, which stops.
\ Refusal and fuel runs drive lf-env-step one declaration at a time, as
\ lf-env-run does, and check after every step that only the declaration's
\ own slot changed, that the dependency pool grew only by an accepted
\ declaration's dependencies, and that every input store is back at its
\ mark, the input intact and its fingerprint unchanged. After every run:
\ - a slot is accepted only when its baseline is and every slot it
\   depended on there is accepted now;
\ - the slot where the injected failure was reached is full (a refusal)
\   or invalid (a THROW); when that was in the publisher, it is open and
\   cleared (outcome invalid, every other field zero) and the run stops.
\   A refusal in the search for a rejection after an undecided comparison
\   is full too (ADR 0008; since plan task 4.2.2c, unknown before);
\ - every other slot has its baseline outcome while every slot before it
\   has; otherwise it may only be unknown (K5) instead, and in a fuel run
\   also exhausted (an analysis that runs out of fuel too, since plan task
\   4.2.2c);
\ - every slot's handle, outcome read back and printed verdict agree, and
\   an accepted slot prints the axiom set it holds (a bit planted after
\   the run must show);
\ - a refusal or a lack of fuel never spends the context; a THROW in a
\   check spends it, one in the publisher does not.
\ Last, a clean run gives the baseline again in the same context. And a
\ check that passed but whose claim the publisher's re-check refuses is
\ published invalid, never accepted.
\
\ The suite prints, per check step, the outcomes it reached, and fails
\ unless they are exactly the expected ones below; then the number of
\ injected runs. Test-only; nothing here accepts a theorem.

include ../support/tester.fs
include ../support/checks.fs
require ../support/alloc-fail.fs
require ../../src/import/checker-input.fs
require ../support/first-checker-driver.fs
decimal

100000 constant fuel
lf-input-capacity constant most

\ ---------------------------------------------------------------------------
\ Reporting a broken rule with the case, the run and the slot.
create fp-case-name 40 allot
variable fp-case#
variable fp-run      \ the run: k, or the fuel
variable fp-mode     \ 0 baseline or clean, 1 refusal, 2 fuel, 3 throw
variable fp-slot
: .fp-mode ( -- )
  fp-mode @ case 0 of ." baseline" endof 1 of ." refusal" endof
    2 of ." fuel" endof 3 of ." throw" endof endcase ;
defer .fp-slot ( -- )   \ the slot's outcomes, once they can be read
' noop is .fp-slot
: fp-where ( -- )
  fp-case-name fp-case# @ type space .fp-mode space fp-run @ 0 .r
  ."  slot " fp-slot @ 0 .r .fp-slot ." : " ;
: fp-must ( flag c-addr u -- ) rot if 2drop exit then fp-where type cr -1 throw ;

\ ---------------------------------------------------------------------------
\ Coverage: the outcomes reached at each step (lf-check-step@: 0 before a
\ snapshot, 1-8 the steps, 9 every step done), as bit sets by outcome.
10 constant steps#
create reached steps# cells allot  reached steps# cells erase
: reach ( step outcome -- ) 1 swap lshift swap cells reached + dup @ rot or swap ! ;

\ ---------------------------------------------------------------------------
\ Cases. A loader ( -- ) loads the case's input into the current context
\ and ends loading.
variable fp-loader
: fp-load ( -- ) fp-loader @ execute ;
: ndjson ( c-addr u -- ) cin-read ok? s" not read" fp-must ;

\ ---------------------------------------------------------------------------
\ The baseline: per slot its outcome, its dependencies (a bit set of
\ slots) and the allocations counted up to the end of its step, which
\ includes its publication.
create base-outcome most cells allot
create base-deps most cells allot
create base-allocs most cells allot
: base@ ( d -- outcome ) cells base-outcome + @ ;
: deps@ ( d -- set ) cells base-deps + @ ;
: allocs@ ( d -- n ) cells base-allocs + @ ;
variable allocs#     \ the allocations of the whole baseline run

\ The environment of a run and its slots.
variable fp-env
: fp-slot@ ( d -- slot ) lf-env lf-env-slot ;
: fp-pool ( -- store ) lf-env lf-env-pool ;
: fp-open ( -- )
  64 lf-env-new ok? s" no environment" fp-must dup fp-env !
  lf-env-use ok? s" not usable" fp-must ;
: fp-close ( -- ) fp-env @ lf-env-free ok? s" not freed" fp-must ;
: slot-deps ( d -- set )
  fp-slot@ dup lf-slot-deps @ swap lf-slot-count @ over + swap
  0 -rot ?do 1 i fp-pool store-slot @ lshift or loop ;

\ ---------------------------------------------------------------------------
\ Per-step invariants. Before the step: a copy of every slot and of the
\ pool's records, and the pool's count.
create slots-before most /lf-slot * allot
create pool-before 64 cells allot
variable pool-count
: slots-bytes ( -- addr u ) 0 fp-slot@ lf-input-count /lf-slot * ;
: pool-bytes ( -- addr u ) fp-pool store-records pool-count @ cells ;
: snap ( -- )
  slots-bytes slots-before swap move fp-pool store-count @ pool-count !
  pool-bytes pool-before swap move ;
: slot-before ( d -- addr ) /lf-slot * slots-before + ;
: same-slot? ( d -- flag ) dup fp-slot@ /lf-slot rot slot-before /lf-slot compare 0= ;
: others-same? ( i -- flag )
  true lf-input-count 0 ?do over i <> if i same-slot? and then loop nip ;
: pool-kept? ( -- flag ) pool-bytes pool-before pool-count @ cells compare 0= ;
\ The pool grew by exactly slot i's dependencies if it was accepted.
: grown ( i -- n ) fp-slot@ dup lf-slot-accepted? if lf-slot-count @ else drop 0 then ;
: pool-grown? ( i -- flag ) grown pool-count @ + fp-pool store-count @ = ;
\ Every input store back at its mark, the name bytes too, the input intact
\ and its fingerprint the one recorded when loading ended.
: store-back? ( k -- flag )
  dup lf-input-mark mark-count @ swap lf-input-store store-count @ = ;
: rolled-back? ( -- flag )
  true lf-input-stores# 0 ?do i store-back? and loop
  lf-name-used @ lf-input-bytes @ = and lf-input-intact? and
  lf-input-print lf-input-fingerprint = and ;
: step-kept ( i -- )
  dup others-same? s" another slot changed" fp-must
  pool-kept? s" the pool's records changed" fp-must
  pool-grown? s" the pool grew wrongly" fp-must
  rolled-back? s" a store was not rolled back" fp-must ;

\ ---------------------------------------------------------------------------
\ One run, driven as lf-env-run drives it: per slot the outcome published
\ (-1 while open), the slot where the injected failure was reached (-1
\ for none), and whether a publisher fault stopped the run.
create got most cells allot
: got@ ( d -- outcome ) cells got + @ ;
: got! ( outcome d -- ) cells got + ! ;
variable fired
variable stopped
: fresh-got ( -- ) got most cells -1 fill -1 fired ! false stopped ! ;
\ Check declaration i with lf-env-step: the outcome published, whether
\ the run must stop, and whether the injected failure was reached in it.
: fired? ( hit-before -- flag ) 0= af-hit 0<> and ;
: step-run ( i -- outcome fault? reached? )
  af-hit >r ['] lf-check-declaration swap lf-env-step r> fired? ;
\ Note the step's coverage, and the outcome when the slot is final.
: step-record ( i outcome fault? -- )
  stopped ! lf-check-step@ over reach over fp-slot@ lf-slot-final?
  if swap got! else 2drop then ;
: fp-step ( i -- )
  dup fp-slot ! snap dup >r step-run if r@ fired ! then
  r@ -rot step-record r> step-kept ;
: fp-steps ( -- )
  fresh-got lf-input-count 0 ?do i fp-step stopped @ if leave then loop ;
: .outcome ( outcome -- ) dup -1 = if drop ." open" else outcome-text type then ;
: .slot-outcomes ( -- )
  fp-slot @ dup lf-input-count u< 0= if drop exit then
  ."  (" dup got@ .outcome ." , baseline " base@ .outcome ." , step "
  lf-check-step@ 0 .r ." , diagnostic " lf-diag-code@ 0 .r ." )" ;
' .slot-outcomes is .fp-slot

\ ---------------------------------------------------------------------------
\ The rules after a run.
: accepted-now? ( d -- flag ) got@ ok? ;
: deps-accepted? ( d -- flag )
  deps@ true lf-input-count 0 ?do over 1 i lshift and if i accepted-now? and then loop
  nip ;
: sound? ( d -- flag )
  dup accepted-now? 0= if drop true exit then dup base@ ok? swap deps-accepted? and ;
\ Whether every slot before d has its baseline outcome.
: prior-same? ( d -- flag ) true swap 0 ?do i got@ i base@ = and loop ;
\ The outcomes slot d may have where no injected failure was reached.
: fuel-early? ( d outcome -- flag )
  fp-mode @ 2 = if outcome-exhausted = nip else 2drop false then ;
: allowed? ( d outcome -- flag )
  2dup swap base@ = if 2drop true exit then 2dup fuel-early? if 2drop true exit then
  outcome-unknown = swap prior-same? 0= and ;
\ The slot an injected failure reached: open and cleared after a fault
\ in the publisher; else full after a refusal, invalid after a THROW. A
\ refusal in the analysis that looks for a rejection after an undecided
\ comparison is full too since plan task 4.2.2c (ADR 0008: with more room
\ it might reject); before, it left the step unknown.
create cleared /lf-slot allot  cleared /lf-slot erase
outcome-invalid cleared lf-slot-outcome !
: cleared? ( d -- flag ) fp-slot@ /lf-slot cleared /lf-slot compare 0= ;
: failed-outcome ( -- outcome ) fp-mode @ 3 = if outcome-invalid else outcome-full then ;
: failed-ok? ( d outcome -- flag ) nip failed-outcome = ;
: fired-ok? ( d -- flag )
  stopped @ if dup got@ -1 = swap cleared? and else dup got@ failed-ok? then ;
: slot-rule ( d -- )
  dup fp-slot ! dup sound? s" accepted without cause" fp-must
  dup fired @ = if fired-ok? s" a failure published wrongly" fp-must exit then
  dup got@ -1 = if drop stopped @ s" a slot left open" fp-must exit then
  dup got@ allowed? s" an outcome not allowed" fp-must ;
: rules ( -- ) lf-input-count 0 ?do i slot-rule loop ;

\ ---------------------------------------------------------------------------
\ Handles and printed verdicts, read in a view after the run: an accepted
\ slot has a valid handle and prints "accepted" with the axiom set it
\ holds, and no label (owner, 2026-11-12); any other has none and prints its outcome alone. TYPE is
\ deferred on both Gforth hosts, so its action is replaced while a
\ verdict prints (output past the buffer is dropped).
160 constant text-room
create printed text-room allot
variable printed#
: grab ( c-addr u -- )
  text-room printed# @ - min tuck printed printed# @ + swap move printed# +! ;
: captured ( d -- c-addr u )
  0 printed# ! ['] type defer@ >r ['] grab is type
  ['] lf-check-verdict. catch r> is type throw printed printed# @ ;
create wanted text-room allot
variable wanted#
: want ( c-addr u -- ) tuck wanted wanted# @ + swap move wanted# +! ;
\ The axiom set: none, or the allowlist's names of the listed bits, then
\ unlisted, comma-separated (core/axiom-allowlist.fs).
: want-bit ( bits bit -- bits )
  2dup and 0= if drop exit then
  dup lf-axiom-unlisted = if s" unlisted" else dup lf-axiom-name then want
  2* 1- invert over and if s" , " want then ;
: want-accepted ( bits -- )
  s" accepted; axioms: " want
  ?dup 0= if s" none" want exit then
  lf-axiom-propext want-bit lf-axiom-choice want-bit lf-axiom-sound want-bit
  lf-axiom-unlisted want-bit drop ;
\ Any other: skipped (plan task 5.2.7), or the outcome's name.
: want-failed ( d outcome -- )
  swap lf-env-skipped? if drop s" skipped" else outcome-text then want ;
: wanted-text ( d -- c-addr u )
  0 wanted# ! dup lf-env-outcome dup ok? if drop lf-env-axioms drop want-accepted
  else want-failed then wanted wanted# @ ;
: verdict-ok? ( d -- flag ) dup captured rot wanted-text compare 0= ;
: handle-ok? ( d -- flag )
  dup lf-env-outcome ok? swap lf-env-handle ok? >r lf-env-handle? ok? r> and = ;
: read-back? ( d -- flag ) dup lf-env-outcome swap got@ outcome-sane = ;
: report-ok ( d -- )
  dup fp-slot ! dup read-back? s" read back wrongly" fp-must
  dup handle-ok? s" a handle disagrees" fp-must
  verdict-ok? s" a verdict misprinted" fp-must ;
\ An axiom bit planted in an accepted slot must show in its verdict.
: axiom-shows? ( d -- flag )
  dup fp-slot@ lf-slot-axioms 1 over ! swap captured rot 0 swap !
  s" accepted; axioms: propext" compare 0= ;
: axioms-ok ( d -- )
  dup lf-env-outcome ok? if axiom-shows? s" stale axioms" fp-must else drop then ;
: reports ( -- )
  lf-env-view ok? s" no view" fp-must lf-input-count 0 ?do i report-ok i axioms-ok loop ;

\ ---------------------------------------------------------------------------
\ Runs in the current context, which must stay usable (not spent).
variable runs#        \ injected runs (refusal, fuel and THROW)
\ A case's word ( -- ) run before each run, so that a growable store
\ starts every run with the same block (default: nothing).
variable fp-prepare  ' noop fp-prepare !
: prepared ( -- ) fp-prepare @ execute ;
: fp-run-once ( -- )
  prepared fp-open fp-steps af-off rules reports fp-close
  lf-env-spent? 0= s" context spent" fp-must ;
: all-base? ( -- flag ) true lf-input-count 0 ?do i got@ i base@ = and loop ;
\ The baseline, with the allocations counted per declaration.
: base-step ( i -- ) dup fp-step af-seen@ swap cells base-allocs + ! ;
: base-steps ( -- ) fresh-got lf-input-count 0 ?do i base-step loop ;
: baseline-record ( -- )
  lf-input-count 0 ?do i got@ i cells base-outcome + ! i slot-deps i cells base-deps + !
  loop ;
: baseline ( -- )
  0 fp-mode ! 0 fp-run ! fuel lf-check-budget prepared 0 af-arm fp-open base-steps
  af-seen@ allocs# ! baseline-record af-off reports fp-close ;
\ A clean run afterwards, in the same context, gives the baseline.
: clean-run ( -- )
  0 fp-mode ! fuel lf-check-budget af-off fp-run-once
  all-base? s" a clean run differs" fp-must ;

\ The refusal sweep: the run reaches k exactly when the baseline does.
: refused-run ( k -- )
  dup fp-run ! dup af-arm fp-run-once 1 runs# +!
  allocs# @ > fired @ 0< = s" injection reached wrongly" fp-must ;
: refusals ( -- )
  1 fp-mode ! fuel lf-check-budget allocs# @ 2 + 1 do i refused-run loop ;

\ The fuel sweep: fuel 0, 1, ... until every slot has its baseline outcome.
: fuel-run ( f -- ) dup fp-run ! lf-check-budget fp-run-once 1 runs# +! ;
: fuel-sweep ( -- )
  2 fp-mode ! af-off 0 begin dup fuel-run all-base? 0= while 1+
  dup 1000000 < s" fuel sweep did not end" fp-must repeat drop ;

\ ---------------------------------------------------------------------------
\ THROW runs, each in a new context ("home") holding the case's input;
\ after a THROW in a check the run goes on in contexts from fp-maker.
: fp-fill ( context -- )
  lf-context @ >r context-use fp-load fuel lf-check-budget r> context-use ;
: fp-maker ( -- context ior ) context-new ?dup if exit then dup fp-fill 0 ;
: no-maker ( -- context ior ) 0 -1 ;
: home ( -- context )
  context-new 0= s" no context" fp-must dup context-use fp-load fuel lf-check-budget ;
: leave-home ( context -- )
  context-main context-use context-free 0= s" not freed" fp-must ;
\ The slot whose check or publication made allocation k.
: owner-slot ( k -- d )
  lf-input-count 0 ?do dup i allocs@ <= if drop i unloop exit then loop drop -1 ;
\ Read the slots back after a run with lf-env-run.
: got-final ( d -- )
  dup fp-slot@ dup lf-slot-final? if lf-slot-outcome@ else drop -1 then swap got! ;
: got-all ( -- ) fresh-got lf-input-count 0 ?do i got-final loop ;
\ The slot the THROW reached; a THROW in the publisher leaves it open.
: thrown-at ( k -- ) owner-slot dup fired ! got@ -1 = stopped ! ;
: run-outcome-ok? ( run-outcome -- flag )
  stopped @ if outcome-invalid else outcome-ok then = ;
\ The coverage of a THROW: in a check, the step it reached; else 9.
: thrown-reach ( -- ) stopped @ if 9 else lf-check-step@ then outcome-invalid reach ;
: thrown-ok ( run-outcome k -- )
  got-all thrown-at run-outcome-ok? s" the run's outcome" fp-must thrown-reach
  rules reports lf-env-spent? stopped @ 0= = s" spent wrongly" fp-must
  rolled-back? s" a store was not rolled back" fp-must ;
: thrown-run ( k -- )
  3 fp-mode ! dup fp-run ! home >r prepared fp-open af-arm-throw
  ['] lf-check-declaration ['] fp-maker lf-env-run af-off fp-run @ thrown-ok
  fp-close r> leave-home 1 runs# +! ;
: throws ( -- ) allocs# @ 1+ 1 ?do i thrown-run loop ;
\ With no maker, a THROW in the first check stops the run: invalid, that
\ slot invalid, every later one open, the context spent.
: later-open? ( -- flag ) true lf-input-count 1 ?do i got@ -1 = and loop ;
: stops-ok ( run-outcome -- )
  outcome-invalid = s" the run went on" fp-must got-all
  0 got@ outcome-invalid = s" a THROW not invalid" fp-must
  later-open? s" a slot published after the stop" fp-must
  lf-env-spent? s" not spent" fp-must ;
: no-maker-run ( -- )
  3 fp-mode ! 1 fp-run ! home >r prepared fp-open 1 af-arm-throw
  ['] lf-check-declaration ['] no-maker lf-env-run af-off stops-ok
  fp-close r> leave-home 1 runs# +! ;

\ ---------------------------------------------------------------------------
\ A case: the expected baseline outcome of each declaration on the stack
\ (the first deepest), their number, the loader and the name.
: fp-name! ( c-addr u -- ) dup fp-case# ! fp-case-name swap move ;
: expect-base ( outcome d -- ) dup fp-slot ! base@ = s" baseline differs" fp-must ;
: expected ( outcome*n n -- )
  dup lf-input-count = s" wrong number of declarations" fp-must
  0 ?do lf-input-count 1- i - expect-base loop ;
\ An accepted declaration has its type inferred, which allocates, so a
\ case with one must count allocations: else the hook is not working.
: any-accepted? ( -- flag ) false lf-input-count 0 ?do i base@ ok? or loop ;
: allocations-counted ( -- )
  any-accepted? 0= allocs# @ 0> or s" no allocation counted" fp-must ;
: fp-case ( outcome*n n xt c-addr u -- )
  fp-name! fp-loader ! fp-load baseline expected allocations-counted
  refusals fuel-sweep throws clean-run ;

\ ---------------------------------------------------------------------------
\ The pinned fixtures, every declaration accepted.
: composition ( -- ) s" tests/reference/composition.ndjson" ndjson ;
: identity ( -- ) s" tests/reference/identity.ndjson" ndjson ;
: type-identity ( -- ) s" tests/reference/type-identity.ndjson" ndjson ;
: poly-identity ( -- ) s" tests/reference/poly-identity.ndjson" ndjson ;
: constant-fixture ( -- ) s" tests/reference/constant-fixture.ndjson" ndjson ;
T{ outcome-ok 1 ' composition s" composition" fp-case -> }T
T{ outcome-ok 1 ' identity s" identity" fp-case -> }T
T{ outcome-ok 1 ' type-identity s" type-identity" fp-case -> }T
T{ outcome-ok 1 ' poly-identity s" poly-identity" fp-case -> }T
T{ outcome-ok outcome-ok outcome-ok 3 ' constant-fixture s" constant-fixture" fp-case
  -> }T
T{ ' composition fp-loader ! no-maker-run -> }T
T{ ' constant-fixture fp-loader ! no-maker-run -> }T

\ ---------------------------------------------------------------------------
\ Cases of tests/core/check-declaration.fs that end elsewhere, the step
\ where the last declaration stops in brackets. A loader of several
\ declarations evaluates one driver line for each.
: fc-end ( -- ) lf-input-end ok? s" not loaded" fp-must ;
: fc-text ( c-addr u -- ) fc-world evaluate fc-end ;
\ Rejected: N2 (2), L3 (3), L2 in the declared type (4), S1 (5), S3 (6),
\ N1 in the value (7), the value's type apart from the declared one (8).
: n2 ( -- )
  fc-world
  s" fc-decl before thm safe idProp 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 V 0" evaluate
  s" fc-decl check thm safe idProp 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 V 0" evaluate
  fc-end ;
: l3 ( -- ) s" fc-decl check def safe repeated 2 u u TYPE S s z VALUE S z" fc-text ;
: l2-type ( -- ) s" fc-decl check def safe undeclared 1 u TYPE S s p v VALUE S p v" fc-text ;
: s1 ( -- ) s" fc-decl check thm safe notType 0 TYPE L S z V 0 VALUE L S z V 0" fc-text ;
: s3 ( -- )
  s" fc-decl check thm safe overType 0 TYPE P S s z P V 0 V 1 VALUE L S s z L V 0 V 0"
  fc-text ;
: n1 ( -- )
  s" fc-decl check thm safe useMissing 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 A A C missing 0 V 1 V 0"
  fc-text ;
: d-value ( -- )
  s" fc-decl check thm safe wrong 0 TYPE P S z P S z P V 1 V 2 VALUE L S z L S z L V 0 V 0"
  fc-text ;
T{ outcome-ok outcome-rejected 2 ' n2 s" n2" fp-case -> }T
T{ outcome-rejected 1 ' l3 s" l3" fp-case -> }T
T{ outcome-rejected 1 ' l2-type s" l2" fp-case -> }T
T{ outcome-rejected 1 ' s1 s" s1" fp-case -> }T
T{ outcome-rejected 1 ' s3 s" s3" fp-case -> }T
T{ outcome-rejected 1 ' n1 s" n1" fp-case -> }T
T{ outcome-rejected 1 ' d-value s" d-value" fp-case -> }T

\ Unknown: K5 in the type (4) and in the value (7), after a definition
\ without a value (invalid in the audit, 1); K6, a specialized level that
\ depends on object sharing in Lean (7, ADR 0011 Amendment 1). A level
\ equal only after Lean's normalisation (formerly K4) is accepted, as
\ Lean accepts it.
: broken ( -- ) fc-world s" fc-decl before def safe broken 0 TYPE S s z VALUE none" evaluate ;
: k5-type ( -- )
  broken s" fc-decl check def safe both 0 TYPE C broken 0 VALUE C missing 0" evaluate fc-end ;
: k5-value ( -- )
  broken s" fc-decl check def safe user 0 TYPE S s z VALUE C broken 0" evaluate fc-end ;
: k4-level ( -- )
  s" fc-decl check def safe spelling 1 u TYPE P S p u P V 0 V 1 VALUE L S m p u p u L V 0 V 0"
  fc-text ;
: k6-level ( -- )
  fc-world s" fc-decl before def safe T5 1 u TYPE S s i s z s p u VALUE S i s z s p u"
  evaluate s" fc-decl check def safe S5 1 u TYPE S s i s z s p u VALUE C T5 1 p u"
  evaluate fc-end ;
T{ outcome-invalid outcome-unknown 2 ' k5-type s" k5-type" fp-case -> }T
T{ outcome-invalid outcome-unknown 2 ' k5-value s" k5-value" fp-case -> }T
T{ outcome-ok 1 ' k4-level s" k4" fp-case -> }T
T{ outcome-ok outcome-unknown 2 ' k6-level s" k6" fp-case -> }T

\ Axioms (plan task 5.3.1): one whose type names nothing (N1, rejected),
\ a use of one in a declared type (rejected: the value has another type)
\ and in a value (accepted). A let (U2): unsupported in the audit (1).
: postulate ( -- )
  fc-world s" fc-decl before ax safe postulate 0 TYPE S z VALUE none" evaluate ;
: axiom ( -- ) s" fc-decl check ax safe postulate 0 TYPE C missing 0 VALUE none" fc-text ;
: let-form ( -- ) s" fc-decl check def safe withLet 0 TYPE S s z VALUE Xlet" fc-text ;
: uses-axiom-type ( -- )
  postulate s" fc-decl check def safe user 0 TYPE C postulate 0 VALUE S z" evaluate fc-end ;
: uses-axiom ( -- )
  postulate s" fc-decl check def safe user 0 TYPE S z VALUE C postulate 0" evaluate fc-end ;
\ And N2 after an axiom of the same name (rejected, 2).
: n2-unsupported ( -- )
  fc-world s" fc-decl before ax safe idProp 0 TYPE S z VALUE none" evaluate
  s" fc-decl check thm safe idProp 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 V 0" evaluate
  fc-end ;
T{ outcome-rejected 1 ' axiom s" axiom" fp-case -> }T
T{ outcome-unsupported 1 ' let-form s" let" fp-case -> }T
T{ outcome-ok outcome-rejected 2 ' uses-axiom-type s" uses-axiom-type"
  fp-case -> }T
T{ outcome-ok outcome-ok 2 ' uses-axiom s" uses-axiom" fp-case -> }T
T{ outcome-ok outcome-rejected 2 ' n2-unsupported s" n2-unsupported"
  fp-case -> }T
\ K5: a use of an unsupported declaration (a definition with a form U2
\ refuses) in a declared type (4) and in a value (7), and N2 after one of
\ the same name (2).
: risky ( -- )
  fc-world s" fc-decl before def safe risky 0 TYPE S s z VALUE Xlet" evaluate ;
: uses-risky-type ( -- )
  risky s" fc-decl check def safe user 0 TYPE C risky 0 VALUE S z" evaluate fc-end ;
: uses-risky ( -- )
  risky s" fc-decl check def safe user 0 TYPE S s z VALUE C risky 0" evaluate fc-end ;
: n2-risky ( -- )
  fc-world s" fc-decl before def safe idProp 0 TYPE S s z VALUE Xlet" evaluate
  s" fc-decl check thm safe idProp 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 V 0" evaluate
  fc-end ;
T{ outcome-unsupported outcome-unsupported 2 ' uses-risky-type s" uses-risky-type"
  fp-case -> }T
T{ outcome-unsupported outcome-unsupported 2 ' uses-risky s" uses-risky" fp-case -> }T
T{ outcome-unsupported outcome-unsupported 2 ' n2-risky s" n2-risky" fp-case -> }T
\ A skipped declaration (an unsafe definition; plan task 5.2.7), rejected
\ unchecked, and a use of it in a declared type (4) and in a value (7):
\ no constant (N1); N2 after one of the same name (2): its name is taken.
: unsafe-world ( -- )
  fc-world s" fc-decl before def unsafe unsafe 0 TYPE S s z VALUE S z" evaluate ;
: uses-unsafe-type ( -- )
  unsafe-world s" fc-decl check def safe user 0 TYPE C unsafe 0 VALUE S z" evaluate
  fc-end ;
: uses-unsafe ( -- )
  unsafe-world s" fc-decl check def safe user 0 TYPE S s z VALUE C unsafe 0" evaluate
  fc-end ;
: n2-unsafe ( -- )
  fc-world s" fc-decl before def unsafe idProp 0 TYPE S s z VALUE S z" evaluate
  s" fc-decl check thm safe idProp 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 V 0" evaluate
  fc-end ;
T{ outcome-rejected outcome-rejected 2 ' uses-unsafe-type s" uses-unsafe-type"
  fp-case -> }T
T{ outcome-rejected outcome-rejected 2 ' uses-unsafe s" uses-unsafe" fp-case -> }T
T{ outcome-rejected outcome-rejected 2 ' n2-unsafe s" n2-unsafe" fp-case -> }T

\ Invalid: a variable without a binder (V1, 1). Full: the term store fills
\ while the declared type is inferred (4): a telescope of 40 binders,
\ Prop -> ... -> Prop, whose 41 nodes and a free variable per binder (plan
\ task 4.2.2a) do not fit the 64 terms. (The binder-domain table's eta
\ case, used here before, now fits: inference discards its scratch as it
\ goes.)
: loose ( -- )
  s" fc-decl check thm safe loose 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 V 2" fc-text ;
: terms-full ( -- )
  s" fc-decl check def safe wide 0 TYPE P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z S z VALUE S z"
  fc-text ;
T{ outcome-invalid 1 ' loose s" loose" fp-case -> }T
T{ outcome-full 1 ' terms-full s" terms-full" fp-case -> }T
\ The binder-domain table's eta case with the term store's capacity
\ raised, a setting of the context (plan task 3.3.1; ADR 0016 C5): the
\ store and its columns grow while the types are inferred and compared,
\ and every growth is an allocation the sweeps refuse or make throw:
\ full, never accepted. Accepted when nothing is refused (eta, plan task
\ 4.2.4; Lean accepts). The capacity goes back to the default afterwards.
: eta-compare ( -- )
  s" fc-decl check thm safe bdCompare 0 TYPE P P P S s z P A L S s z V 0 P V 0 V 1 P V 1 V 2 S z P A V 0 L S s z L A L S s z V 0 P V 0 V 1 V 0 A V 1 L S s z L P V 0 V 1 L V 1 A V 1 V 0 VALUE L P P S s z P A L S s z V 0 P V 0 V 1 P V 1 V 2 S z L A V 0 L S s z L A L S s z V 0 P V 0 V 1 V 0 V 0"
  fc-text ;
\ Before each run the block shrinks to the input and the columns are made
\ as large as the capacity, and the local context's block (which grows
\ when a check opens more than lf-lctx-default binders) shrinks to its
\ first size, so that every run grows the stores at the same allocations
\ (blocks never shrink by themselves).
4096 constant grown
: grown-capacity ( n -- ) lf-term-capacity! ok? s" no setting" fp-must ;
: column-grown ( column -- ) grown swap column-slab column-reserve ok? s" no column" fp-must ;
: lctx-capacity ( n -- ) lf-lctx-capacity! ok? s" no local context" fp-must ;
: lctx-first ( -- )
  lf-lctx-reset lf-lctx-default lctx-capacity lf-lctx-default-limit lctx-capacity ;
: grown-block ( -- )
  lf-term-count @ grown-capacity grown grown-capacity
  ['] column-grown lf-term-columns columns-each lctx-first ;
: terms-grown ( -- ) lf-term-reset grown grown-capacity eta-compare ;
' grown-block fp-prepare !
T{ outcome-ok 1 ' terms-grown s" terms-grown" fp-case -> }T
' noop fp-prepare !
lf-input-reset lf-term-reset lf-term-default grown-capacity

\ Accepted with two dependencies, whose publication appends two pool
\ entries: a refusal or THROW at the second must take the first back.
: dependencies ( -- )
  fc-world
  s" fc-decl before def safe fixtureId 1 u TYPE P S p u P V 0 V 1 VALUE L S p u L V 0 V 0"
  evaluate
  s" fc-decl before thm safe fixtureUse 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 A A C fixtureId 1 z V 1 V 0"
  evaluate
  s" fc-decl check thm safe cites 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 A A C fixtureUse 0 V 1 A A C fixtureId 1 z V 1 V 0"
  evaluate fc-end ;
T{ outcome-ok outcome-ok outcome-ok 3 ' dependencies s" dependencies" fp-case -> }T

\ A check outside any check's snapshot (here a view's) ends before step
\ 1, invalid.
: outside ( -- outcome step )
  fp-open lf-env-view ok? s" no view" fp-must lf-check-declaration
  lf-env-cand lf-cand-outcome @ lf-check-step@ 2dup swap reach fp-close ;
T{ composition outside -> outcome-invalid 0 }T

\ The publisher's re-check: a check of composition that passes, then
\ claims an axiom its dependencies do not have, is published invalid
\ (diagnostic 28, part 2: the axiom set), its slot final, with no handle.
: lying-check ( -- ) lf-check-declaration 1 lf-env-cand lf-cand-axioms ! ;
: lied ( -- outcome fault? step code read handle )
  composition fp-open ['] lying-check 0 lf-env-step lf-check-step@ lf-diag-code@
  lf-env-view ok? s" no view" fp-must 0 lf-env-outcome 0 lf-env-handle nip nip
  fp-close ;
T{ lied -> outcome-invalid false lf-step-done lf-diag-recheck outcome-invalid outcome-invalid }T

\ ---------------------------------------------------------------------------
\ Coverage. Each step must reach exactly these outcomes; a cell that is
\ empty is reached by no run of these cases: steps 2, 3, 5 and 6 make no
\ allocation but the growth of the check's lookup list (plan step SN3;
\ kernel/environment.fs, "Lookups": a THROW there is invalid, a refusal
\ leaves the check's outcome and makes the publisher's full, tested in
\ tests/core/env-snapshot.fs) and steps 2 and 3 use no fuel (step 5 runs out of fuel only
\ while Lean's whnf reduces the type's type: exhausted, since plan task
\ 4.2.2c; before, in ADR 0011's search for a rejection, unknown); a THROW is
\ injected only at an allocation, so invalid needs one (or V1 in the
\ audit, or a failed publication after step 8); and step 8 allocates, in
\ terms-grown, while it reduces (a refused growth of the term store: full).
\ No case ends unknown at step 8 since terms-grown's eta comparison is
\ decided (plan task 4.2.4). Step 1 rejects a skipped declaration (plan
\ task 5.2.7).
: outcome-named ( c-addr u -- outcome )
  7 0 do 2dup i outcome-text compare 0= if 2drop i unloop exit then loop
  true abort" failure-paths: not an outcome" ;
: names>set ( "name ...<eol>" -- set )
  0 begin parse-name dup while outcome-named 1 swap lshift or repeat 2drop ;
create expected-reach steps# cells allot  expected-reach steps# cells erase
: reaches: ( step "name ...<eol>" -- ) names>set swap cells expected-reach + ! ;
0 reaches: invalid
1 reaches: invalid exhausted rejected unsupported
2 reaches: invalid unknown rejected unsupported
3 reaches: invalid rejected
4 reaches: invalid exhausted unknown rejected unsupported full
5 reaches: invalid exhausted rejected
6 reaches: invalid exhausted rejected
7 reaches: invalid exhausted unknown rejected unsupported full
8 reaches: invalid exhausted rejected full
9 reaches: ok invalid

: .outcomes ( set -- )
  7 0 do dup 1 i lshift and if i outcome-text type space then loop drop ;
: reached@ ( step -- set ) cells reached + @ ;
: expected@ ( step -- set ) cells expected-reach + @ ;
: .expected ( step -- )
  dup reached@ over expected@ <> if ." -- expected: " dup expected@ .outcomes then drop ;
: .step ( step -- ) dup 0 .r ." : " dup reached@ .outcomes .expected cr ;
: coverage-ok? ( -- flag ) true steps# 0 do i reached@ i expected@ = and loop ;
cr ." Outcomes reached per check step (0 before a snapshot, 9 every step done):" cr
: .coverage ( -- ) steps# 0 do i .step loop ;
.coverage
." Injected runs (refusal, fuel and THROW): " runs# @ . cr
T{ coverage-ok? -> true }T
cases-done
bye

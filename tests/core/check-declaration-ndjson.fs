\ The first checker end to end from lean4export NDJSON files (plan task
\ 2.2.3): the pinned exports of four fixtures (composition, type_identity,
\ poly_identity and the constant fixture, tests/reference/*.ndjson) are
\ read with the checker-input module src/import/checker-input.fs (each also checked
\ against its manifest) and
\ checked by check-declaration through the checked environment: every
\ declaration accepted, with a valid handle and no axioms. Four copies of
\ the composition export changed by hand (tests/core/check-declaration-cases)
\ reach the other outcomes: g applied to value instead of f value
\ (rejected; Lean's appTypeMismatch, row composition.wrong-argument of the
\ expected-results table), the statement assumed as an axiom
\ (unsupported, U1), a natural-number literal as the value (unsupported,
\ U2), and a variable without a binder (invalid, V1). A fifth copy, with
\ a numeric name part of 2^64 (tests/cli/composition-huge-number.ndjson),
\ must stop reading as full.
\ Test-only; nothing here accepts a theorem outside the code under test.
include ../support/tester.fs
include ../support/checks.fs
require ../../src/import/checker-input.fs
require ../../src/kernel/check-declaration.fs

: must ( flag -- ) 0= abort" check-declaration-ndjson: refused" ;
100000 constant fuel
variable the-env

\ Read and check a file: the run's outcome; the environment stays current
\ for the queries below, and env-done frees it.
: checked ( c-addr u -- outcome )
  cin-read ok? must fuel 64 lf-check-input swap the-env ! lf-env-view ok? must ;
: env-done ( -- ) the-env @ lf-env-free ok? must ;
\ Declaration d accepted, with a handle valid in the view, and no axioms.
: accepted? ( d -- flag )
  dup lf-env-outcome ok? over lf-env-handle ok? >r lf-env-handle? ok? r> and and
  swap lf-env-axioms ok? swap 0= and and ;
: all-accepted? ( -- flag ) true lf-input-count 0 ?do i accepted? and loop ;
\ The number of declarations and whether all were accepted; then freed.
: verdicts ( -- n flag ) lf-input-count all-accepted? env-done ;
: last-outcome ( -- outcome code step )
  lf-input-count 1- lf-env-outcome lf-diag-code@ lf-check-step@ ;

T{ s" tests/reference/composition.ndjson" checked verdicts -> outcome-ok 1 true }T
T{ s" tests/reference/type-identity.ndjson" checked verdicts -> outcome-ok 1 true }T
T{ s" tests/reference/poly-identity.ndjson" checked verdicts -> outcome-ok 1 true }T
T{ s" tests/reference/constant-fixture.ndjson" checked verdicts -> outcome-ok 3 true }T

\ The changed copies: the run ends ok, the declaration does not.
: case-file ( c-addr u -- outcome code step )
  checked ok? must last-outcome env-done ;
T{ s" tests/core/check-declaration-cases/composition-wrong-argument.ndjson" case-file
  -> outcome-rejected lf-diag-argument-apart 7 }T
T{ s" tests/core/check-declaration-cases/composition-postulate.ndjson" case-file
  -> outcome-unsupported lf-diag-unsupported-kind 1 }T
T{ s" tests/core/check-declaration-cases/composition-literal.ndjson" case-file
  -> outcome-unsupported lf-diag-unsupported-form 1 }T
T{ s" tests/core/check-declaration-cases/composition-loose.ndjson" case-file
  -> outcome-invalid lf-diag-out-of-scope 1 }T

\ The reader fails closed on a file that is not an export.
T{ s" tests/core/check-declaration-ndjson.fs" cin-read ok? -> false }T

\ With the manifest checked: the fixtures read as before; a changed copy
\ without a manifest is refused as invalid, with the manifest's reason,
\ and nothing is loaded; staged without the manifest, it reads.
: sealed? ( -- flag ) lf-input-sealed? ;
\ The reason cin-error gives is c-addr u.
: why? ( c-addr u -- flag ) cin-error 2>r 2drop drop 2r> compare 0= ;
T{ s" tests/reference/composition.ndjson" cin-read-checked sealed? -> outcome-ok true }T
T{ s" tests/reference/constant-fixture.ndjson" cin-read-checked lf-input-count
  -> outcome-ok 3 }T
: case-wrong ( -- c-addr u )
  s" tests/core/check-declaration-cases/composition-wrong-argument.ndjson" ;
T{ case-wrong cin-read-checked sealed? -> outcome-invalid false }T
T{ s" manifest missing, unreadable or too large" why? -> true }T
T{ case-wrong cin-read sealed? -> outcome-ok true }T

\ A handler's refusal carries its own reason, and the reader's line: an
\ inductive type (line 51 of the export of every record kind) is
\ unsupported. tests/cli/test_leanforth.py reaches full with a larger file.
: line@ ( -- line ) cin-error 2drop 2drop ;
T{ s" tests/core/reexport/kinds.ndjson" cin-read sealed? line@
  -> outcome-unsupported false 51 }T
T{ s" an inductive type (not supported yet)" why? -> true }T

\ A numeric name part is staged only when it fits a cell, never wrapped
\ into another number (another name): composition with the part 0 of
\ a._@._internal._hyg.0 changed to 2^64 is full, at its line, 12.
T{ s" 0" cin-digits s" 007" cin-digits -> 0 true 7 true }T
: max-text ( -- c-addr u ) max-n 0 <# #s #> ;
T{ max-text cin-digits -> max-n true }T
T{ s" 18446744073709551616" cin-digits s" 99999999999999999999999" cin-digits
  -> false false }T
T{ s" tests/cli/composition-huge-number.ndjson" cin-read
  sealed? line@ -> outcome-full false 12 }T
T{ s" a numeric name part larger than the check holds" why? -> true }T

\ ---------------------------------------------------------------------------
\ The same exports staged in the compact store (src/import/stage.fs) and
\ fed to the checker in file order (src/import/feed.fs, plan task 3.2.2):
\ the names stay in the shared input tier, the stores grow to the feed's
\ capacities, and every verdict is the same as above.
require ../../src/import/feed.fs
create stg /stage allot
create fdd /feed allot
: staged ( c-addr u -- ) 16 stg stage-init ok? must stg stage-load-unchecked ok? must ;
: fed ( c-addr u -- outcome ) staged stg fdd lf-feed ;
: unstage ( -- ) lf-name-detach stg stage-free ;
: fed-checked ( c-addr u -- outcome )
  fed ok? must fuel 64 lf-check-input swap the-env ! lf-env-view ok? must ;
T{ s" tests/reference/composition.ndjson" fed-checked verdicts unstage
   -> outcome-ok 1 true }T
T{ s" tests/reference/type-identity.ndjson" fed-checked verdicts unstage
   -> outcome-ok 1 true }T
T{ s" tests/reference/poly-identity.ndjson" fed-checked verdicts unstage
   -> outcome-ok 1 true }T
T{ s" tests/reference/constant-fixture.ndjson" fed-checked verdicts unstage
   -> outcome-ok 3 true }T
T{ s" tests/reference/identity.ndjson" fed-checked verdicts unstage -> outcome-ok 1 true }T
: fed-case ( c-addr u -- outcome code step ) fed-checked ok? must last-outcome env-done unstage ;
T{ s" tests/core/check-declaration-cases/composition-wrong-argument.ndjson" fed-case
  -> outcome-rejected lf-diag-argument-apart 7 }T
T{ s" tests/core/check-declaration-cases/composition-postulate.ndjson" fed-case
  -> outcome-unsupported lf-diag-unsupported-kind 1 }T
T{ s" tests/core/check-declaration-cases/composition-literal.ndjson" fed-case
  -> outcome-unsupported lf-diag-unsupported-form 1 }T
T{ s" tests/core/check-declaration-cases/composition-loose.ndjson" fed-case
  -> outcome-invalid lf-diag-out-of-scope 1 }T
\ The stores grew past their defaults, and the names are the stage's: a
\ name made under the view that the stage has gets the stage's ID (here
\ from the stage's own text, which is copied first), a new one the next
\ number.
T{ s" tests/reference/composition.ndjson" fed lf-term-capacity lf-term-default >
   lf-input-indexed? -> outcome-ok true true }T
0 lf-input-name constant comp-name
T{ comp-name lf-name-prefix@ comp-name lf-name-text lf-name-str -> comp-name true }T
lf-name-numbers constant fresh-id
T{ 0 s" not.in.the.stage" lf-name-str -> fresh-id true }T
T{ fresh-id lf-name-text s" not.in.the.stage" compare fresh-id 7 lf-name-num nip
   -> 0 true }T
T{ comp-name fresh-id lf-name-equal? comp-name comp-name lf-name-equal? -> false true }T
unstage
T{ lf-input-indexed? -> false }T
\ Only a sealed stage is fed.
T{ 16 stg stage-init stg fdd lf-feed -> outcome-ok outcome-invalid }T
stg stage-free

\ ADR 0012 E5 against the name-to-declaration array (ADR 0016 C4): with
\ names interned in the input tier, the environment reads a name's chain;
\ for every name, every limit and each slot test the chain gives what the
\ scan of every earlier declaration gives.
variable e5-name  variable e5-test  variable e5-limit
: e5-args ( -- name test limit ) e5-name @ e5-test @ e5-limit @ ;
: e5-same? ( -- flag )
  e5-args lf-env-chain-first e5-args lf-env-scan-first =
  e5-args lf-env-chain-matches e5-args lf-env-scan-matches = and ;
create e5-tests
  ' lf-slot-accepted? , ' lf-slot-undecided? , ' lf-slot-unsupported? , ' lf-slot-open? ,
  ' lf-slot-final? ,
here e5-tests - 1 cells / constant e5-tests#
variable e5-checks
: e5-tested? ( -- flag )
  true e5-tests# 0 ?do i cells e5-tests + @ e5-test ! e5-same? and 1 e5-checks +! loop ;
: e5-named? ( -- flag )
  true lf-name-numbers 0 ?do i e5-name ! e5-tested? and loop ;
: e5-all? ( -- flag )
  true lf-input-count 1+ 0 ?do i e5-limit ! e5-named? and loop ;
: e5-file ( c-addr u -- flag ) fed-checked ok? must e5-all? env-done unstage ;
T{ s" tests/reference/constant-fixture.ndjson" e5-file -> true }T
T{ s" tests/reference/composition.ndjson" e5-file -> true }T
T{ s" tests/core/check-declaration-cases/composition-postulate.ndjson" e5-file -> true }T
\ The theorem declared twice (a copy of the export with its last line
\ repeated): the second is rejected as already declared (N2), as Lean's
\ kernel does, by both paths; its chain holds both.
: twice ( -- c-addr u ) s" tests/core/check-declaration-cases/composition-twice.ndjson" ;
T{ twice case-file -> outcome-rejected lf-diag-already-declared 2 }T
T{ twice fed-case -> outcome-rejected lf-diag-already-declared 2 }T
T{ twice e5-file -> true }T
T{ e5-checks @ 500 > -> true }T
." E5 chain against scan: " e5-checks @ . ." lookups agree" cr

cases-done
bye

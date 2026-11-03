\ The first checker end to end from lean4export NDJSON files (plan task
\ 2.2.3): the pinned exports of four fixtures (composition, type_identity,
\ poly_identity and the constant fixture, tests/reference/*.ndjson) are
\ read with the test-only transport tests/support/ndjson-input.fs and
\ checked by check-declaration through the checked environment: every
\ declaration accepted, with a valid handle and no axioms. Four copies of
\ the composition export changed by hand (tests/core/check-declaration-cases)
\ reach the other outcomes: g applied to value instead of f value
\ (rejected; Lean's appTypeMismatch, row composition.wrong-argument of the
\ expected-results table), the statement assumed as an axiom
\ (unsupported, U1), a natural-number literal as the value (unsupported,
\ U2), and a variable without a binder (invalid, V1).
\ Test-only; nothing here accepts a theorem outside the code under test.
include ../support/tester.fs
include ../support/checks.fs
require ../support/ndjson-input.fs

: must ( flag -- ) 0= abort" check-declaration-ndjson: refused" ;
100000 constant fuel
variable the-env

\ Read and check a file: the run's outcome; the environment stays current
\ for the queries below, and env-done frees it.
: checked ( c-addr u -- outcome )
  ni-read ok? must fuel 64 lf-check-input swap the-env ! lf-env-view ok? must ;
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
T{ s" tests/core/check-declaration-ndjson.fs" ni-read ok? -> false }T

cases-done
bye

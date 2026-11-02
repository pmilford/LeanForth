\ Untrusted diagnostic only. Manual reconstruction, not NDJSON import.
include ../support/tester.fs
include ../../src/core/terms.fs
include ../../src/experimental/levels.fs
include ../../src/experimental/level-scope.fs
include ../../src/experimental/tagged-sort-boundary.fs
include ../../src/experimental/symbolic-session.fs
include ../../src/experimental/generation-handles.fs
include ../../src/experimental/tagged-shift.fs
include ../../src/experimental/tagged-instantiate.fs
include ../../src/experimental/tagged-compare.fs
include ../../src/experimental/tagged-beta.fs
include ../../src/experimental/level-value.fs
include ../../src/experimental/level-compare.fs
include ../../src/experimental/tagged-convert.fs
include ../../src/experimental/tagged-infer.fs
include ../../src/experimental/candidate-definition-probe.fs

variable claim-id
variable value-id
variable sort-id
variable free-id
variable bad-id
variable saved-serial
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ 2 lf-lscope-context-add -> true }T
T{ 2 lf-hlevel-param -> 1 lf-level-serial @ true }T
T{ lf-ssession-begin -> true }T
T{ 1 lf-level-serial @ lf-hterm-sort -> 0 lf-term-serial @ true }T
lf-term-serial @ sort-id !
T{ 0 lf-term-bvar -> 1 true }T
T{ 1 lf-term-bvar -> 2 true }T
T{ 1 2 lf-term-pi -> 3 true }T
T{ 0 3 lf-term-pi -> 4 true }T
lf-term-serial @ claim-id !
T{ 1 1 lf-term-lam -> 5 true }T
T{ 0 5 lf-term-lam -> 6 true }T
lf-term-serial @ value-id !
\ Exact expression nodes 0..6 of tests/reference/constant-fixture.ndjson;
\ fixtureId type=4, value=6, universe parameter name id=2: (A : Sort u) -> A -> A.
T{ 4 claim-id @ 6 value-id @ 10000 lf-candidate-definition-probe -> lf-candidate-ok }T
T{ lf-term-count @ -> 7 }T
T{ lf-level-count @ -> 2 }T
\ A lambda is not itself a type; the checker conservatively reports unknown.
T{ 6 value-id @ 6 value-id @ 10000 lf-candidate-definition-probe -> lf-candidate-unknown }T
\ Both roots are audited before an inconclusive claim can hide a stale value.
lf-term-serial @ constant preaudit-term-serial
lf-level-serial @ constant preaudit-level-serial
T{ 6 value-id @ 6 value-id @ 1+ 10000 lf-candidate-definition-probe -> lf-candidate-invalid }T
T{ lf-term-serial @ lf-level-serial @ -> preaudit-term-serial preaudit-level-serial }T
\ A well-formed wrong value is not evidence of conversion or inequality.
T{ 4 claim-id @ 0 sort-id @ 10000 lf-candidate-definition-probe -> lf-candidate-unknown }T
T{ 4 claim-id @ 6 value-id @ 1+ 10000 lf-candidate-definition-probe -> lf-candidate-invalid }T
T{ 4 claim-id @ 6 value-id @ -1 lf-candidate-definition-probe -> lf-candidate-invalid }T
T{ 4 claim-id @ 6 value-id @ 0 lf-candidate-definition-probe -> lf-candidate-exhausted }T
T{ lf-term-count @ -> 7 }T
T{ lf-level-count @ -> 2 }T
\ Unbound term variable: both claim and value paths fail closed.
T{ 0 lf-hterm-bvar -> 7 lf-term-serial @ true }T
lf-term-serial @ free-id !
T{ 7 free-id @ 6 value-id @ 10000 lf-candidate-definition-probe -> lf-candidate-invalid }T
T{ 4 claim-id @ 7 free-id @ 10000 lf-candidate-definition-probe -> lf-candidate-invalid }T
\ A raw symbolic sort lacks its required generation stamp.
T{ 1 lf-term-symbolic-sort -> 8 true }T
lf-term-serial @ bad-id !
T{ 4 claim-id @ 8 bad-id @ 10000 lf-candidate-definition-probe -> lf-candidate-invalid }T
T{ lf-term-count @ -> 9 }T
T{ lf-level-count @ -> 2 }T
variable saw-ok
variable saw-exhausted
: fuel-sweep ( -- )
  0 saw-ok ! 0 saw-exhausted !
  1000 0 do
    4 claim-id @ 6 value-id @ i lf-candidate-definition-probe
    dup lf-candidate-exhausted = if drop true saw-exhausted ! else
      lf-candidate-ok <> abort" unexpected status" true saw-ok ! then
    lf-term-count @ 9 <> abort" term leak"
    lf-level-count @ 2 <> abort" level leak"
  loop
  saw-ok @ 0= abort" no success"
  saw-exhausted @ 0= abort" no exhaustion" ;
fuel-sweep
\ A failed term allocation after a level allocation must restore both arenas.
: fill-arena ( -- )
  begin lf-term-count @ lf-term-capacity < while
    0 lf-term-bvar 0= abort" setup" drop
  repeat ;
fill-arena
T{ 0 sort-id @ 0 sort-id @ 10000 lf-candidate-definition-probe -> lf-candidate-exhausted }T
T{ lf-term-count @ -> lf-term-capacity }T
T{ lf-level-count @ -> 2 }T
\ A rolled-back allocation identity cannot be reused as a live handle.
9 lf-term-count !
T{ 0 lf-hterm-bvar -> 9 lf-term-serial @ true }T
lf-term-serial @ saved-serial !
9 lf-term-count !
T{ 0 lf-hterm-bvar -> 9 lf-term-serial @ true }T
T{ 4 claim-id @ 9 saved-serial @ 10000 lf-candidate-definition-probe -> lf-candidate-invalid }T
T{ lf-term-count @ -> 10 }T
T{ lf-level-count @ -> 2 }T
\ Mutate the exported identity value's inner body from #0 to #1.
\ This stays closed but its inferred type is conservatively non-convertible.
T{ 1 2 lf-term-lam -> 10 true }T
T{ 0 10 lf-term-lam -> 11 true }T
T{ 4 claim-id @ 11 lf-term-serial @ 10000 lf-candidate-definition-probe -> lf-candidate-unknown }T
T{ lf-term-count @ -> 12 }T
T{ lf-level-count @ -> 2 }T
\ Exact fixture mutation: replace the inner lambda with the earlier Pi.
T{ 0 3 lf-term-lam -> 12 true }T
T{ 4 claim-id @ 12 lf-term-serial @ 10000 lf-candidate-definition-probe
   -> lf-candidate-unknown }T
12 lf-term-count !
\ An out-of-context universe parameter is invalid even when the term is stamped.
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ 2 lf-lscope-context-add -> true }T
T{ 3 lf-hlevel-param -> 1 lf-level-serial @ true }T
T{ lf-ssession-begin -> true }T
T{ 1 lf-level-serial @ lf-hterm-sort -> 0 lf-term-serial @ true }T
lf-term-serial @ sort-id !
T{ 0 sort-id @ 0 sort-id @ 10000 lf-candidate-definition-probe -> lf-candidate-invalid }T
T{ lf-term-count @ -> 1 }T
T{ lf-level-count @ -> 2 }T
\ Changing the context invalidates the captured session and all its handles.
T{ 3 lf-lscope-context-add -> true }T
T{ 0 sort-id @ 0 sort-id @ 10000 lf-candidate-definition-probe -> lf-candidate-invalid }T
T{ lf-term-count @ -> 1 }T
T{ lf-level-count @ -> 2 }T
\ Helper statuses keep their meaning; other codes are invalid, never ok.
T{ lf-repr-ok lf-candidate-repr-status -> lf-candidate-ok }T
T{ lf-repr-invalid lf-candidate-repr-status -> lf-candidate-invalid }T
T{ lf-repr-exhausted lf-candidate-repr-status -> lf-candidate-exhausted }T
T{ 3 lf-candidate-repr-status -> lf-candidate-invalid }T
T{ 99 lf-candidate-repr-status -> lf-candidate-invalid }T
T{ lf-tinfer-ok lf-candidate-infer-status -> lf-candidate-ok }T
T{ lf-tinfer-invalid lf-candidate-infer-status -> lf-candidate-invalid }T
T{ lf-tinfer-exhausted lf-candidate-infer-status -> lf-candidate-exhausted }T
T{ lf-tinfer-unknown lf-candidate-infer-status -> lf-candidate-unknown }T
T{ 99 lf-candidate-infer-status -> lf-candidate-invalid }T
T{ lf-tconvert-equal lf-candidate-convert-status -> lf-candidate-ok }T
T{ lf-tconvert-invalid lf-candidate-convert-status -> lf-candidate-invalid }T
T{ lf-tconvert-exhausted lf-candidate-convert-status -> lf-candidate-exhausted }T
T{ lf-tconvert-unknown lf-candidate-convert-status -> lf-candidate-unknown }T
T{ 99 lf-candidate-convert-status -> lf-candidate-invalid }T
bye

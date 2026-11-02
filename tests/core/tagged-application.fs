\ Application inference regressions; none of these results is a theorem.
include ../support/tester.fs
include ../../src/core/terms.fs
include ../../src/core/levels.fs
include ../../src/core/level-scope.fs
include ../../src/core/tagged-sort-boundary.fs
include ../../src/core/symbolic-session.fs
include ../../src/core/generation-handles.fs
include ../../src/legacy/tagged-shift.fs
include ../../src/legacy/tagged-instantiate.fs
include ../../src/legacy/tagged-compare.fs
include ../../src/legacy/tagged-beta.fs
include ../../src/kernel/level-value.fs
include ../../src/kernel/level-compare.fs
include ../../src/legacy/tagged-convert.fs
include ../../src/legacy/tagged-infer.fs

\ Build fun (A : Sort u) => (fun (B : Sort u) => B) A. Both the
\ argument type and Pi domain refer to the same validated symbolic level.
variable application-root-id
: application-fixture ( -- )
  lf-term-reset lf-level-reset lf-lscope-context-reset
  42 lf-lscope-context-add 0= abort" context setup"
  42 lf-hlevel-param 0= abort" level setup" 2drop
  lf-ssession-begin 0= abort" session setup"
  1 lf-level-serial @ lf-hterm-sort 0= abort" sort setup" 2drop
  0 lf-term-bvar 0= abort" variable setup" drop
  0 1 lf-term-lam 0= abort" inner lambda setup" drop
  2 1 lf-term-app 0= abort" application setup" drop
  0 3 lf-term-lam 0= abort" outer lambda setup" drop
  lf-term-serial @ application-root-id ! ;

\ Sweep the entire small budget range. Each failure must roll back all
\ intermediate inference and substitution allocations and unwind binders.
\ Retry after each failure to catch poisoned scratch/context state.
variable application-saw-success
variable application-saw-exhaustion
: application-budget-sweep ( -- )
  0 application-saw-success ! 0 application-saw-exhaustion !
  300 0 do
    application-fixture
    4 application-root-id @ i lf-tinfer
    dup lf-tinfer-exhausted = if
      drop 0<> abort" failure identity" -1 <> abort" failure index"
      lf-term-count @ 5 <> abort" term rollback"
      lf-level-count @ 2 <> abort" level rollback"
      lf-tinfer-context-depth @ 0<> abort" context leak"
      4 application-root-id @ 10000 lf-tinfer
      lf-tinfer-ok <> abort" retry failed" lf-hterm-valid? 0= abort" retry handle"
      true application-saw-exhaustion !
    else
      lf-tinfer-ok <> abort" unexpected inference status"
      lf-hterm-valid? 0= abort" invalid successful handle"
      true application-saw-success !
    then
    lf-tinfer-context-depth @ 0<> abort" context leak"
  loop
  application-saw-success @ 0= abort" no successful budget"
  application-saw-exhaustion @ 0= abort" no exhausted budget" ;
\ T{ }T also checks that the whole sweep leaves the data stack unchanged.
T{ application-budget-sweep -> }T
bye

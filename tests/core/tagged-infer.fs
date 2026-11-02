\ Untrusted tagged symbolic inference tests. Results are mutable syntax, not
\ theorem handles; this deliberately limited fragment rejects unsupported work.
include ../support/tester.fs
include ../support/checks.fs
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

variable test-u-id
variable test-root-id
variable test-level-serial
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ 42 lf-lscope-context-add -> true }T
T{ 42 lf-hlevel-param -> 1 lf-level-serial @ true }T
lf-level-serial @ test-u-id !
T{ lf-ssession-begin -> true }T
T{ 1 test-u-id @ lf-hterm-sort -> 0 lf-term-serial @ true }T
lf-term-serial @ test-root-id !
T{ 0 test-root-id @ 1000 lf-tinfer -> 1 lf-term-serial @ lf-tinfer-ok }T
T{ 1 lf-term-read -> lf-tag-symbolic-sort 2 0 true }T
T{ 2 lf-level-read -> lf-level-tag-succ 1 0 true }T

\ The binder's domain and body are Sort u. Lean may simplify imax, so inspect
\ the unnormalized graph rather than requiring identical surface syntax.
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ 42 lf-lscope-context-add -> true }T
T{ 42 lf-hlevel-param -> 1 lf-level-serial @ true }T
lf-level-serial @ test-u-id !
T{ lf-ssession-begin -> true }T
T{ 1 test-u-id @ lf-hterm-sort -> 0 lf-term-serial @ true }T
lf-term-serial @ test-root-id !
T{ 0 test-root-id @ 0 test-root-id @ lf-hterm-pi -> 1 lf-term-serial @ true }T
lf-term-serial @ test-root-id !
T{ 1 test-root-id @ 1000 lf-tinfer -> 4 lf-term-serial @ lf-tinfer-ok }T
T{ 4 lf-term-read -> lf-tag-symbolic-sort 4 0 true }T
T{ 4 lf-level-read -> lf-level-tag-imax 2 3 true }T
T{ 2 lf-level-read -> lf-level-tag-succ 1 0 true }T
T{ 3 lf-level-read -> lf-level-tag-succ 1 0 true }T

\ Polymorphic identity: fun (A : Sort u) (x : A) => x. The inner
\ bound variable's type must be shifted under the x binder, yielding bvar 1.
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ 42 lf-lscope-context-add -> true }T
T{ 42 lf-hlevel-param -> 1 lf-level-serial @ true }T
lf-level-serial @ test-u-id !
T{ lf-ssession-begin -> true }T
T{ 1 test-u-id @ lf-hterm-sort -> 0 lf-term-serial @ true }T
T{ 0 lf-hterm-bvar -> 1 lf-term-serial @ true }T
T{ 1 1 lf-term-lam -> 2 true }T
T{ 0 2 lf-term-lam -> 3 true }T
lf-term-serial @ test-root-id !
T{ 3 test-root-id @ 10000 lf-tinfer -> 7 lf-term-serial @ lf-tinfer-ok }T
T{ 5 lf-term-read -> lf-tag-bvar 1 0 true }T
T{ 6 lf-term-read -> lf-tag-pi 1 5 true }T
T{ 7 lf-term-read -> lf-tag-pi 0 6 true }T
T{ 7 lf-term-serial @ 1000 lf-hterm-check -> lf-repr-ok }T

\ Dependent Pi: (A : Sort u) -> A. Its universe is imax(succ u, u),
\ including Lean's impredicative zero case when u is instantiated to zero.
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ 42 lf-lscope-context-add -> true }T
T{ 42 lf-hlevel-param -> 1 lf-level-serial @ true }T
T{ lf-ssession-begin -> true }T
T{ 1 lf-level-serial @ lf-hterm-sort -> 0 lf-term-serial @ true }T
T{ 0 lf-hterm-bvar -> 1 lf-term-serial @ true }T
T{ 0 1 lf-term-pi -> 2 true }T
lf-term-serial @ test-root-id !
T{ 2 test-root-id @ 10000 lf-tinfer -> 4 lf-term-serial @ lf-tinfer-ok }T
T{ 4 lf-term-read -> lf-tag-symbolic-sort 3 0 true }T
T{ 3 lf-level-read -> lf-level-tag-imax 2 1 true }T
T{ 2 lf-level-read -> lf-level-tag-succ 1 0 true }T

\ A variable in a binder annotation is outside that binder's scope. Reject
\ it and restore both arenas, then verify that the context is empty.
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ lf-ssession-begin -> true }T
T{ 0 lf-hterm-bvar -> 0 lf-term-serial @ true }T
T{ 0 0 lf-term-lam -> 1 true }T
lf-term-serial @ test-root-id !
T{ 1 test-root-id @ 10000 lf-tinfer -> -1 0 lf-tinfer-invalid }T
T{ lf-term-count @ -> 2 }T
T{ lf-level-count @ -> 1 }T
T{ lf-tinfer-context-depth @ -> 0 }T

\ Sweep budgets through nested binder inference and shifting. A failed
\ operation restores counts and always unwinds the logical binder context.
variable binder-saw-success
variable binder-saw-exhaustion
: tagged-binder-fuel-sweep ( -- )
  0 binder-saw-success ! 0 binder-saw-exhaustion !
  160 0 do
    lf-term-reset lf-level-reset lf-lscope-context-reset
    42 lf-lscope-context-add 0= abort" context setup"
    42 lf-hlevel-param 0= abort" level setup" drop drop
    lf-ssession-begin 0= abort" session setup"
    1 lf-level-serial @ lf-hterm-sort 0= abort" sort setup" 2drop
    0 lf-term-bvar 0= abort" variable setup" drop
    1 1 lf-term-lam 0= abort" lambda setup" drop
    0 2 lf-term-lam 0= abort" lambda setup" drop
    3 lf-term-serial @ i lf-tinfer
    dup lf-tinfer-exhausted = if
      drop 0<> abort" failure identity" -1 <> abort" failure index"
      lf-term-count @ 4 <> abort" term rollback"
      lf-level-count @ 2 <> abort" level rollback"
      true binder-saw-exhaustion !
    else
      lf-tinfer-ok <> abort" unexpected status"
      lf-hterm-valid? 0= abort" invalid result"
      true binder-saw-success !
    then
    lf-tinfer-context-depth @ 0<> abort" context leak"
  loop
  binder-saw-success @ 0= abort" no successful binder budget"
  binder-saw-exhaustion @ 0= abort" no exhausted binder budget" ;
tagged-binder-fuel-sweep

\ Each budget begins from the same Pi input. Failed traversals, including
\ failures after intermediate allocations, restore both arena counts.
variable sweep-succeeded
variable sweep-exhausted
: tagged-inference-fuel-sweep ( -- )
  0 sweep-succeeded ! 0 sweep-exhausted !
  100 0 do
    lf-term-reset lf-level-reset lf-lscope-context-reset
    42 lf-lscope-context-add 0= abort" context setup"
    42 lf-hlevel-param 0= abort" level setup" test-u-id ! drop
    lf-ssession-begin 0= abort" session setup"
    1 test-u-id @ lf-hterm-sort 0= abort" sort setup" test-root-id ! drop
    0 test-root-id @ 0 test-root-id @ lf-hterm-pi 0= abort" Pi setup"
    test-root-id ! drop
    1 test-root-id @ i lf-tinfer
    dup lf-tinfer-exhausted = if
      drop 0<> abort" failure identity" -1 <> abort" failure index"
      lf-term-count @ 2 <> abort" term leak"
      lf-level-count @ 2 <> abort" level leak"
      true sweep-exhausted !
    else
      lf-tinfer-ok <> abort" unexpected status"
      lf-hterm-valid? 0= abort" bad output handle"
      true sweep-succeeded !
    then
  loop
  sweep-succeeded @ 0= abort" no successful budget"
  sweep-exhausted @ 0= abort" no exhausted budget" ;
tagged-inference-fuel-sweep

\ A previously valid Sort whose level allocation was replaced cannot be
\ inferred, even when the replacement is valid in the same context.
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ 42 lf-lscope-context-add -> true }T
T{ 42 lf-hlevel-param -> 1 lf-level-serial @ true }T
lf-level-serial @ test-u-id !
T{ lf-ssession-begin -> true }T
T{ 1 test-u-id @ lf-hterm-sort -> 0 lf-term-serial @ true }T
lf-term-serial @ test-root-id !
1 lf-level-count !
T{ 42 lf-hlevel-param -> 1 lf-level-serial @ true }T
T{ 0 test-root-id @ 1000 lf-tinfer -> -1 0 lf-tinfer-invalid }T
T{ lf-term-count @ -> 1 }T
T{ lf-level-count @ -> 2 }T

\ An unsupported Pi body is reached after its domain has allocated a type;
\ unknown must roll back that partial work in both arenas.
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ lf-ssession-begin -> true }T
T{ lf-hlevel-zero -> 0 lf-level-identities @ true }T
T{ 0 lf-level-identities @ lf-hterm-sort -> 0 lf-term-serial @ true }T
lf-term-serial @ test-root-id !
T{ 0 test-root-id @ 0 test-root-id @ lf-hterm-app -> 1 lf-term-serial @ true }T
T{ 0 test-root-id @ 1 lf-term-serial @ lf-hterm-pi -> 2 lf-term-serial @ true }T
lf-term-serial @ test-root-id !
T{ 2 test-root-id @ 1000 lf-tinfer -> -1 0 lf-tinfer-unknown }T
T{ lf-term-count @ -> 3 }T
T{ lf-level-count @ -> 1 }T
T{ 2 test-root-id @ 1+ 1000 lf-tinfer -> -1 0 lf-tinfer-invalid }T
T{ lf-term-count @ -> 3 }T
T{ lf-level-count @ -> 1 }T

\ Filling the term arena makes Sort inference fail after allocating a level;
\ that temporary level must be discarded without changing the full arena.
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ lf-ssession-begin -> true }T
T{ lf-hlevel-zero -> 0 lf-level-identities @ true }T
T{ 0 lf-level-identities @ lf-hterm-sort -> 0 lf-term-serial @ true }T
lf-term-serial @ test-root-id !
: fill-tagged-term-arena ( -- )
  begin lf-term-count @ lf-term-capacity < while
    0 lf-term-bvar 0= abort" arena setup" drop
  repeat ;
fill-tagged-term-arena
T{ 0 test-root-id @ 1000 lf-tinfer -> -1 0 lf-tinfer-exhausted }T
T{ lf-term-count @ -> lf-term-capacity }T
T{ lf-level-count @ -> 1 }T

\ Level allocation identity exhaustion must also fail without changing either
\ arena count. The input handle remains the same valid allocation.
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ lf-ssession-begin -> true }T
T{ 0 lf-level-identities @ lf-hterm-sort -> 0 lf-term-serial @ true }T
lf-term-serial @ test-root-id !
lf-level-serial @ test-level-serial !
-1 1 rshift lf-level-serial !
T{ 0 test-root-id @ 1000 lf-tinfer -> -1 0 lf-tinfer-exhausted }T
T{ lf-term-count @ -> 1 }T
T{ lf-level-count @ -> 1 }T
T{ 0 test-root-id @ lf-hterm-valid? -> true }T
\ Restore test-only scratch state before resetting the level arena below.
test-level-serial @ lf-level-serial !

\ Unknown syntax and exhausted fuel do not leave allocated results behind.
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ lf-ssession-begin -> true }T
T{ 0 lf-hterm-bvar -> 0 lf-term-serial @ true }T
lf-term-serial @ test-root-id !
T{ 0 test-root-id @ 100 lf-tinfer -> -1 0 lf-tinfer-invalid }T
T{ 0 test-root-id @ 0 lf-tinfer -> -1 0 lf-tinfer-exhausted }T
T{ lf-term-count @ -> 1 }T
T{ lf-level-count @ -> 1 }T

\ A binder domain or Pi body that infers but whose type is not a Sort is
\ unknown, never a type, and rolls back the work done to infer it.
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ 42 lf-lscope-context-add -> true }T
T{ 42 lf-hlevel-param -> 1 lf-level-serial @ true }T
T{ lf-ssession-begin -> true }T
T{ 1 lf-level-serial @ lf-hterm-sort -> 0 lf-term-serial @ true }T
T{ 0 lf-hterm-bvar -> 1 lf-term-serial @ true }T
T{ 0 1 lf-term-lam -> 2 true }T \ fun (A : Sort u) => A
T{ 2 1 lf-term-lam -> 3 true }T \ fun (x : fun A => A) => x
T{ 1 1 lf-term-lam -> 4 true }T \ fun (x : A) => x, open
T{ 0 4 lf-term-pi -> 5 true }T  \ (A : Sort u) -> fun (x : A) => x
: infer-live ( index -- type identity status )
  dup lf-term-identity drop 10000 ['] lf-tinfer rs-checked ;
T{ 3 infer-live -> -1 0 lf-tinfer-unknown }T
T{ lf-term-count @ lf-level-count @ -> 6 2 }T
T{ 5 infer-live -> -1 0 lf-tinfer-unknown }T
T{ lf-term-count @ lf-level-count @ -> 6 2 }T
bye

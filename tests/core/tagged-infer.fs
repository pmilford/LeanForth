\ Untrusted tagged symbolic inference tests. Results are mutable syntax, not
\ theorem handles; this deliberately limited fragment rejects unsupported work.
include ../support/tester.fs
include ../../src/core/terms.fs
include ../../src/experimental/levels.fs
include ../../src/experimental/level-scope.fs
include ../../src/experimental/tagged-sort-boundary.fs
include ../../src/experimental/symbolic-session.fs
include ../../src/experimental/generation-handles.fs
include ../../src/experimental/tagged-infer.fs

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
T{ 0 lf-hterm-bvar -> 1 lf-term-serial @ true }T
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
T{ 0 test-root-id @ 100 lf-tinfer -> -1 0 lf-tinfer-unknown }T
T{ 0 test-root-id @ 0 lf-tinfer -> -1 0 lf-tinfer-exhausted }T
T{ lf-term-count @ -> 1 }T
T{ lf-level-count @ -> 1 }T
bye

\ Tests for untrusted concrete level evaluation. Success is not a proof.
include ../support/tester.fs
include ../../src/experimental/levels.fs
include ../../src/experimental/level-scope.fs
include ../../src/experimental/level-value.fs

lf-level-reset lf-lscope-context-reset
T{ 0 lf-level-succ -> 1 true }T
T{ 1 lf-level-succ -> 2 true }T
T{ 2 0 lf-level-imax -> 3 true }T
T{ 1 3 lf-level-max -> 4 true }T
T{ 2 1 lf-level-imax -> 5 true }T
T{ 0 100 lf-level-value -> 0 lf-lvalue-ok }T
T{ 0 1 lf-level-value -> -1 lf-lvalue-exhausted }T
T{ 0 2 lf-level-value -> 0 lf-lvalue-ok }T
T{ 2 100 lf-level-value -> 2 lf-lvalue-ok }T
T{ 3 100 lf-level-value -> 0 lf-lvalue-ok }T
T{ 4 100 lf-level-value -> 1 lf-lvalue-ok }T
T{ 5 100 lf-level-value -> 2 lf-lvalue-ok }T
T{ 5 0 lf-level-value -> -1 lf-lvalue-exhausted }T
T{ -1 100 lf-level-value -> -1 lf-lvalue-invalid }T
T{ 5 -1 lf-level-value -> -1 lf-lvalue-invalid }T
T{ lf-lscope-ok lf-lvalue-scope-status -> lf-lvalue-ok }T
T{ lf-lscope-invalid lf-lvalue-scope-status -> lf-lvalue-invalid }T
T{ lf-lscope-exhausted lf-lvalue-scope-status -> lf-lvalue-exhausted }T
T{ 99 lf-lvalue-scope-status -> lf-lvalue-invalid }T
\ Exhaustion during validation or evaluation leaves the original DAG intact.
: check-level-budgets ( -- )
  100 0 do
    5 i lf-level-value
    dup lf-lvalue-ok = if
      drop 2 <> if -1 throw then
    else
      lf-lvalue-exhausted <> if -1 throw then -1 <> if -1 throw then
    then
    lf-level-count @ 6 <> if -1 throw then
  loop ;
check-level-budgets

\ Parameters remain unknown, including expressions Lean could simplify.
T{ 42 lf-lscope-context-add -> true }T
T{ 42 lf-level-param -> 6 true }T
T{ 6 0 lf-level-imax -> 7 true }T
T{ 6 100 lf-level-value -> -1 lf-lvalue-unknown }T
T{ 7 100 lf-level-value -> -1 lf-lvalue-unknown }T
\ Scope checks both branches before a symbolic result can short-circuit.
T{ 0 lf-level-succ -> 8 true }T
T{ 6 8 lf-level-max -> 9 true }T
T{ 8 6 lf-level-imax -> 10 true }T
99 8 lf-level-slot !
T{ 9 100 lf-level-value -> -1 lf-lvalue-invalid }T
T{ 10 100 lf-level-value -> -1 lf-lvalue-invalid }T
lf-level-tag-succ 8 lf-level-slot !
T{ 9 100 lf-level-value -> -1 lf-lvalue-unknown }T
T{ 10 100 lf-level-value -> -1 lf-lvalue-unknown }T
lf-lscope-context-reset
T{ 6 100 lf-level-value -> -1 lf-lvalue-invalid }T

\ Corrupted reachable nodes fail before evaluation and a valid retry works.
99 2 lf-level-slot !
T{ 5 100 lf-level-value -> -1 lf-lvalue-invalid }T
lf-level-tag-succ 2 lf-level-slot !
T{ 5 100 lf-level-value -> 2 lf-lvalue-ok }T
T{ lf-level-count @ -> 11 }T
bye

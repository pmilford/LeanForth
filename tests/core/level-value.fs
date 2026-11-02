\ Tests for untrusted concrete level evaluation. Success is not a proof.
include ../support/tester.fs
include ../support/checks.fs
require ../../src/core/level-scope.fs
require ../../src/core/levels.fs
require ../../src/kernel/level-value.fs

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
\ lf-lvalue-fuel is set only once the scope check succeeds. Root 2 costs
\ three scope visits and three evaluation visits; root 5 six scope visits.
7 lf-lvalue-fuel !
T{ 5 -1 lf-level-value lf-lvalue-fuel @ -> -1 lf-lvalue-invalid 7 }T
T{ 5 3 lf-level-value lf-lvalue-fuel @ -> -1 lf-lvalue-exhausted 7 }T
T{ 2 6 lf-level-value lf-lvalue-fuel @ -> 2 lf-lvalue-ok 0 }T
T{ 2 5 lf-level-value lf-lvalue-fuel @ -> -1 lf-lvalue-exhausted 0 }T
T{ 2 100 ' lf-level-value rs-checked -> 2 lf-lvalue-ok }T
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
\ Explicit assignments evaluate only that instance, never a theorem.
lf-lassign-reset
T{ 42 0 lf-lassign-add -> true }T
T{ 42 1 lf-lassign-add -> false }T
T{ 43 1 lf-lassign-add -> false }T
T{ 42 -1 lf-lassign-add -> false }T
T{ 6 100 lf-level-value-assigned -> 0 lf-lvalue-ok }T
T{ 42 lf-lscope-context-add -> false }T
T{ 6 100 lf-level-value-assigned -> 0 lf-lvalue-ok }T
T{ 7 100 lf-level-value-assigned -> 0 lf-lvalue-ok }T
T{ 6 100 lf-level-value -> -1 lf-lvalue-unknown }T
lf-lassign-reset
T{ 6 100 lf-level-value-assigned -> -1 lf-lvalue-unknown }T
T{ 42 3 lf-lassign-add -> true }T
T{ 6 100 lf-level-value-assigned -> 3 lf-lvalue-ok }T
T{ 7 100 lf-level-value-assigned -> 0 lf-lvalue-ok }T
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
T{ 6 100 lf-level-value-assigned -> -1 lf-lvalue-invalid }T
lf-lassign-reset

\ Corrupted reachable nodes fail before evaluation and a valid retry works.
99 2 lf-level-slot !
T{ 5 100 lf-level-value -> -1 lf-lvalue-invalid }T
lf-level-tag-succ 2 lf-level-slot !
T{ 5 100 lf-level-value -> 2 lf-lvalue-ok }T
T{ lf-level-count @ -> 11 }T

\ A maximal assigned value cannot overflow when used as a successor.
lf-level-reset lf-lscope-context-reset lf-lassign-reset
T{ 42 lf-lscope-context-add -> true }T
T{ 42 lf-level-param -> 1 true }T
T{ 1 lf-level-succ -> 2 true }T
lf-lassign-reset
T{ 42 lf-lvalue-cell-max lf-lassign-add -> true }T
T{ 1 100 lf-level-value-assigned -> lf-lvalue-cell-max lf-lvalue-ok }T
T{ 2 100 lf-level-value-assigned -> -1 lf-lvalue-exhausted }T
\ Corruption and stale assignments after context changes are rejected.
-1 lf-lassign-count !
T{ 1 100 lf-level-value-assigned -> -1 lf-lvalue-invalid }T
lf-lassign-reset
T{ 42 0 lf-lassign-add -> true }T
lf-lscope-context-reset
T{ 1 100 lf-level-value-assigned -> -1 lf-lvalue-invalid }T

\ Missing assignments stay unknown; corrupt tables cannot authorize a value.
lf-level-reset lf-lscope-context-reset lf-lassign-reset
T{ 42 lf-lscope-context-add -> true }T
T{ 43 lf-lscope-context-add -> true }T
T{ 42 lf-level-param -> 1 true }T
T{ 43 lf-level-param -> 2 true }T
T{ 1 2 lf-level-max -> 3 true }T
lf-lassign-reset
T{ 42 3 lf-lassign-add -> true }T
T{ 3 100 lf-level-value-assigned -> -1 lf-lvalue-unknown }T
T{ 43 5 lf-lassign-add -> true }T
T{ 3 100 lf-level-value-assigned -> 5 lf-lvalue-ok }T
T{ 3 100 lf-level-value -> -1 lf-lvalue-unknown }T
-1 lf-lassign-values cell+ !
T{ 3 100 lf-level-value-assigned -> -1 lf-lvalue-invalid }T
T{ 42 1 lf-lassign-add -> false }T
T{ lf-lassign-count @ -> 2 }T
5 lf-lassign-values cell+ !
42 lf-lassign-ids cell+ !
T{ 3 100 lf-level-value-assigned -> -1 lf-lvalue-invalid }T
43 lf-lassign-ids cell+ !
T{ 3 100 lf-level-value-assigned -> 5 lf-lvalue-ok }T
lf-level-capacity 1+ lf-lassign-count !
T{ 3 100 lf-level-value-assigned -> -1 lf-lvalue-invalid }T
lf-lassign-reset

\ Reusing a numeric ID after context or arena reset must not reuse its value.
T{ 42 7 lf-lassign-add -> true }T
lf-lscope-context-reset
T{ 42 lf-lscope-context-add -> true }T
T{ 1 100 lf-level-value-assigned -> -1 lf-lvalue-invalid }T
T{ 42 7 lf-lassign-add -> false }T
lf-lassign-reset
T{ 42 7 lf-lassign-add -> true }T
lf-level-reset
T{ 42 lf-level-param -> 1 true }T
T{ 1 100 lf-level-value-assigned -> -1 lf-lvalue-invalid }T
lf-lassign-reset
T{ 1 100 lf-level-value-assigned -> -1 lf-lvalue-unknown }T
T{ 42 7 lf-lassign-add -> true }T
T{ 1 100 lf-level-value-assigned -> 7 lf-lvalue-ok }T
T{ 1 100 lf-level-value -> -1 lf-lvalue-unknown }T
T{ 43 lf-lscope-context-add -> true }T
T{ 1 100 lf-level-value-assigned -> -1 lf-lvalue-invalid }T
\ Generation saturation fails closed instead of wrapping into stale snapshots.
lf-lvalue-cell-max 1- lf-lscope-generation !
T{ 44 lf-lscope-context-add -> true }T
T{ lf-lscope-generation @ -> lf-lvalue-cell-max }T
T{ 45 lf-lscope-context-add -> false }T
T{ lf-lscope-context-count @ -> 3 }T
lf-lscope-context-reset
T{ lf-lscope-generation @ -> -1 }T
lf-lscope-context-reset
T{ lf-lscope-generation @ -> -1 }T
lf-lassign-reset
T{ 1 100 lf-level-value-assigned -> -1 lf-lvalue-invalid }T
lf-lvalue-cell-max 1- lf-level-generation !
lf-level-reset
T{ lf-level-generation @ -> lf-lvalue-cell-max }T
lf-level-reset
T{ lf-level-generation @ -> -1 }T
lf-level-reset
T{ lf-level-generation @ -> -1 }T
T{ 0 lf-level-read -> false }T
bye

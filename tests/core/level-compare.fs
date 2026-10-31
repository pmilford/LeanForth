\ Conservative experimental level comparison tests; no theorem is checked.
include ../support/tester.fs
include ../../src/experimental/levels.fs
include ../../src/experimental/level-scope.fs
include ../../src/experimental/level-value.fs
include ../../src/experimental/level-compare.fs

lf-level-reset lf-lscope-context-reset
T{ 10 lf-lscope-context-add -> true }T
T{ 11 lf-lscope-context-add -> true }T
T{ 10 lf-level-param -> 1 true }T
T{ 11 lf-level-param -> 2 true }T
T{ 1 lf-level-succ -> 3 true }T
T{ 1 lf-level-succ -> 4 true }T
T{ 1 0 lf-level-max -> 5 true }T
T{ 0 lf-level-succ -> 6 true }T
T{ 6 0 lf-level-max -> 7 true }T
T{ 3 4 100 lf-level-compare -> lf-lcmp-equal }T
T{ 1 2 100 lf-level-compare -> lf-lcmp-unknown }T
T{ 1 5 100 lf-level-compare -> lf-lcmp-unknown }T
T{ 6 7 100 lf-level-compare -> lf-lcmp-equal }T
T{ lf-lcmp-fuel @ lf-lvalue-fuel @ = -> true }T
T{ 0 6 100 lf-level-compare -> lf-lcmp-unknown }T
T{ 3 4 0 lf-level-compare -> lf-lcmp-exhausted }T
T{ 3 4 -1 lf-level-compare -> lf-lcmp-invalid }T
T{ -1 4 100 lf-level-compare -> lf-lcmp-invalid }T
\ Explicit assignments must never be used to claim symbolic equality.
lf-lassign-reset
T{ 10 0 lf-lassign-add -> true }T
T{ 11 0 lf-lassign-add -> true }T
T{ 1 0 100 lf-level-compare -> lf-lcmp-unknown }T
T{ 0 1 100 lf-level-compare -> lf-lcmp-unknown }T
T{ 1 2 100 lf-level-compare -> lf-lcmp-unknown }T
-1 lf-lassign-count !
T{ 1 2 100 lf-level-compare -> lf-lcmp-unknown }T
lf-lassign-reset

\ Sweep budgets through the concrete fallback, retaining stack sentinel and
\ original arena count even when either value evaluation exhausts fuel.
: check-fallback-budgets ( -- )
  100 0 do
    987 6 7 i lf-level-compare
    dup lf-lcmp-equal <> swap lf-lcmp-exhausted <> and if -1 throw then
    987 <> if -1 throw then
    lf-level-count @ 8 <> if -1 throw then
  loop ;
check-fallback-budgets

\ Even when root constructors differ, a corrupted other root is invalid.
99 4 lf-level-slot !
T{ 0 4 100 lf-level-compare -> lf-lcmp-invalid }T
T{ 4 4 100 lf-level-compare -> lf-lcmp-invalid }T
lf-level-tag-succ 4 lf-level-slot !
T{ 3 4 100 lf-level-compare -> lf-lcmp-equal }T
lf-lscope-context-reset
T{ 1 1 100 lf-level-compare -> lf-lcmp-invalid }T

\ Every bounded attempt either finds equality or reports exhaustion; no
\ partial traversal can be upgraded to equality for insufficient fuel.
lf-level-reset lf-lscope-context-reset
T{ 0 lf-level-succ -> 1 true }T
: check-comparison-budgets ( -- )
  40 0 do
    1 1 i lf-level-compare
    dup lf-lcmp-equal <> swap lf-lcmp-exhausted <> and if -1 throw then
    0 1 i lf-level-compare
    dup lf-lcmp-unknown <> swap lf-lcmp-exhausted <> and if -1 throw then
    lf-level-count @ 2 <> if -1 throw then
  loop ;
check-comparison-budgets
bye

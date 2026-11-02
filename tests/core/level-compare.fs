\ Conservative experimental level comparison tests; no theorem is checked.
include ../support/tester.fs
include ../support/checks.fs
require ../../src/core/level-scope.fs
require ../../src/core/levels.fs
require ../../src/kernel/level-compare.fs
require ../../src/kernel/level-value.fs

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
T{ 6 6 lf-level-max -> 8 true }T
T{ 0 1 lf-level-max -> 9 true }T
T{ 1 0 lf-level-imax -> 10 true }T
T{ 5 lf-level-succ -> 11 true }T
T{ 0 1 lf-level-imax -> 12 true }T
T{ 0 5 lf-level-max -> 13 true }T
T{ 11 2 lf-level-max -> 14 true }T
T{ 3 2 lf-level-max -> 15 true }T
T{ 11 2 lf-level-imax -> 16 true }T
T{ 3 2 lf-level-imax -> 17 true }T
T{ 3 4 100 lf-level-compare -> lf-lcmp-equal }T
T{ 1 2 100 lf-level-compare -> lf-lcmp-unknown }T
T{ 1 5 100 lf-level-compare -> lf-lcmp-equal }T
T{ 9 1 100 lf-level-compare -> lf-lcmp-equal }T
T{ 10 0 100 lf-level-compare -> lf-lcmp-equal }T
T{ 11 3 100 lf-level-compare -> lf-lcmp-equal }T
T{ 12 0 100 lf-level-compare -> lf-lcmp-unknown }T
T{ 13 1 100 lf-level-compare -> lf-lcmp-equal }T
T{ 14 15 100 lf-level-compare -> lf-lcmp-equal }T
T{ 16 17 100 lf-level-compare -> lf-lcmp-equal }T
T{ 6 7 100 lf-level-compare -> lf-lcmp-equal }T
T{ 6 8 100 lf-level-compare -> lf-lcmp-equal }T
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
    987 6 8 i lf-level-compare
    dup lf-lcmp-equal <> swap lf-lcmp-exhausted <> and if -1 throw then
    987 <> if -1 throw then
    lf-level-count @ 18 <> if -1 throw then
  loop ;
check-fallback-budgets

\ Verify exact fuel boundary for rewriting imax(u,0), in both orders.
: check-zero-rewrite-budgets ( -- )
  9 0 do
    987 10 0 i lf-level-compare
    i 8 < if lf-lcmp-exhausted else lf-lcmp-equal then <> if -1 throw then
    987 <> if -1 throw then
    987 0 10 i lf-level-compare
    i 8 < if lf-lcmp-exhausted else lf-lcmp-equal then <> if -1 throw then
    987 <> if -1 throw then
  loop ;
check-zero-rewrite-budgets

\ Even when root constructors differ, a corrupted other root is invalid.
99 1 lf-level-slot !
T{ 10 0 100 lf-level-compare -> lf-lcmp-invalid }T
T{ 0 10 100 lf-level-compare -> lf-lcmp-invalid }T
lf-level-tag-param 1 lf-level-slot !
1 1 lf-level-slot 2 cells + !
T{ 10 0 100 lf-level-compare -> lf-lcmp-invalid }T
0 1 lf-level-slot 2 cells + !
1 0 lf-level-slot cell+ !
T{ 10 0 100 lf-level-compare -> lf-lcmp-invalid }T
0 0 lf-level-slot cell+ !
99 4 lf-level-slot !
T{ 0 4 100 lf-level-compare -> lf-lcmp-invalid }T
T{ 4 4 100 lf-level-compare -> lf-lcmp-invalid }T
lf-level-tag-succ 4 lf-level-slot !
T{ 3 4 100 lf-level-compare -> lf-lcmp-equal }T
lf-lscope-context-reset
T{ 1 1 100 lf-level-compare -> lf-lcmp-invalid }T
T{ 10 0 100 lf-level-compare -> lf-lcmp-invalid }T

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
\ Fuel left, which mixed-convert reads. 1 1: two scope checks of two
\ visits, then the walk visits the pair, shrinks both, and does the same
\ for the children: ten units. 0 1: three scope visits, three walk visits,
\ then the fallback evaluates both roots (two and four units). Any failure
\ leaves no fuel.
T{ 1 1 20 lf-level-compare lf-lcmp-fuel @ -> lf-lcmp-equal 10 }T
T{ 1 1 10 lf-level-compare lf-lcmp-fuel @ -> lf-lcmp-equal 0 }T
T{ 1 1 9 lf-level-compare lf-lcmp-fuel @ -> lf-lcmp-exhausted 0 }T
T{ 0 1 20 lf-level-compare lf-lcmp-fuel @ -> lf-lcmp-unknown 8 }T
5 lf-lcmp-fuel !
T{ 1 1 -1 lf-level-compare lf-lcmp-fuel @ -> lf-lcmp-invalid 0 }T
5 lf-lcmp-fuel !
T{ -1 1 20 lf-level-compare lf-lcmp-fuel @ -> lf-lcmp-invalid 0 }T
T{ 1 1 20 ' lf-level-compare rs-checked -> lf-lcmp-equal }T
bye

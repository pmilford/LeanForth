\ Untrusted conversion tests: no status creates an accepted theorem.
include ../support/tester.fs
include ../../src/core/terms.fs
include ../../src/core/levels.fs
include ../../src/core/level-scope.fs
include ../../src/core/tagged-sort-boundary.fs
include ../../src/core/symbolic-session.fs
include ../../src/core/generation-handles.fs
include ../../src/legacy/tagged-shift.fs
include ../../src/legacy/tagged-instantiate.fs
include ../../src/legacy/tagged-beta.fs
include ../../src/core/level-value.fs
include ../../src/core/level-compare.fs
include ../../src/legacy/tagged-convert.fs

: handle ( node -- node identity ) dup lf-term-identity 0= abort" identity" ;
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ lf-ssession-begin -> true }T
T{ lf-hlevel-zero -> 0 lf-level-identities @ true }T
T{ 0 lf-level-identities @ lf-hterm-sort -> 0 lf-term-serial @ true }T
T{ 0 lf-level-identities @ lf-hlevel-succ -> 1 lf-level-serial @ true }T
T{ 1 lf-level-serial @ lf-hterm-sort -> 1 lf-term-serial @ true }T
T{ 0 lf-term-bvar -> 2 true }T
T{ 1 2 lf-term-lam -> 3 true }T
T{ 3 0 lf-term-app -> 4 true }T
T{ 4 0 lf-term-pi -> 5 true }T
T{ 0 0 lf-term-pi -> 6 true }T
\ Beta at the root and inside a binder domain; temporary results roll back.
T{ 4 handle 0 handle 10000 lf-tagged-convert -> lf-tconvert-equal }T
T{ 5 handle 6 handle 10000 lf-tagged-convert -> lf-tconvert-equal }T
T{ lf-term-count @ -> 7 }T
\ Nonidentical Sort levels remain unknown; exhausted work is never equality.
T{ 0 handle 1 handle 10000 lf-tagged-convert -> lf-tconvert-unknown }T
T{ 4 handle 0 handle 0 lf-tagged-convert -> lf-tconvert-exhausted }T
T{ 4 handle 0 handle -1 lf-tagged-convert -> lf-tconvert-invalid }T
T{ lf-term-count @ -> 7 }T
\ Sweep budgets for beta conversion inside a binder. Temporary beta and
\ substitution allocations are discarded even when the comparison fails.
variable conversion-saw-success
variable conversion-saw-exhaustion
: conversion-fuel-sweep ( -- )
  0 conversion-saw-success ! 0 conversion-saw-exhaustion !
  300 0 do
    5 handle 6 handle i lf-tagged-convert
    dup lf-tconvert-exhausted = if
      drop true conversion-saw-exhaustion !
    else
      lf-tconvert-equal <> abort" conversion status"
      true conversion-saw-success !
    then
    lf-term-count @ 7 <> abort" conversion allocation leak"
  loop
  conversion-saw-success @ 0= abort" no successful conversion budget"
  conversion-saw-exhaustion @ 0= abort" no exhausted conversion budget" ;
conversion-fuel-sweep
\ Even an argument discarded by beta must be audited. A raw, unstamped Sort
\ is invalid as either input, including below a lambda body or application.
T{ 0 lf-term-symbolic-sort -> 7 true }T
T{ 0 0 lf-term-lam -> 8 true }T
T{ 8 7 lf-term-app -> 9 true }T
T{ 9 handle 0 handle 10000 lf-tagged-convert -> lf-tconvert-invalid }T
T{ 0 handle 9 handle 10000 lf-tagged-convert -> lf-tconvert-invalid }T
T{ lf-term-count @ -> 10 }T

\ Distinct universe DAGs may still represent Lean-equivalent levels. These
\ checks are conservative: unresolved symbolic equations remain unknown.
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ 42 lf-lscope-context-add -> true }T
T{ 43 lf-lscope-context-add -> true }T
T{ 42 lf-hlevel-param -> 1 lf-level-serial @ true }T
T{ 43 lf-hlevel-param -> 2 lf-level-serial @ true }T
T{ 1 0 lf-level-max -> 3 true }T
T{ 1 0 lf-level-imax -> 4 true }T
T{ lf-ssession-begin -> true }T
T{ 1 lf-level-identities cell+ @ lf-hterm-sort -> 0 lf-term-serial @ true }T
T{ 3 lf-level-identities 3 cells + @ lf-hterm-sort -> 1 lf-term-serial @ true }T
T{ 4 lf-level-identities 4 cells + @ lf-hterm-sort -> 2 lf-term-serial @ true }T
T{ 0 lf-level-identities @ lf-hterm-sort -> 3 lf-term-serial @ true }T
T{ 2 lf-level-identities 2 cells + @ lf-hterm-sort -> 4 lf-term-serial @ true }T
T{ 0 handle 1 handle 10000 lf-tagged-convert -> lf-tconvert-equal }T
T{ 2 handle 3 handle 10000 lf-tagged-convert -> lf-tconvert-equal }T
T{ 0 handle 4 handle 10000 lf-tagged-convert -> lf-tconvert-unknown }T
T{ lf-term-count @ -> 5 }T
T{ lf-level-count @ -> 5 }T
\ Level validation and normalization share the conversion visit budget.
: level-conversion-fuel-sweep ( -- )
  100 0 do
    0 handle 1 handle i lf-tagged-convert
    dup lf-tconvert-equal <> swap lf-tconvert-exhausted <> and
    if -1 throw then
    lf-term-count @ 5 <> if -1 throw then
    lf-level-count @ 5 <> if -1 throw then
  loop ;
level-conversion-fuel-sweep

\ Beta reduction under binders must avoid capture: fun z =>
\ (fun x => fun y => x) z equals fun z => fun y => z, but not
\ fun z => fun y => y. The latter remains unknown, not an inequality proof.
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ lf-ssession-begin -> true }T
T{ lf-hlevel-zero -> 0 lf-level-serial @ true }T
T{ 0 lf-level-serial @ lf-hterm-sort -> 0 lf-term-serial @ true }T
T{ 0 lf-term-bvar -> 1 true }T
T{ 1 lf-term-bvar -> 2 true }T
T{ 0 2 lf-term-lam -> 3 true }T
T{ 0 3 lf-term-lam -> 4 true }T
T{ 4 1 lf-term-app -> 5 true }T
T{ 0 5 lf-term-lam -> 6 true }T
T{ 0 3 lf-term-lam -> 7 true }T
T{ 0 1 lf-term-lam -> 8 true }T
T{ 0 8 lf-term-lam -> 9 true }T
T{ 6 handle 7 handle 10000 lf-tagged-convert -> lf-tconvert-equal }T
T{ 6 handle 9 handle 10000 lf-tagged-convert -> lf-tconvert-unknown }T
T{ lf-term-count @ -> 10 }T
bye

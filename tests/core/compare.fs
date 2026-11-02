\ Unit tests for untrusted conversion experiments. An equal result is not a
\ checked theorem and does not establish that either input is well typed.
include ../support/tester.fs
include ../../src/legacy/compare.fs

lf-term-reset
T{ 0 lf-term-sort -> 0 true }T
T{ 1 lf-term-sort -> 1 true }T
T{ 0 lf-term-bvar -> 2 true }T
T{ 1 2 lf-term-lam -> 3 true }T
T{ 3 0 lf-term-app -> 4 true }T
T{ 0 2 lf-term-lam -> 5 true }T
T{ 4 2 lf-term-lam -> 6 true }T
T{ 0 0 lf-term-app -> 7 true }T

\ Exact matches and a beta-reduced application compare equal in the model.
T{ 0 0 1000 lf-compare -> lf-compare-equal }T
T{ 2 2 1000 lf-compare -> lf-compare-equal }T
T{ 4 0 1000 lf-compare -> lf-compare-equal }T
T{ 5 5 1000 lf-compare -> lf-compare-equal }T
\ This closed application is ill typed: comparison is not type validation.
T{ 7 7 1000 lf-compare -> lf-compare-equal }T

\ Different sorts, constructors and beta-equivalent but non-identical binder
\ domains are inconclusive rather than claims of Lean inequality.
T{ 0 1 1000 lf-compare -> lf-compare-unknown }T
T{ 0 2 1000 lf-compare -> lf-compare-unknown }T
T{ 5 6 1000 lf-compare -> lf-compare-unknown }T
T{ lf-term-count @ -> 8 }T

\ Resource exhaustion, invalid roots and malformed nodes fail without retaining
\ any temporary reduction allocations or altering existing terms.
T{ 0 0 0 lf-compare -> lf-compare-exhausted }T
T{ 0 0 -1 lf-compare -> lf-compare-invalid }T
T{ -1 0 1000 lf-compare -> lf-compare-invalid }T
T{ 0 8 1000 lf-compare -> lf-compare-invalid }T
99 3 lf-term-slot !
T{ 4 0 1000 lf-compare -> lf-compare-invalid }T
lf-tag-lam 3 lf-term-slot !
T{ lf-term-count @ -> 8 }T
T{ 4 0 1000 lf-compare -> lf-compare-equal }T

\ Exercise many budget boundaries. The comparison is either established or
\ exhausted, and every run restores the original allocation count.
: check-compare-budgets ( -- )
  30 0 do
    4 0 i lf-compare
    dup lf-compare-equal = swap lf-compare-exhausted = or 0= if -1 throw then
    lf-term-count @ 8 <> if -1 throw then
  loop ;
check-compare-budgets

\ Equal syntax in separately allocated nodes must not require pointer identity.
T{ 0 lf-term-bvar -> 8 true }T
T{ 0 8 lf-term-lam -> 9 true }T
T{ 5 9 1000 lf-compare -> lf-compare-equal }T
T{ lf-term-count @ -> 10 }T
lf-term-reset
bye

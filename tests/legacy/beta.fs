\ Tests for the untrusted weak-head beta experiment. These are syntax checks,
\ not proofs or theorem acceptance tests.
include ../support/tester.fs
include ../../src/legacy/beta.fs

\ The identity application reduces to its argument.
lf-term-reset
T{ 0 lf-term-sort -> 0 true }T
T{ 0 lf-term-bvar -> 1 true }T
T{ 0 1 lf-term-lam -> 2 true }T
T{ 2 0 lf-term-app -> 3 true }T
T{ 3 100 lf-beta-whnf -> 0 lf-beta-ok }T

\ A stuck application remains an application; this is not a type judgment.
T{ 1 0 lf-term-app -> 4 true }T
T{ 4 100 lf-beta-whnf -> 4 lf-beta-ok }T

\ A lambda is already in weak-head form, even if its body contains a redex.
T{ 0 3 lf-term-lam -> 5 true }T
T{ 5 100 lf-beta-whnf -> 5 lf-beta-ok }T

\ Invalid roots, malformed nodes and insufficient fuel must not keep new nodes.
T{ -1 100 lf-beta-whnf -> -1 lf-beta-invalid }T
T{ 6 100 lf-beta-whnf -> -1 lf-beta-invalid }T
T{ 3 -1 lf-beta-whnf -> -1 lf-beta-invalid }T
T{ 3 0 lf-beta-whnf -> -1 lf-beta-exhausted }T
T{ 3 5 lf-beta-whnf -> -1 lf-beta-exhausted }T
T{ lf-term-count @ -> 6 }T
99 2 lf-term-slot !
T{ 3 100 lf-beta-whnf -> -1 lf-beta-invalid }T
lf-tag-lam 2 lf-term-slot !
T{ lf-term-count @ -> 6 }T
T{ 3 100 lf-beta-whnf -> 0 lf-beta-ok }T

\ The untyped self-application loop must exhaust resources rather than hang or
\ leave intermediate nodes reachable. It is not a valid theorem candidate.
lf-term-reset
T{ 0 lf-term-sort -> 0 true }T
T{ 0 lf-term-bvar -> 1 true }T
T{ 1 1 lf-term-app -> 2 true }T
T{ 0 2 lf-term-lam -> 3 true }T
T{ 3 3 lf-term-app -> 4 true }T
T{ 4 100 lf-beta-whnf -> -1 lf-beta-exhausted }T
T{ lf-term-count @ -> 5 }T
T{ 4 100 lf-beta-whnf -> -1 lf-beta-exhausted }T
T{ lf-term-count @ -> 5 }T
lf-term-reset
bye

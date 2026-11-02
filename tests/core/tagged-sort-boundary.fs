\ Tests for an untrusted syntax-only representation boundary. These cases
\ do not establish Lean typing, level validity, or theorem acceptance.
include ../support/tester.fs
require ../../src/core/tagged-sort-boundary.fs
require ../../src/core/terms.fs

lf-term-reset
T{ 1 lf-term-sort -> 0 true }T
T{ 1 lf-term-symbolic-sort -> 1 true }T
T{ 0 lf-term-read -> lf-tag-sort 1 0 true }T
T{ 1 lf-term-read -> lf-tag-symbolic-sort 1 0 true }T
T{ -1 lf-term-symbolic-sort -> false }T
T{ 0 lf-repr-concrete 10 lf-repr-check -> lf-repr-ok }T
T{ 0 lf-repr-symbolic 10 lf-repr-check -> lf-repr-invalid }T
T{ 1 lf-repr-symbolic 10 lf-repr-check -> lf-repr-ok }T
T{ 1 lf-repr-concrete 10 lf-repr-check -> lf-repr-invalid }T
\ The kernel passes reject a concrete Sort in tests/core/mixed-shift.fs.

\ The wrong kind must be rejected anywhere in a reachable binary tree, even
\ when the other root or another branch has no Sorts.
T{ 0 lf-term-bvar -> 2 true }T
T{ 2 1 lf-term-app -> 3 true }T
T{ 1 2 lf-term-lam -> 4 true }T
T{ 2 0 lf-term-pi -> 5 true }T
T{ 3 lf-repr-concrete 10 lf-repr-check -> lf-repr-invalid }T
T{ 4 lf-repr-concrete 10 lf-repr-check -> lf-repr-invalid }T
T{ 5 lf-repr-symbolic 10 lf-repr-check -> lf-repr-invalid }T
T{ 2 lf-repr-concrete 10 lf-repr-check -> lf-repr-ok }T
T{ 2 lf-repr-symbolic 10 lf-repr-check -> lf-repr-ok }T
T{ 2 1 lf-repr-concrete 10 lf-repr-check-pair -> lf-repr-invalid }T
T{ 1 2 lf-repr-concrete 10 lf-repr-check-pair -> lf-repr-invalid }T
T{ 0 2 lf-repr-concrete 2 lf-repr-check-pair -> lf-repr-ok }T
T{ 0 2 lf-repr-concrete 1 lf-repr-check-pair -> lf-repr-exhausted }T
T{ 0 lf-repr-concrete 0 lf-repr-check -> lf-repr-exhausted }T
T{ 0 -1 10 lf-repr-check -> lf-repr-invalid }T
T{ 0 lf-repr-concrete -1 lf-repr-check -> lf-repr-invalid }T
T{ -1 lf-repr-concrete 10 lf-repr-check -> lf-repr-invalid }T
T{ lf-term-count @ -> 6 }T

\ Both child positions of each binary constructor reject a wrong-mode Sort.
\ The roots contain an otherwise representation-neutral bound variable.
T{ 1 2 lf-term-app -> 6 true }T
T{ 2 1 lf-term-lam -> 7 true }T
T{ 1 2 lf-term-pi -> 8 true }T
T{ 0 2 lf-term-app -> 9 true }T
T{ 2 0 lf-term-lam -> 10 true }T
T{ 0 2 lf-term-pi -> 11 true }T
T{ 6 lf-repr-concrete 10 lf-repr-check -> lf-repr-invalid }T
T{ 7 lf-repr-concrete 10 lf-repr-check -> lf-repr-invalid }T
T{ 8 lf-repr-concrete 10 lf-repr-check -> lf-repr-invalid }T
T{ 9 lf-repr-symbolic 10 lf-repr-check -> lf-repr-invalid }T
T{ 10 lf-repr-symbolic 10 lf-repr-check -> lf-repr-invalid }T
T{ 11 lf-repr-symbolic 10 lf-repr-check -> lf-repr-invalid }T
T{ 0 0 lf-repr-concrete 2 lf-repr-check-pair -> lf-repr-ok }T
T{ 1 1 lf-repr-concrete 2 lf-repr-check-pair -> lf-repr-invalid }T
T{ 0 99 lf-repr-concrete 20 lf-repr-check-pair -> lf-repr-invalid }T
T{ 99 0 lf-repr-concrete 20 lf-repr-check-pair -> lf-repr-invalid }T
T{ lf-term-count @ -> 12 }T

\ Repeat the opposite child positions in each mode and check zero payloads;
\ equal payloads still do not identify the representation.
T{ 2 1 lf-term-pi -> 12 true }T
T{ 2 0 lf-term-app -> 13 true }T
T{ 0 2 lf-term-lam -> 14 true }T
T{ 2 0 lf-term-pi -> 15 true }T
T{ 12 lf-repr-concrete 10 lf-repr-check -> lf-repr-invalid }T
T{ 13 lf-repr-symbolic 10 lf-repr-check -> lf-repr-invalid }T
T{ 14 lf-repr-symbolic 10 lf-repr-check -> lf-repr-invalid }T
T{ 15 lf-repr-symbolic 10 lf-repr-check -> lf-repr-invalid }T
T{ 0 lf-term-sort -> 16 true }T
T{ 0 lf-term-symbolic-sort -> 17 true }T
T{ 16 lf-repr-symbolic 2 lf-repr-check -> lf-repr-invalid }T
T{ 17 lf-repr-concrete 2 lf-repr-check -> lf-repr-invalid }T
T{ 17 lf-repr-symbolic 2 lf-repr-check -> lf-repr-ok }T

\ Malformed leaf fields, cycles and forward references fail closed. Unrelated
\ corrupt nodes do not change the result for an otherwise valid root.
7 1 lf-term-slot 2 cells + !
T{ 1 lf-repr-symbolic 10 lf-repr-check -> lf-repr-invalid }T
T{ 0 lf-repr-concrete 10 lf-repr-check -> lf-repr-ok }T
0 1 lf-term-slot 2 cells + !
99 1 lf-term-slot !
T{ 777 1 lf-repr-symbolic 10 lf-repr-check -> 777 lf-repr-invalid }T
lf-tag-symbolic-sort 1 lf-term-slot !
-1 1 lf-term-slot cell+ !
T{ 1 lf-repr-symbolic 10 lf-repr-check -> lf-repr-invalid }T
1 1 lf-term-slot cell+ !
-1 2 lf-term-slot cell+ !
T{ 2 lf-repr-concrete 10 lf-repr-check -> lf-repr-invalid }T
0 2 lf-term-slot cell+ !
1 2 lf-term-slot 2 cells + !
T{ 2 lf-repr-concrete 10 lf-repr-check -> lf-repr-invalid }T
0 2 lf-term-slot 2 cells + !
3 3 lf-term-slot cell+ !
T{ 3 lf-repr-symbolic 10 lf-repr-check -> lf-repr-invalid }T
4 3 lf-term-slot cell+ !
T{ 3 lf-repr-symbolic 10 lf-repr-check -> lf-repr-invalid }T
T{ 777 0 1 -1 10 lf-repr-check-pair -> 777 lf-repr-invalid }T
T{ 777 0 1 lf-repr-symbolic -1 lf-repr-check-pair -> 777 lf-repr-invalid }T
T{ 0 lf-term-read -> lf-tag-sort 1 0 true }T
T{ 1 lf-term-read -> lf-tag-symbolic-sort 1 0 true }T
T{ lf-term-count @ -> 18 }T

\ Shared DAG children are charged per visit. Exhaustion need not discover a
\ bad node that the budget cannot reach. The validators never allocate.
lf-term-reset
T{ 0 lf-term-sort -> 0 true }T
T{ 0 0 lf-term-app -> 1 true }T
T{ 1 lf-repr-concrete 2 lf-repr-check -> lf-repr-exhausted }T
T{ 1 lf-repr-concrete 3 lf-repr-check -> lf-repr-ok }T
T{ 1 1 lf-repr-concrete 5 lf-repr-check-pair -> lf-repr-exhausted }T
T{ 1 1 lf-repr-concrete 6 lf-repr-check-pair -> lf-repr-ok }T
T{ lf-term-count @ -> 2 }T
-1 lf-term-count !
T{ 0 lf-repr-concrete 10 lf-repr-check -> lf-repr-invalid }T
T{ lf-term-count @ -> -1 }T
lf-term-capacity 1+ lf-term-count !
T{ 0 1 lf-repr-concrete 10 lf-repr-check-pair -> lf-repr-invalid }T
T{ lf-term-count @ -> lf-term-capacity 1+ }T
lf-term-reset
bye

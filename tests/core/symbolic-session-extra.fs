\ Regression tests for the untrusted symbolic session guard. A successful
\ check establishes representation and level structure, not typing or proof.
include ../support/tester.fs
include ../../src/core/terms.fs
include ../../src/core/levels.fs
include ../../src/core/level-scope.fs
include ../../src/core/tagged-sort-boundary.fs
include ../../src/core/symbolic-session.fs

\ A session can start only with an empty term arena. New terms and levels
\ may then be allocated without invalidating the snapshot.
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ 0 lf-term-bvar -> 0 true }T
T{ lf-ssession-begin -> false }T
lf-term-reset
T{ lf-ssession-begin -> true }T
T{ 0 lf-level-succ -> 1 true }T
T{ 1 lf-term-symbolic-sort -> 0 true }T
T{ 0 100 lf-ssession-check -> lf-repr-ok }T
T{ -1 100 lf-ssession-check -> lf-repr-invalid }T
T{ 1 100 lf-ssession-check -> lf-repr-invalid }T
T{ 0 -1 lf-ssession-check -> lf-repr-invalid }T
T{ 0 0 lf-ssession-check -> lf-repr-exhausted }T

\ Reusing identical indices after any reset must not revive a stale session.
lf-term-reset
T{ 1 lf-term-symbolic-sort -> 0 true }T
T{ 0 100 lf-ssession-check -> lf-repr-invalid }T
lf-term-reset
T{ lf-ssession-begin -> true }T
T{ 1 lf-term-symbolic-sort -> 0 true }T
lf-level-reset
T{ 0 lf-level-succ -> 1 true }T
T{ 0 100 lf-ssession-check -> lf-repr-invalid }T
lf-term-reset
T{ lf-ssession-begin -> true }T
T{ 1 lf-term-symbolic-sort -> 0 true }T
lf-lscope-context-reset
T{ 0 100 lf-ssession-check -> lf-repr-invalid }T

\ Context extension changes the snapshot, including for a root that does not
\ mention the new parameter. A failed duplicate addition does not change it.
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ 7 lf-lscope-context-add -> true }T
T{ 7 lf-level-param -> 1 true }T
T{ lf-ssession-begin -> true }T
T{ 1 lf-term-symbolic-sort -> 0 true }T
T{ 0 100 lf-ssession-check -> lf-repr-ok }T
T{ 7 lf-lscope-context-add -> false }T
T{ 0 100 lf-ssession-check -> lf-repr-ok }T
T{ 8 lf-lscope-context-add -> true }T
T{ 0 100 lf-ssession-check -> lf-repr-invalid }T
lf-term-reset
T{ lf-ssession-begin -> true }T
T{ 1 lf-term-symbolic-sort -> 0 true }T
T{ 0 100 lf-ssession-check -> lf-repr-ok }T

\ Concrete Sorts and invalid or unbound level references fail at either
\ child position; an unrelated malformed term is not reachable from root 0.
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ 9 lf-level-param -> 1 true }T
T{ lf-ssession-begin -> true }T
T{ 0 lf-term-symbolic-sort -> 0 true }T
T{ 0 lf-term-sort -> 1 true }T
T{ 63 lf-term-symbolic-sort -> 2 true }T
T{ 1 lf-term-symbolic-sort -> 3 true }T
T{ 0 1 lf-term-app -> 4 true }T
T{ 1 0 lf-term-lam -> 5 true }T
T{ 0 2 lf-term-pi -> 6 true }T
T{ 3 0 lf-term-app -> 7 true }T
T{ 0 100 lf-ssession-check -> lf-repr-ok }T
T{ 1 100 lf-ssession-check -> lf-repr-invalid }T
T{ 2 100 lf-ssession-check -> lf-repr-invalid }T
T{ 3 100 lf-ssession-check -> lf-repr-invalid }T
T{ 4 100 lf-ssession-check -> lf-repr-invalid }T
T{ 5 100 lf-ssession-check -> lf-repr-invalid }T
T{ 6 100 lf-ssession-check -> lf-repr-invalid }T
T{ 7 100 lf-ssession-check -> lf-repr-invalid }T

\ Corrupted tags, reserved fields, child links and level nodes fail closed.
99 0 lf-term-slot !
T{ 0 100 lf-ssession-check -> lf-repr-invalid }T
lf-tag-symbolic-sort 0 lf-term-slot !
1 0 lf-term-slot 2 cells + !
T{ 0 100 lf-ssession-check -> lf-repr-invalid }T
0 0 lf-term-slot 2 cells + !
4 4 lf-term-slot cell+ !
T{ 4 100 lf-ssession-check -> lf-repr-invalid }T
0 4 lf-term-slot cell+ !
1 0 lf-level-slot cell+ !
T{ 0 100 lf-ssession-check -> lf-repr-invalid }T
0 0 lf-level-slot cell+ !
T{ 0 100 lf-ssession-check -> lf-repr-ok }T

\ A valid shared DAG requires fuel across term and level traversals. Checks
\ must not silently reset fuel for each child or each symbolic Sort.
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ 0 0 lf-level-max -> 1 true }T
T{ lf-ssession-begin -> true }T
T{ 1 lf-term-symbolic-sort -> 0 true }T
T{ 0 0 lf-term-app -> 1 true }T
T{ 1 3 lf-ssession-check -> lf-repr-exhausted }T
T{ 1 11 lf-ssession-check -> lf-repr-exhausted }T
T{ 1 12 lf-ssession-check -> lf-repr-ok }T
T{ 1 100 lf-ssession-check -> lf-repr-ok }T
T{ lf-term-count @ -> 2 }T
T{ lf-level-count @ -> 2 }T
bye

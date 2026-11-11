\ Regression tests for the untrusted symbolic session guard. A successful
\ check establishes representation and level structure, not typing or proof.
include ../support/tester.fs
require ../../src/core/level-scope.fs
require ../../src/core/levels.fs
require ../../src/core/symbolic-session.fs
require ../../src/core/tagged-sort-boundary.fs
require ../../src/core/terms.fs
require ../support/store-faults.fs

\ A session can start only with an empty term arena. New terms and levels
\ may then be allocated without invalidating the snapshot.
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ 0 lf-term-bvar -> 0 true }T
T{ lf-ssession-begin -> false }T
lf-term-reset
T{ lf-ssession-begin -> true }T
T{ 0 lf-level-succ -> 1 true }T
T{ 1 lf-term-symbolic-sort -> 0 true }T
T{ 0 100 lf-ssession-check -> outcome-ok }T
T{ -1 100 lf-ssession-check -> outcome-invalid }T
T{ 1 100 lf-ssession-check -> outcome-invalid }T
T{ 0 -1 lf-ssession-check -> outcome-invalid }T
T{ 0 0 lf-ssession-check -> outcome-exhausted }T

\ Reusing identical indices after any reset must not revive a stale session.
lf-term-reset
T{ 1 lf-term-symbolic-sort -> 0 true }T
T{ 0 100 lf-ssession-check -> outcome-invalid }T
lf-term-reset
T{ lf-ssession-begin -> true }T
T{ 1 lf-term-symbolic-sort -> 0 true }T
lf-level-reset
T{ 0 lf-level-succ -> 1 true }T
T{ 0 100 lf-ssession-check -> outcome-invalid }T
lf-term-reset
T{ lf-ssession-begin -> true }T
T{ 1 lf-term-symbolic-sort -> 0 true }T
lf-lscope-context-reset
T{ 0 100 lf-ssession-check -> outcome-invalid }T

\ Context extension changes the snapshot, including for a root that does not
\ mention the new parameter. A failed duplicate addition does not change it.
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ 7 lf-lscope-context-add -> true }T
T{ 7 lf-level-param -> 1 true }T
T{ lf-ssession-begin -> true }T
T{ 1 lf-term-symbolic-sort -> 0 true }T
T{ 0 100 lf-ssession-check -> outcome-ok }T
T{ 7 lf-lscope-context-add -> false }T
T{ 0 100 lf-ssession-check -> outcome-ok }T
T{ 8 lf-lscope-context-add -> true }T
T{ 0 100 lf-ssession-check -> outcome-invalid }T
lf-term-reset
T{ lf-ssession-begin -> true }T
T{ 1 lf-term-symbolic-sort -> 0 true }T
T{ 0 100 lf-ssession-check -> outcome-ok }T

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
T{ 0 100 lf-ssession-check -> outcome-ok }T
T{ 1 100 lf-ssession-check -> outcome-invalid }T
T{ 2 100 lf-ssession-check -> outcome-invalid }T
T{ 3 100 lf-ssession-check -> outcome-invalid }T
T{ 4 100 lf-ssession-check -> outcome-invalid }T
T{ 5 100 lf-ssession-check -> outcome-invalid }T
T{ 6 100 lf-ssession-check -> outcome-invalid }T
T{ 7 100 lf-ssession-check -> outcome-invalid }T

\ Corrupted tags, reserved fields, child links and level nodes fail closed.
99 0 term-tag!
T{ 0 100 lf-ssession-check -> outcome-invalid }T
lf-tag-symbolic-sort 0 term-tag!
1 0 term-second!
T{ 0 100 lf-ssession-check -> outcome-invalid }T
0 0 term-second!
4 4 term-first!
T{ 4 100 lf-ssession-check -> outcome-invalid }T
0 4 term-first!
1 0 level-first!
T{ 0 100 lf-ssession-check -> outcome-invalid }T
0 0 level-first!
T{ 0 100 lf-ssession-check -> outcome-ok }T

\ A valid shared DAG requires fuel across term and level traversals. Checks
\ must not silently reset fuel for each child or each symbolic Sort.
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ 0 0 lf-level-max -> 1 true }T
T{ lf-ssession-begin -> true }T
T{ 1 lf-term-symbolic-sort -> 0 true }T
T{ 0 0 lf-term-app -> 1 true }T
T{ 1 3 lf-ssession-check -> outcome-exhausted }T
T{ 1 11 lf-ssession-check -> outcome-exhausted }T
T{ 1 12 lf-ssession-check -> outcome-ok }T
T{ 1 100 lf-ssession-check -> outcome-ok }T
T{ lf-term-count @ -> 2 }T
T{ lf-level-count @ -> 2 }T
bye

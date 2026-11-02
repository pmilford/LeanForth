\ Structural-scope regression tests for the untrusted prototype. These cases
\ inspect syntax and budget behavior; they do not test theorem acceptance.
include ../support/tester.fs
include ../../src/core/terms.fs
include ../../src/legacy/scope.fs

lf-term-reset
T{ 0 lf-term-sort -> 0 true }T
T{ 0 lf-term-bvar -> 1 true }T
T{ 1 lf-term-bvar -> 2 true }T
T{ 1 2 lf-term-pi -> 3 true }T
T{ 0 3 lf-term-pi -> 4 true }T
T{ 1 1 lf-term-lam -> 5 true }T
T{ 0 5 lf-term-lam -> 6 true }T
T{ 0 1 lf-scope-check -> lf-scope-ok }T
T{ 1 10 lf-scope-check -> lf-scope-invalid }T
T{ 3 20 lf-scope-check -> lf-scope-invalid }T
T{ 4 20 lf-scope-check -> lf-scope-ok }T
T{ 6 20 lf-scope-check -> lf-scope-ok }T
T{ 6 0 lf-scope-check -> lf-scope-exhausted }T
T{ 6 1 lf-scope-check -> lf-scope-exhausted }T
T{ 6 -1 lf-scope-check -> lf-scope-exhausted }T
T{ -1 20 lf-scope-check -> lf-scope-invalid }T
T{ 7 20 lf-scope-check -> lf-scope-invalid }T

\ A shared variable node is valid in a body but invalid in a domain; checking
\ the same DAG child at different binder depths must not use a depthless cache.
T{ 0 1 lf-term-lam -> 7 true }T
T{ 1 7 lf-term-lam -> 8 true }T
T{ 7 10 lf-scope-check -> lf-scope-ok }T
T{ 8 20 lf-scope-check -> lf-scope-invalid }T
\ Applying a sort to a sort is closed syntactically but ill typed. A structural
\ scope result must never be confused with proof or type acceptance.
T{ 0 0 lf-term-app -> 9 true }T
T{ 9 10 lf-scope-check -> lf-scope-ok }T

\ Inject malformed nodes through prototype internals to test fail-closed
\ traversal. Restore each node before testing the next corruption.
99 0 lf-term-slot !
T{ 0 10 lf-scope-check -> lf-scope-invalid }T
lf-tag-sort 0 lf-term-slot !
-1 0 lf-term-slot cell+ !
T{ 0 10 lf-scope-check -> lf-scope-invalid }T
0 0 lf-term-slot cell+ !
1 0 lf-term-slot 2 cells + !
T{ 0 10 lf-scope-check -> lf-scope-invalid }T
0 0 lf-term-slot 2 cells + !
7 7 lf-term-slot 2 cells + !
T{ 7 20 lf-scope-check -> lf-scope-invalid }T
1 7 lf-term-slot 2 cells + !
T{ 7 10 lf-scope-check -> lf-scope-ok }T
7 6 lf-term-slot 2 cells + !
T{ 6 20 lf-scope-check -> lf-scope-invalid }T
5 6 lf-term-slot 2 cells + !

\ Repeated sharing expands to 2047 visits without a cache; the budget must
\ fail closed immediately below that count and succeed at the exact boundary.
lf-term-reset
T{ 0 lf-term-sort -> 0 true }T
: grow-shared ( root count -- new-root )
  0 ?do dup dup lf-term-app 0= if -1 throw then nip loop ;
T{ 0 10 grow-shared -> 10 }T
T{ 10 2046 lf-scope-check -> lf-scope-exhausted }T
T{ 10 2047 lf-scope-check -> lf-scope-ok }T

\ Invalid global counts cannot become out-of-bounds traversal addresses.
-1 lf-term-count !
T{ 0 10 lf-scope-check -> lf-scope-invalid }T
lf-term-capacity 1+ lf-term-count !
T{ 0 10 lf-scope-check -> lf-scope-invalid }T
lf-term-reset
T{ 0 10 lf-scope-check -> lf-scope-invalid }T
bye

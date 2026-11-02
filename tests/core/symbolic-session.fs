\ Tests for an untrusted symbolic syntax/level session; not proof checking.
include ../support/tester.fs
require ../../src/core/level-scope.fs
require ../../src/core/levels.fs
require ../../src/core/symbolic-session.fs
require ../../src/core/tagged-sort-boundary.fs
require ../../src/core/terms.fs

lf-term-reset lf-level-reset lf-lscope-context-reset
T{ 42 lf-lscope-context-add -> true }T
T{ 42 lf-level-param -> 1 true }T
T{ lf-ssession-begin -> true }T
T{ 1 lf-term-symbolic-sort -> 0 true }T
T{ 0 10 lf-ssession-check -> lf-repr-ok }T
T{ 0 0 lf-ssession-check -> lf-repr-exhausted }T
\ Reusing a level index after reset must invalidate the old session, even if
\ the replacement happens to have the same parameter identifier.
lf-level-reset
T{ 42 lf-level-param -> 1 true }T
T{ 0 100 lf-ssession-check -> lf-repr-invalid }T
T{ lf-ssession-begin -> false }T
lf-term-reset
T{ lf-ssession-begin -> true }T
T{ 1 lf-term-symbolic-sort -> 0 true }T
T{ 0 100 lf-ssession-check -> lf-repr-ok }T
\ Context changes and term resets also invalidate a bound session.
T{ 43 lf-lscope-context-add -> true }T
T{ 0 100 lf-ssession-check -> lf-repr-invalid }T
lf-term-reset
T{ lf-ssession-begin -> true }T
T{ 1 lf-term-symbolic-sort -> 0 true }T
lf-term-reset
T{ 1 lf-term-symbolic-sort -> 0 true }T
T{ 0 100 lf-ssession-check -> lf-repr-invalid }T
\ Stale bare handles reused after a *new* session cannot be detected here.
\ Generation wrap must not revive an old session or permit new allocations.
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ lf-ssession-begin -> true }T
T{ 0 lf-term-symbolic-sort -> 0 true }T
-1 1 rshift lf-term-generation !
lf-term-reset
T{ lf-term-generation @ -> -1 }T
T{ 0 lf-term-symbolic-sort -> false }T
T{ 0 100 lf-ssession-check -> lf-repr-invalid }T
T{ lf-ssession-begin -> false }T
bye

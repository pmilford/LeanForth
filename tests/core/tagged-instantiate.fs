\ Untrusted symbolic substitution: structure and failure behavior only.
include ../support/tester.fs
include ../../src/core/terms.fs
include ../../src/experimental/levels.fs
include ../../src/experimental/level-scope.fs
include ../../src/experimental/tagged-sort-boundary.fs
include ../../src/experimental/symbolic-session.fs
include ../../src/experimental/generation-handles.fs
include ../../src/experimental/tagged-shift.fs
include ../../src/experimental/tagged-instantiate.fs

variable sid variable rid variable result-id variable saved-count variable saved-serial
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ lf-ssession-begin -> true }T
T{ lf-hlevel-zero -> 0 lf-level-serial @ true }T
T{ 0 lf-level-serial @ lf-hterm-sort -> 0 lf-term-serial @ true }T
lf-term-serial @ sid !
T{ 0 lf-hterm-bvar -> 1 lf-term-serial @ true }T
T{ 1 lf-hterm-bvar -> 2 lf-term-serial @ true }T
T{ 2 lf-hterm-bvar -> 3 lf-term-serial @ true }T
\ lambda domain targets 0; body has local 0, target 1, outer 2.
T{ 1 2 lf-term-app -> 4 true }T
T{ 4 3 lf-term-app -> 5 true }T
T{ 1 5 lf-term-lam -> 6 true }T
lf-term-serial @ rid !
\ Replacement is bvar 0. Under lambda it must become bvar 1.
T{ 6 rid @ 1 1 lf-term-identity drop 200 lf-tagged-instantiate -> 12 lf-term-serial @ lf-tinst-ok }T
lf-term-serial @ result-id !
T{ 7 lf-term-read -> lf-tag-bvar 0 0 true }T
T{ 8 lf-term-read -> lf-tag-bvar 1 0 true }T
T{ 9 lf-term-read -> lf-tag-app 1 8 true }T
T{ 10 lf-term-read -> lf-tag-bvar 1 0 true }T
T{ 11 lf-term-read -> lf-tag-app 9 10 true }T
T{ 12 lf-term-read -> lf-tag-lam 7 11 true }T
T{ 12 result-id @ 200 lf-hterm-check -> lf-repr-ok }T
\ Sort identities are preserved in both source and shifted replacement.
T{ 0 sid @ 1 1 lf-term-identity drop 100 lf-tagged-instantiate -> 0 sid @ lf-tinst-ok }T
T{ 1 1 lf-term-identity drop 0 sid @ 100 lf-tagged-instantiate -> 0 sid @ lf-tinst-ok }T
\ Even an unused replacement must validate; failures do not allocate.
lf-term-count @ saved-count !
T{ 0 sid @ 1 0 100 lf-tagged-instantiate -> -1 0 lf-tinst-invalid }T
T{ lf-tinst-fuel @ -> 0 }T
T{ 0 sid @ 1 1 lf-term-identity drop -1 lf-tagged-instantiate -> -1 0 lf-tinst-invalid }T
T{ 0 sid @ 1 1 lf-term-identity drop 4 lf-tagged-instantiate -> -1 0 lf-tinst-exhausted }T
T{ lf-tinst-fuel @ -> 0 }T
T{ lf-term-count @ -> saved-count @ }T
\ A bare unstamped symbolic Sort fails even when unused.
T{ 0 lf-term-symbolic-sort -> 13 true }T
T{ 0 sid @ 13 lf-term-serial @ 100 lf-tagged-instantiate -> -1 0 lf-tinst-invalid }T
\ Validation succeeds but traversal runs out after making allocations.
lf-term-count @ saved-count !
lf-term-serial @ saved-serial !
T{ 6 rid @ 1 1 lf-term-identity drop 29 lf-tagged-instantiate -> -1 0 lf-tinst-exhausted }T
T{ lf-term-count @ -> saved-count @ }T
T{ lf-term-serial @ saved-serial @ > -> true }T
\ Pi body increments depth; shifting a compound replacement retains its Sort.
T{ 0 1 lf-term-app -> 14 true }T
T{ 0 2 lf-term-pi -> 15 true }T
lf-term-serial @ rid !
T{ 15 rid @ 14 14 lf-term-identity drop 100 lf-tagged-instantiate -> 18 lf-term-serial @ lf-tinst-ok }T
lf-term-serial @ result-id !
T{ 16 lf-term-read -> lf-tag-bvar 1 0 true }T
T{ 17 lf-term-read -> lf-tag-app 0 16 true }T
T{ 18 lf-term-read -> lf-tag-pi 0 17 true }T
T{ 18 result-id @ 100 lf-hterm-check -> lf-repr-ok }T
\ A malformed source fails before visiting; reused handles remain stale.
lf-term-count @ saved-count !
1 1 lf-term-slot 2 cells + !
T{ 6 6 lf-term-identity drop 0 sid @ 100 lf-tagged-instantiate -> -1 0 lf-tinst-invalid }T
0 1 lf-term-slot 2 cells + !
T{ lf-term-count @ -> saved-count @ }T
15 lf-term-count !
T{ 0 2 lf-term-pi -> 15 true }T
T{ 15 rid @ 0 sid @ 100 lf-tagged-instantiate -> -1 0 lf-tinst-invalid }T
bye

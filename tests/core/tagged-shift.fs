\ Untrusted symbolic shifting: structural tests only, no theorem claims.
include ../support/tester.fs
include ../../src/core/terms.fs
include ../../src/experimental/levels.fs
include ../../src/experimental/level-scope.fs
include ../../src/experimental/tagged-sort-boundary.fs
include ../../src/experimental/symbolic-session.fs
include ../../src/experimental/generation-handles.fs
include ../../src/experimental/tagged-shift.fs

variable sort-id
variable root-id
variable shifted-id
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ lf-ssession-begin -> true }T
T{ lf-hlevel-zero -> 0 lf-level-serial @ true }T
T{ 0 lf-level-serial @ lf-hterm-sort -> 0 lf-term-serial @ true }T
lf-term-serial @ sort-id !
T{ 0 lf-hterm-bvar -> 1 lf-term-serial @ true }T
T{ 1 lf-hterm-bvar -> 2 lf-term-serial @ true }T
T{ 1 2 lf-term-app -> 3 true }T
T{ 0 3 lf-term-lam -> 4 true }T
lf-term-serial @ root-id !
T{ 4 root-id @ 0 1 100 lf-tagged-shift -> 7 lf-term-serial @ lf-tshift-ok }T
lf-term-serial @ shifted-id !
T{ 5 lf-term-read -> lf-tag-bvar 2 0 true }T
T{ 6 lf-term-read -> lf-tag-app 1 5 true }T
T{ 7 lf-term-read -> lf-tag-lam 0 6 true }T
T{ 7 shifted-id @ 100 lf-hterm-check -> lf-repr-ok }T
T{ 0 sort-id @ 0 4 5 lf-tagged-shift -> 0 sort-id @ lf-tshift-ok }T
T{ 0 sort-id @ 0 4 4 lf-tagged-shift -> -1 0 lf-tshift-exhausted }T
T{ 4 root-id @ -1 1 100 lf-tagged-shift -> -1 0 lf-tshift-invalid }T
T{ 4 root-id @ 0 -1 100 lf-tagged-shift -> -1 0 lf-tshift-invalid }T
T{ 4 root-id @ 0 1 -1 lf-tagged-shift -> -1 0 lf-tshift-invalid }T
T{ 4 root-id @ 0 1 15 lf-tagged-shift -> -1 0 lf-tshift-exhausted }T
T{ lf-term-count @ -> 8 }T
T{ 4 root-id @ lf-tshift-cell-max 0 100 lf-tagged-shift -> -1 0 lf-tshift-exhausted }T
T{ lf-term-count @ -> 8 }T
T{ 0 lf-term-sort -> 8 true }T
T{ 8 lf-term-serial @ 0 1 100 lf-tagged-shift -> -1 0 lf-tshift-invalid }T
T{ lf-term-count @ -> 9 }T
\ Validation uses 9 visits for this three-node application; traversal can
\ allocate its first variable before fuel runs out on the second.
T{ 1 2 lf-term-app -> 9 true }T
T{ 9 lf-term-serial @ 0 1 11 lf-tagged-shift -> -1 0 lf-tshift-exhausted }T
T{ lf-term-count @ -> 10 }T
\ Corrupted reachable child and malformed leaf are rejected.
9 9 lf-term-slot cell+ !
T{ 9 lf-term-serial @ 0 1 100 lf-tagged-shift -> -1 0 lf-tshift-invalid }T
1 9 lf-term-slot cell+ !
1 1 lf-term-slot 2 cells + !
T{ 9 lf-term-serial @ 0 1 100 lf-tagged-shift -> -1 0 lf-tshift-invalid }T
0 1 lf-term-slot 2 cells + !
\ A reused term slot cannot authenticate an old root handle.
4 lf-term-count !
T{ 0 3 lf-term-lam -> 4 true }T
T{ 4 root-id @ 0 1 100 lf-tagged-shift -> -1 0 lf-tshift-invalid }T
\ A level slot replaced without resetting the session invalidates its stamp.
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ 42 lf-lscope-context-add -> true }T
T{ 42 lf-hlevel-param -> 1 lf-level-serial @ true }T
T{ lf-ssession-begin -> true }T
T{ 1 lf-level-serial @ lf-hterm-sort -> 0 lf-term-serial @ true }T
lf-term-serial @ sort-id !
1 lf-level-count !
T{ 42 lf-hlevel-param -> 1 lf-level-serial @ true }T
T{ 0 sort-id @ 0 0 100 lf-tagged-shift -> -1 0 lf-tshift-invalid }T
\ A level reset invalidates the whole session.
lf-level-reset
T{ 0 sort-id @ 0 0 100 lf-tagged-shift -> -1 0 lf-tshift-invalid }T
bye

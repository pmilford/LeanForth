\ Weak-head syntax reduction, not a theorem or type checker.
include ../support/tester.fs
include ../../src/core/terms.fs
include ../../src/experimental/levels.fs
include ../../src/experimental/level-scope.fs
include ../../src/experimental/tagged-sort-boundary.fs
include ../../src/experimental/symbolic-session.fs
include ../../src/experimental/generation-handles.fs
include ../../src/experimental/tagged-shift.fs
include ../../src/experimental/tagged-instantiate.fs
include ../../src/experimental/tagged-beta.fs

variable sort-id variable root-id variable saved-count variable saved-serial
variable rebuilt
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ lf-ssession-begin -> true }T
T{ lf-hlevel-zero -> 0 lf-level-serial @ true }T
T{ 0 lf-level-serial @ lf-hterm-sort -> 0 lf-term-serial @ true }T
lf-term-serial @ sort-id !
T{ 0 lf-hterm-bvar -> 1 lf-term-serial @ true }T
\ (lambda x. x) Sort
T{ 0 1 lf-term-lam -> 2 true }T
T{ 2 0 lf-term-app -> 3 true }T
T{ 3 lf-term-serial @ 200 lf-tagged-beta -> 0 sort-id @ lf-tbeta-ok }T
\ Nested redex in head position: ((identity identity) Sort).
T{ 2 2 lf-term-app -> 4 true }T
T{ 4 0 lf-term-app -> 5 true }T
lf-term-serial @ root-id !
T{ 5 root-id @ 500 lf-tagged-beta -> 0 sort-id @ lf-tbeta-ok }T
6 lf-term-count !
\ Weak head does not reduce arguments or under binders.
T{ 1 3 lf-term-app -> 6 true }T
T{ 6 lf-term-serial @ 200 lf-tagged-beta -> 6 lf-term-serial @ lf-tbeta-ok }T
T{ 0 3 lf-term-lam -> 7 true }T
T{ 7 lf-term-serial @ 200 lf-tagged-beta -> 7 lf-term-serial @ lf-tbeta-ok }T
\ Reducing a head to a variable rebuilds the outer application while leaving
\ the argument intact. The allocated result still passes handle validation.
T{ 2 1 lf-term-app -> 8 true }T
T{ 8 3 lf-term-app -> 9 true }T
T{ 9 lf-term-serial @ 300 lf-tagged-beta -> 11 lf-term-serial @ lf-tbeta-ok }T
lf-term-serial @ rebuilt !
T{ 11 lf-term-read -> lf-tag-app 10 3 true }T
T{ 11 rebuilt @ 200 lf-hterm-check -> lf-repr-ok }T
8 lf-term-count !
\ A discarded invalid Sort must still fail public preflight.
T{ 0 lf-term-symbolic-sort -> 8 true }T
T{ 0 0 lf-term-lam -> 9 true }T
T{ 9 8 lf-term-app -> 10 true }T
lf-term-count @ saved-count !
T{ 10 lf-term-serial @ 200 lf-tagged-beta -> -1 0 lf-tbeta-invalid }T
T{ lf-term-count @ -> saved-count @ }T
T{ 5 0 200 lf-tagged-beta -> -1 0 lf-tbeta-invalid }T
\ Malformed source syntax fails even when the root identity is live.
1 1 lf-term-slot 2 cells + !
T{ 5 root-id @ 200 lf-tagged-beta -> -1 0 lf-tbeta-invalid }T
0 1 lf-term-slot 2 cells + !
T{ 5 root-id @ -1 lf-tagged-beta -> -1 0 lf-tbeta-invalid }T
T{ 5 root-id @ 0 lf-tagged-beta -> -1 0 lf-tbeta-exhausted }T
\ Locate a budget that fails after allocating, and prove rollback/serial advance.
: rollback-probe ( -- flag )
  500 1 do
    lf-term-count @ saved-count ! lf-term-serial @ saved-serial !
    5 root-id @ i lf-tagged-beta
    dup lf-tbeta-exhausted = lf-term-serial @ saved-serial @ > and if
      2drop drop lf-term-count @ saved-count @ = unloop exit
    then
    2drop drop
    saved-count @ lf-term-count !
  loop false ;
T{ rollback-probe -> true }T
\ Omega has no weak-head normal form; finite fuel fails and rolls back.
T{ 1 1 lf-term-app -> 11 true }T
T{ 0 11 lf-term-lam -> 12 true }T
T{ 12 12 lf-term-app -> 13 true }T
lf-term-count @ saved-count !
T{ 13 lf-term-serial @ 300 lf-tagged-beta -> -1 0 lf-tbeta-exhausted }T
T{ lf-term-count @ -> saved-count @ }T
\ Reusing an index does not revive its stale handle.
5 lf-term-count !
T{ 4 0 lf-term-app -> 5 true }T
T{ 5 root-id @ 500 lf-tagged-beta -> -1 0 lf-tbeta-invalid }T
\ Capture avoidance: (fun x => fun y => x) applied to free v0 returns
\ fun y => v1, not fun y => v0. This is syntax, not a type judgment.
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ lf-ssession-begin -> true }T
T{ lf-hlevel-zero -> 0 lf-level-serial @ true }T
T{ 0 lf-level-serial @ lf-hterm-sort -> 0 lf-term-serial @ true }T
T{ 1 lf-term-bvar -> 1 true }T
T{ 0 1 lf-term-lam -> 2 true }T
T{ 0 2 lf-term-lam -> 3 true }T
T{ 0 lf-term-bvar -> 4 true }T
T{ 3 4 lf-term-app -> 5 true }T
T{ 5 lf-term-serial @ 1000 lf-tagged-beta -> 7 lf-term-serial @ lf-tbeta-ok }T
T{ 6 lf-term-read -> lf-tag-bvar 1 0 true }T
T{ 7 lf-term-read -> lf-tag-lam 0 6 true }T
bye

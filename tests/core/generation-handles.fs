\ Development-only handle tests: slot identities detect resets and reuse, not
\ forgery, raw mutation, wrong arena kinds or stale references stored in nodes.
include ../support/tester.fs
include ../support/checks.fs
include ../../src/core/terms.fs
include ../../src/core/levels.fs
include ../../src/core/level-scope.fs
include ../../src/core/tagged-sort-boundary.fs
include ../../src/core/symbolic-session.fs
include ../../src/core/generation-handles.fs

variable old-level-identity
variable old-term-identity
variable rolled-level-identity
variable rolled-term-identity
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ 42 lf-lscope-context-add -> true }T
T{ 42 lf-hlevel-param -> 1 lf-level-serial @ true }T
lf-level-serial @ old-level-identity !
\ Before any session begins, no term is built even from a live level handle.
T{ lf-ssession-current? -> false }T
T{ 1 old-level-identity @ ' lf-hterm-sort rs-checked -> false }T
T{ 0 ' lf-hterm-bvar rs-checked -> false }T
T{ lf-term-count @ -> 0 }T
T{ lf-ssession-begin -> true }T
T{ 1 old-level-identity @ lf-hterm-sort -> 0 lf-term-serial @ true }T
lf-term-serial @ old-term-identity !
T{ 0 old-term-identity @ 100 lf-hterm-check -> lf-repr-ok }T
T{ 0 old-term-identity @ lf-hterm-valid? -> true }T
T{ 1 old-level-identity @ lf-hlevel-valid? -> true }T
T{ 777 999 true lf-hlevel-result -> 777 false }T
T{ 777 999 true lf-hterm-result -> 777 false }T
T{ 0 lf-hterm-bvar -> 1 lf-term-serial @ true }T
T{ 0 old-term-identity @ 1 lf-term-serial @ lf-hterm-app -> 2 lf-term-serial @ true }T
T{ 2 lf-term-serial @ 100 lf-hterm-check -> lf-repr-ok }T
\ Reset both arenas and reuse their indices. Old handles must not be accepted
\ by the new session even when their integer indices are currently allocated.
lf-term-reset lf-level-reset
T{ 42 lf-hlevel-param -> 1 lf-level-serial @ true }T
\ The reset ended the old session: even the new live level builds no term.
T{ lf-ssession-current? -> false }T
T{ 1 lf-level-serial @ ' lf-hterm-sort rs-checked -> false }T
T{ 0 ' lf-hterm-bvar rs-checked -> false }T
T{ lf-term-count @ -> 0 }T
\ The old level handle names a reused, live index but cannot extend it.
T{ 1 old-level-identity @ ' lf-hlevel-succ rs-checked -> false }T
T{ lf-level-count @ -> 2 }T
T{ lf-ssession-begin -> true }T
T{ 1 lf-level-serial @ lf-hterm-sort -> 0 lf-term-serial @ true }T
T{ 1 old-level-identity @ lf-hlevel-valid? -> false }T
T{ 1 old-level-identity @ lf-hterm-sort -> false }T
T{ 0 old-term-identity @ lf-hterm-valid? -> false }T
T{ 0 old-term-identity @ 100 lf-hterm-check -> lf-repr-invalid }T
T{ 0 old-term-identity @ 0 lf-term-serial @ lf-hterm-app -> false }T
T{ 0 lf-term-serial @ 0 old-term-identity @ lf-hterm-app -> false }T
T{ lf-term-count @ -> 1 }T
T{ 0 lf-term-serial @ 100 lf-hterm-check -> lf-repr-ok }T
\ Simulate an allocation transaction that discards its last slot and then
\ reuses it. The old handle must not match the new occupant even though the
\ arena generation did not change. No node may retain a rolled-back level.
T{ 0 lf-hterm-bvar -> 1 lf-term-serial @ true }T
lf-term-serial @ rolled-term-identity !
1 lf-term-count !
T{ 1 lf-hterm-bvar -> 1 lf-term-serial @ true }T
T{ 1 rolled-term-identity @ lf-hterm-valid? -> false }T
T{ 1 lf-term-serial @ lf-hterm-valid? -> true }T
T{ lf-hlevel-zero -> 0 lf-level-identities @ true }T
T{ 0 lf-level-identities @ lf-hlevel-succ -> 2 lf-level-serial @ true }T
lf-level-serial @ rolled-level-identity !
2 lf-level-count !
T{ 0 lf-level-identities @ lf-hlevel-succ -> 2 lf-level-serial @ true }T
T{ 2 rolled-level-identity @ lf-hlevel-valid? -> false }T
T{ 2 lf-level-serial @ lf-hlevel-valid? -> true }T
\ The final serial is usable once; then allocation fails without wrapping or
\ damaging the existing handle. Level reset at saturation also fails closed.
-1 1 rshift 1- lf-term-serial !
T{ 0 lf-hterm-bvar -> 2 lf-term-serial @ true }T
T{ 2 lf-term-serial @ lf-hterm-valid? -> true }T
T{ 0 lf-hterm-bvar -> false }T
T{ lf-term-count @ -> 3 }T
-1 1 rshift lf-level-serial !
T{ 0 lf-level-identities @ lf-hlevel-succ -> false }T
T{ lf-level-count @ -> 3 }T
lf-level-reset
T{ lf-level-count-valid? -> false }T
T{ lf-hlevel-zero -> false }T
bye

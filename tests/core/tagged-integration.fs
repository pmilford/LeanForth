\ Integration of two untrusted operations. Each call currently has its own
\ budget and transaction; this test does not establish a combined contract.
include ../support/tester.fs
include ../../src/core/terms.fs
include ../../src/core/levels.fs
include ../../src/core/level-scope.fs
include ../../src/core/tagged-sort-boundary.fs
include ../../src/core/symbolic-session.fs
include ../../src/core/generation-handles.fs
include ../../src/legacy/tagged-shift.fs
include ../../src/legacy/tagged-instantiate.fs
include ../../src/legacy/tagged-compare.fs
include ../../src/legacy/tagged-beta.fs
include ../../src/core/level-value.fs
include ../../src/core/level-compare.fs
include ../../src/legacy/tagged-convert.fs
include ../../src/legacy/tagged-infer.fs

variable integration-sort-id
variable integration-pi-id
variable integration-shift-id
variable integration-infer-id
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ 42 lf-lscope-context-add -> true }T
T{ 42 lf-hlevel-param -> 1 lf-level-serial @ true }T
T{ lf-ssession-begin -> true }T
T{ 1 lf-level-serial @ lf-hterm-sort -> 0 lf-term-serial @ true }T
lf-term-serial @ integration-sort-id !
T{ 0 integration-sort-id @ 0 integration-sort-id @ lf-hterm-pi -> 1 lf-term-serial @ true }T
lf-term-serial @ integration-pi-id !
T{ 1 integration-pi-id @ 0 1 1000 lf-tagged-shift -> 2 lf-term-serial @ lf-tshift-ok }T
lf-term-serial @ integration-shift-id !
T{ 2 integration-shift-id @ 1000 lf-tinfer -> 5 lf-term-serial @ lf-tinfer-ok }T
lf-term-serial @ integration-infer-id !
T{ 5 integration-infer-id @ 1000 lf-hterm-check -> lf-repr-ok }T
T{ 5 integration-infer-id @ 0 1 1000 lf-tagged-shift -> 5 integration-infer-id @ lf-tshift-ok }T
bye

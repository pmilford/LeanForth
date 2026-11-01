\ An index token is valid only while the captured level arena and parameter
\ context remain live. These tests provide no declaration or proof checking.
include ../support/tester.fs
include ../../src/core/terms.fs
include ../../src/experimental/names.fs
include ../../src/experimental/levels.fs
include ../../src/experimental/level-scope.fs
include ../../src/experimental/tagged-sort-boundary.fs
include ../../src/experimental/symbolic-session.fs
include ../../src/experimental/generation-handles.fs
include ../../src/experimental/raw-declaration-index.fs
variable old-token

\ Prepare an index while all four captured generations are independently live.
: start-index ( -- )
  lf-name-reset lf-term-reset lf-level-reset lf-lscope-context-reset
  lf-ssession-begin 0= if -1 throw then
  lf-rawdecl-begin 0= if -1 throw then ;

start-index
T{ lf-rawdecl-current? -> true }T
lf-rawdecl-token drop old-token !
lf-level-reset
T{ lf-rawdecl-current? -> false }T
T{ lf-rawdecl-token -> false }T
T{ lf-rawdecl-begin -> false }T
\ Rebinding the still-empty term arena must not revive the prior index.
T{ lf-ssession-begin -> true }T
T{ lf-rawdecl-current? -> false }T
T{ lf-rawdecl-begin -> true }T
T{ lf-rawdecl-token -> old-token @ 2 + true }T

start-index
T{ lf-rawdecl-current? -> true }T
lf-lscope-context-reset
T{ lf-rawdecl-current? -> false }T
T{ lf-rawdecl-token -> false }T
T{ lf-ssession-begin -> true }T
T{ lf-rawdecl-current? -> false }T
T{ lf-rawdecl-token -> false }T

start-index
T{ lf-rawdecl-current? -> true }T
T{ 0 lf-lscope-context-add -> false }T
T{ lf-rawdecl-current? -> true }T
T{ 11 lf-lscope-context-add -> true }T
T{ lf-rawdecl-current? -> false }T
T{ lf-rawdecl-token -> false }T
bye

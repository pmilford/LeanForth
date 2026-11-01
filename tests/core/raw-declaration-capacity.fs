\ Capacity, repeated lookup and stale-reference checks for the unchecked
\ candidate-signature index. This does not check declarations or proofs.
include ../support/tester.fs
include ../../src/core/terms.fs
include ../../src/experimental/names.fs
include ../../src/experimental/levels.fs
include ../../src/experimental/level-scope.fs
include ../../src/experimental/tagged-sort-boundary.fs
include ../../src/experimental/symbolic-session.fs
include ../../src/experimental/generation-handles.fs
include ../../src/experimental/raw-declaration-index.fs
variable capacity-id
variable extra-name
lf-name-reset lf-term-reset lf-level-reset lf-lscope-context-reset
T{ lf-ssession-begin -> true }T
T{ lf-rawdecl-begin -> true }T
T{ 0 lf-level-identities @ lf-hterm-sort -> 0 lf-term-serial @ true }T
lf-term-serial @ capacity-id !
: fill-rawdecl ( -- )
  lf-rawdecl-capacity 0 do
    0 i lf-name-num 0= abort" name allocation"
    0 capacity-id @ 1000 lf-rawdecl-put lf-rawdecl-ok <> abort" put"
  loop ;
fill-rawdecl
T{ lf-rawdecl-count @ -> lf-rawdecl-capacity }T
T{ 1 1000 lf-rawdecl-find -> 0 capacity-id @ lf-rawdecl-ok }T
T{ 1 0 lf-rawdecl-find -> -1 0 lf-rawdecl-exhausted }T
T{ 0 lf-rawdecl-capacity lf-name-num -> 33 true }T
33 extra-name !
T{ extra-name @ 0 capacity-id @ 1000 lf-rawdecl-put -> lf-rawdecl-exhausted }T
T{ lf-rawdecl-count @ -> lf-rawdecl-capacity }T
\ A stored handle becomes stale when its slot is rolled back and reused,
\ even if the name index and the symbolic session are otherwise still live.
0 lf-term-count !
T{ 0 lf-level-identities @ lf-hterm-sort -> 0 lf-term-serial @ true }T
T{ 1 1000 lf-rawdecl-find -> -1 0 lf-rawdecl-invalid }T
T{ lf-rawdecl-count @ -> lf-rawdecl-capacity }T
bye

\ Tests for untrusted symbolic universe structure and parameter contexts.
include ../support/tester.fs
include ../../src/experimental/levels.fs
include ../../src/experimental/level-scope.fs

\ Zero and a parameterized expression are structurally valid in context.
lf-level-reset lf-lscope-context-reset
T{ 0 1 lf-lscope-check -> lf-lscope-ok }T
T{ 2 lf-lscope-context-add -> true }T
T{ 2 lf-lscope-context-add -> false }T
T{ 0 lf-lscope-context-add -> false }T
T{ 2 lf-level-param -> 1 true }T
T{ 1 lf-level-succ -> 2 true }T
T{ 0 2 lf-level-imax -> 3 true }T
T{ 3 4 lf-lscope-check -> lf-lscope-ok }T
T{ 3 3 lf-lscope-check -> lf-lscope-exhausted }T
T{ 3 -1 lf-lscope-check -> lf-lscope-invalid }T
T{ -1 10 lf-lscope-check -> lf-lscope-invalid }T
T{ 4 10 lf-lscope-check -> lf-lscope-invalid }T
lf-lscope-context-reset
T{ 3 10 lf-lscope-check -> lf-lscope-invalid }T
T{ 2 lf-lscope-context-add -> true }T
T{ 3 10 lf-lscope-check -> lf-lscope-ok }T

\ Shared DAG occurrences consume fuel for each visit, not each unique node.
lf-level-reset lf-lscope-context-reset
T{ 0 0 lf-level-max -> 1 true }T
T{ 1 1 lf-level-max -> 2 true }T
T{ 2 7 lf-lscope-check -> lf-lscope-ok }T
T{ 2 6 lf-lscope-check -> lf-lscope-exhausted }T

\ Corrupt tags, reserved fields, self references and zero node are rejected.
99 2 lf-level-slot !
T{ 2 20 lf-lscope-check -> lf-lscope-invalid }T
lf-level-tag-max 2 lf-level-slot !
2 2 lf-level-slot cell+ !
T{ 2 20 lf-lscope-check -> lf-lscope-invalid }T
1 2 lf-level-slot cell+ !
1 0 lf-level-slot cell+ !
T{ 2 20 lf-lscope-check -> lf-lscope-invalid }T
0 0 lf-level-slot cell+ !
T{ 2 20 lf-lscope-check -> lf-lscope-ok }T
lf-level-reset
T{ 0 lf-level-succ -> 1 true }T
1 1 lf-level-slot 2 cells + !
T{ 1 20 lf-lscope-check -> lf-lscope-invalid }T
0 1 lf-level-slot 2 cells + !
T{ 1 20 lf-lscope-check -> lf-lscope-ok }T

\ Corrupt context counts, identifiers and duplicate entries are invalid.
lf-lscope-context-reset
T{ 2 lf-lscope-context-add -> true }T
T{ 3 lf-lscope-context-add -> true }T
2 lf-lscope-context cell+ !
T{ 0 10 lf-lscope-check -> lf-lscope-invalid }T
0 lf-lscope-context cell+ !
T{ 0 10 lf-lscope-check -> lf-lscope-invalid }T
-1 lf-lscope-context-count !
T{ 0 10 lf-lscope-check -> lf-lscope-invalid }T
T{ 4 lf-lscope-context-add -> false }T
lf-level-capacity 1+ lf-lscope-context-count !
T{ 0 10 lf-lscope-check -> lf-lscope-invalid }T
lf-lscope-context-reset
T{ 0 1 lf-lscope-check -> lf-lscope-ok }T

\ A corrupted parameter payload or reserved field must never validate.
lf-level-reset lf-lscope-context-reset
T{ 2 lf-lscope-context-add -> true }T
T{ 2 lf-level-param -> 1 true }T
0 1 lf-level-slot cell+ !
T{ 1 10 lf-lscope-check -> lf-lscope-invalid }T
2 1 lf-level-slot cell+ !
1 1 lf-level-slot 2 cells + !
T{ 1 10 lf-lscope-check -> lf-lscope-invalid }T
0 1 lf-level-slot 2 cells + !
T{ 1 10 lf-lscope-check -> lf-lscope-ok }T

\ A full parameter context remains bounded and rejects an additional entry.
lf-lscope-context-reset
: fill-level-context ( -- )
  lf-level-capacity 0 do
    i 1+ lf-lscope-context-add 0= if -1 throw then
  loop ;
fill-level-context
T{ lf-level-capacity 1+ lf-lscope-context-add -> false }T
T{ lf-lscope-context-count @ -> lf-level-capacity }T
T{ 1 10 lf-lscope-check -> lf-lscope-ok }T
T{ lf-level-count @ -> 2 }T
bye

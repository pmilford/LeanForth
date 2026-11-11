\ A surviving Sort must not silently acquire a different universe when its
\ referenced level slot is rolled back and reused within the same session.
\ This is an untrusted handle-boundary test, not a theorem check.
include ../support/tester.fs
require ../../src/core/generation-handles.fs
require ../../src/core/level-scope.fs
require ../../src/core/levels.fs
require ../../src/core/symbolic-session.fs
require ../../src/core/tagged-sort-boundary.fs
require ../../src/core/terms.fs
require ../support/store-faults.fs

variable saved-level-id
variable saved-sort-id
variable saved-root-id
\ The level slot is given back through a mark of the level store
\ (lib/store.fs), taken where the parameters begin.
create level-start /store-mark allot
: levels-back ( -- outcome ) level-start lf-levels store-rollback ;
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ level-start lf-levels store-mark -> outcome-ok }T
T{ 42 lf-lscope-context-add -> true }T
T{ 43 lf-lscope-context-add -> true }T
T{ 42 lf-hlevel-param -> 1 level-serial true }T
level-serial saved-level-id !
T{ lf-ssession-begin -> true }T
T{ 1 saved-level-id @ lf-hterm-sort -> 0 term-serial true }T
term-serial saved-sort-id !
T{ 0 lf-hterm-bvar -> 1 term-serial true }T
T{ 0 saved-sort-id @ 1 term-serial lf-hterm-pi -> 2 term-serial true }T
term-serial saved-root-id !
T{ 0 saved-sort-id @ 100 lf-hterm-check -> outcome-ok }T
T{ 2 saved-root-id @ 100 lf-hterm-check -> outcome-ok }T
T{ levels-back lf-level-count @ -> outcome-ok 1 }T
T{ 0 saved-sort-id @ 100 lf-hterm-check -> outcome-invalid }T
T{ 43 lf-hlevel-param -> 1 level-serial true }T
T{ 0 saved-sort-id @ 100 lf-hterm-check -> outcome-invalid }T
T{ 2 saved-root-id @ 100 lf-hterm-check -> outcome-invalid }T
\ The replacement itself is valid and in context; this isolates the lifetime
\ mismatch from ordinary graph or parameter-scope failures.
T{ 1 100 lf-lscope-check -> outcome-ok }T
\ A raw Sort does not acquire a valid stamp merely because it reuses a term
\ slot whose previous occupant was constructed through the handle interface.
lf-term-reset
T{ lf-ssession-begin -> true }T
T{ 1 lf-term-symbolic-sort -> 0 true }T
T{ 0 term-serial 100 lf-hterm-check -> outcome-invalid }T
\ Slot stamps are overwritten when a fresh Sort is created through the API.
lf-term-reset
T{ lf-ssession-begin -> true }T
T{ 1 level-serial lf-hterm-sort -> 0 term-serial true }T
T{ 0 term-serial 100 lf-hterm-check -> outcome-ok }T
\ A single Sort costs one syntax visit, one session visit, one level visit,
\ and one reference audit visit. Exhaustion is never treated as success.
T{ 0 term-serial 3 lf-hterm-check -> outcome-exhausted }T
T{ 0 term-serial 4 lf-hterm-check -> outcome-ok }T
T{ 0 term-serial 0 lf-hterm-check -> outcome-exhausted }T
T{ 0 term-serial -1 lf-hterm-check -> outcome-invalid }T
\ Replacing a level with byte-for-byte identical syntax still changes its
\ allocation identity; the surviving Sort must fail its audit.
T{ levels-back lf-level-count @ -> outcome-ok 1 }T
T{ 43 lf-hlevel-param -> 1 level-serial true }T
T{ 0 term-serial 100 lf-hterm-check -> outcome-invalid }T
bye

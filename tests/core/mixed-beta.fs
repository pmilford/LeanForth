\ Structural reduction tests, not proof or type checking.
include ../support/tester.fs
include ../../src/core/terms.fs
include ../../src/experimental/names.fs
include ../../src/experimental/levels.fs
include ../../src/experimental/level-scope.fs
include ../../src/experimental/tagged-sort-boundary.fs
include ../../src/experimental/symbolic-session.fs
include ../../src/experimental/generation-handles.fs
include ../../src/experimental/constant-references.fs
include ../../src/experimental/constant-term-boundary.fs
include ../../src/experimental/mixed-shift.fs
include ../../src/experimental/mixed-instantiate.fs
include ../../src/experimental/mixed-beta.fs

variable cid variable sid variable rootid variable count-before variable serial-before
create args 2 cells allot
: setup ( -- )
  lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
  lf-ssession-begin 0= abort" session"
  0 s" x" lf-name-str 0= abort" name" drop
  0 args ! 0 lf-level-identity 0= abort" level" args cell+ !
  0 lf-name-generation @ args 1 lf-cref-new 0= abort" cref"
  lf-cterm-new 0= abort" constant" cid ! drop
  0 args cell+ @ lf-hterm-sort 0= abort" sort" sid ! drop
  0 lf-term-bvar 0= abort" bvar" drop
  0 2 lf-term-lam 0= abort" identity" drop ;

setup
\ Identity preserves a constant's allocation stamp, including its reference.
T{ 3 0 lf-term-app -> 4 true }T
T{ 4 lf-term-serial @ 200 lf-mixed-beta -> 0 cid @ lf-mbeta-ok }T
T{ 0 cid @ 100 lf-cterm-check -> lf-repr-ok }T
\ A generated lambda becomes the head of the next contraction.
T{ 3 3 lf-term-app -> 5 true }T
T{ 5 0 lf-term-app -> 6 true }T
lf-term-serial @ rootid !
T{ 6 rootid @ 500 lf-mixed-beta -> 0 cid @ lf-mbeta-ok }T
\ Non-lambda heads are rebuilt; neither arguments nor binder bodies reduce.
setup
T{ 3 0 lf-term-app -> 4 true }T
T{ 3 2 lf-term-app -> 5 true }T
T{ 5 4 lf-term-app -> 6 true }T
T{ 6 lf-term-serial @ 500 lf-mixed-beta -> 8 lf-term-serial @ lf-mbeta-ok }T
T{ 8 lf-term-read -> lf-tag-app 7 4 true }T
T{ 8 lf-term-serial @ 100 lf-cterm-check -> lf-repr-ok }T
T{ 3 3 lf-term-identity drop 100 lf-mixed-beta -> 3 3 lf-term-identity drop lf-mbeta-ok }T
\ A malformed discarded argument must fail before any allocations.
T{ 0 lf-term-symbolic-sort -> 9 true }T
T{ 0 0 lf-term-lam -> 10 true }T
T{ 10 9 lf-term-app -> 11 true }T
lf-term-count @ count-before ! lf-term-serial @ serial-before !
T{ 11 lf-term-serial @ 200 lf-mixed-beta -> -1 0 lf-mbeta-invalid }T
T{ lf-term-count @ -> count-before @ }T
T{ lf-term-serial @ -> serial-before @ }T
6 lf-term-identity drop rootid !
T{ 6 rootid @ -1 lf-mixed-beta -> -1 0 lf-mbeta-invalid }T
T{ 6 rootid @ 0 lf-mixed-beta -> -1 0 lf-mbeta-exhausted }T
T{ 6 0 500 lf-mixed-beta -> -1 0 lf-mbeta-invalid }T
\ Find exhaustion after allocation and check atomic rollback and serial use.
: rollback-probe ( -- flag )
  500 1 do
    lf-term-count @ count-before ! lf-term-serial @ serial-before !
    6 rootid @ i lf-mixed-beta
    dup lf-mbeta-exhausted = lf-term-serial @ serial-before @ > and if
      2drop drop lf-term-count @ count-before @ = unloop exit
    then
    2drop drop count-before @ lf-term-count !
  loop false ;
T{ rollback-probe -> true }T
\ Reuse the first rolled-back slot; its prior allocation identity stays stale.
T{ 0 lf-term-bvar -> count-before @ true }T
T{ count-before @ serial-before @ 1+ lf-hterm-valid? -> false }T
T{ count-before @ lf-term-serial @ lf-hterm-valid? -> true }T
count-before @ lf-term-count !
\ Omega exhausts shared fuel and rolls back all generated terms.
T{ 2 2 lf-term-app -> 12 true }T
T{ 0 12 lf-term-lam -> 13 true }T
T{ 13 13 lf-term-app -> 14 true }T
lf-term-count @ count-before !
T{ 14 lf-term-serial @ 300 lf-mixed-beta -> -1 0 lf-mbeta-exhausted }T
T{ lf-term-count @ -> count-before @ }T
\ Capture avoidance under a binder preserves the constant annotation.
setup
T{ 1 lf-term-bvar -> 4 true }T
T{ 0 4 lf-term-lam -> 5 true }T
T{ 1 5 lf-term-lam -> 6 true }T
T{ 6 2 lf-term-app -> 7 true }T
T{ 7 lf-term-serial @ 500 lf-mixed-beta -> 9 lf-term-serial @ lf-mbeta-ok }T
T{ 8 lf-term-read -> lf-tag-bvar 1 0 true }T
T{ 9 lf-term-read -> lf-tag-lam 0 8 true }T
T{ 9 lf-term-serial @ 100 lf-cterm-check -> lf-repr-ok }T
lf-cref-reset
T{ 7 7 lf-term-identity drop 500 lf-mixed-beta -> -1 0 lf-mbeta-invalid }T
bye

\ Structural transformation tests; these do not establish theorem validity.
include ../support/tester.fs
include ../../src/core/terms.fs
include ../../src/core/names.fs
include ../../src/core/levels.fs
include ../../src/core/level-scope.fs
include ../../src/core/tagged-sort-boundary.fs
include ../../src/core/symbolic-session.fs
include ../../src/core/generation-handles.fs
include ../../src/core/constant-references.fs
include ../../src/core/constant-term-boundary.fs
include ../../src/kernel/mixed-shift.fs

variable rid variable cid variable sid variable rootid variable outid variable serial-before
create args 2 cells allot
: setup ( -- )
  lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
  lf-ssession-begin 0= abort" session"
  0 s" x" lf-name-str 0= abort" name" drop
  0 args ! 0 lf-level-identity 0= abort" level" args cell+ !
  0 lf-name-generation @ args 1 lf-cref-new 0= abort" cref" rid ! drop
  0 rid @ lf-cterm-new 0= abort" constant" cid ! drop
  0 args cell+ @ lf-hterm-sort 0= abort" sort" sid ! drop
  0 lf-hterm-bvar 0= abort" bound" 2drop
  1 lf-hterm-bvar 0= abort" free" 2drop
  0 3 lf-term-app 0= abort" app" drop
  2 4 lf-term-app 0= abort" app" drop
  1 5 lf-term-lam 0= abort" lam" drop
  lf-term-serial @ rootid ! ;
setup
T{ 6 rootid @ 0 1 100 lf-mixed-shift -> 10 lf-term-serial @ lf-mshift-ok }T
lf-term-serial @ outid !
T{ 7 lf-term-read -> lf-tag-bvar 2 0 true }T
T{ 8 lf-term-read -> lf-tag-app 0 7 true }T
T{ 9 lf-term-read -> lf-tag-app 2 8 true }T
T{ 10 lf-term-read -> lf-tag-lam 1 9 true }T
T{ 10 outid @ 100 lf-cterm-check -> lf-repr-ok }T
T{ 0 cid @ 0 3 3 lf-mixed-shift -> 0 cid @ lf-mshift-ok }T
T{ 0 cid @ 0 0 3 lf-mixed-shift -> 0 cid @ lf-mshift-ok }T
T{ lf-mshift-fuel @ -> 1 }T
T{ 1 sid @ 0 3 3 lf-mixed-shift -> 1 sid @ lf-mshift-ok }T
T{ 0 cid @ 0 0 1 lf-mixed-shift -> -1 0 lf-mshift-exhausted }T
T{ 6 rootid @ -1 0 100 lf-mixed-shift -> -1 0 lf-mshift-invalid }T
T{ 6 rootid @ 0 -1 100 lf-mixed-shift -> -1 0 lf-mshift-invalid }T
T{ 6 rootid @ 0 0 -1 lf-mixed-shift -> -1 0 lf-mshift-invalid }T
T{ 6 rootid @ lf-mshift-max 1 100 lf-mixed-shift -> -1 0 lf-mshift-exhausted }T
T{ lf-term-count @ -> 11 }T
\ Force failure after the first child has allocated a shifted variable.
setup
T{ 2 3 lf-term-app -> 7 true }T
lf-term-serial @ serial-before !
T{ 7 lf-term-serial @ 0 1 5 lf-mixed-shift -> -1 0 lf-mshift-exhausted }T
T{ lf-term-count @ -> 8 }T
T{ lf-term-serial @ -> serial-before @ 1+ }T
\ A rolled-back identity cannot resurrect when its slot is reused.
lf-term-serial @ outid !
T{ 0 lf-term-bvar -> 8 true }T
T{ 8 outid @ lf-hterm-valid? -> false }T
T{ 8 lf-term-serial @ lf-hterm-valid? -> true }T
\ Overflow and stale references fail without retaining output.
T{ 3 lf-term-serial @ 0 lf-mshift-max 100 lf-mixed-shift -> -1 0 lf-mshift-invalid }T
T{ 7 lf-term-identities 7 cells + @ 0 lf-mshift-max 100 lf-mixed-shift -> -1 0 lf-mshift-exhausted }T
T{ lf-term-count @ -> 9 }T
\ Shared constant occurrences each consume audit and traversal fuel.
setup
T{ 0 0 lf-term-pi -> 7 true }T
T{ 7 lf-term-serial @ 0 1 7 lf-mixed-shift -> -1 0 lf-mshift-exhausted }T
T{ 7 lf-term-serial @ 0 1 8 lf-mixed-shift -> 8 lf-term-serial @ lf-mshift-ok }T
T{ 8 lf-term-read -> lf-tag-pi 0 0 true }T
\ A malformed leaf fails before allocation.
1 3 lf-term-slot 2 cells + !
T{ 6 rootid @ 0 1 100 lf-mixed-shift -> -1 0 lf-mshift-invalid }T
0 3 lf-term-slot 2 cells + !
\ Full arena: a variable requiring reconstruction exhausts without mutation.
: fill-arena ( -- ) begin lf-term-count @ lf-term-capacity < while
  0 lf-term-bvar 0= abort" fill" drop repeat ;
fill-arena
T{ 3 lf-term-identities 3 cells + @ 0 0 100 lf-mixed-shift ->
  3 lf-term-identities 3 cells + @ lf-mshift-ok }T
T{ 3 lf-term-identities 3 cells + @ 0 1 100 lf-mixed-shift -> -1 0 lf-mshift-exhausted }T
T{ lf-term-count @ -> lf-term-capacity }T
setup
lf-cref-reset
T{ 6 rootid @ 0 1 100 lf-mixed-shift -> -1 0 lf-mshift-invalid }T
setup
lf-level-reset
T{ 6 rootid @ 0 1 100 lf-mixed-shift -> -1 0 lf-mshift-invalid }T
bye

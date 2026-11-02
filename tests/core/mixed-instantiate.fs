\ Structural transformation tests; these do not establish theorem validity.
include ../support/tester.fs
include ../support/checks.fs
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
include ../../src/kernel/mixed-instantiate.fs

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
\ Source lambda: domain constant, body app(local 0, target 1).
setup
T{ 2 3 lf-term-app -> 7 true }T
T{ 0 7 lf-term-lam -> 8 true }T
lf-term-serial @ rootid !
\ Replacement app(Sort, bvar 0): the free variable shifts under lambda.
T{ 1 2 lf-term-app -> 9 true }T
lf-term-serial @ rid !
T{ 8 rootid @ 9 rid @ 100 lf-mixed-instantiate -> 13 lf-term-serial @ lf-minst-ok }T
lf-term-serial @ outid !
T{ 10 lf-term-read -> lf-tag-bvar 1 0 true }T
T{ 11 lf-term-read -> lf-tag-app 1 10 true }T
T{ 12 lf-term-read -> lf-tag-app 2 11 true }T
T{ 13 lf-term-read -> lf-tag-lam 0 12 true }T
T{ 13 outid @ 100 lf-cterm-check -> lf-repr-ok }T
\ Free variables above the target are lowered; leaves keep identities.
T{ 3 3 lf-term-identity drop 0 cid @ 100 lf-mixed-instantiate -> 14 lf-term-serial @ lf-minst-ok }T
T{ 14 lf-term-read -> lf-tag-bvar 0 0 true }T
T{ 0 cid @ 1 sid @ 100 lf-mixed-instantiate -> 0 cid @ lf-minst-ok }T
T{ 2 2 lf-term-identity drop 0 cid @ 100 lf-mixed-instantiate -> 0 cid @ lf-minst-ok }T
T{ 2 2 lf-term-identity drop 1 sid @ 100 lf-mixed-instantiate -> 1 sid @ lf-minst-ok }T
T{ lf-minst-fuel @ 0> -> true }T
T{ 0 cid @ 1 sid @ -1 lf-mixed-instantiate -> -1 0 lf-minst-invalid }T
T{ lf-minst-fuel @ -> 0 }T
\ Two leaf audits cost four visits; visiting the source costs one more.
T{ 0 cid @ 1 sid @ 4 lf-mixed-instantiate -> -1 0 lf-minst-exhausted }T
T{ 0 cid @ 1 sid @ 5 lf-mixed-instantiate -> 0 cid @ lf-minst-ok }T
T{ lf-minst-fuel @ -> 0 }T
\ Even unused invalid or exhausted replacements are audited first.
lf-term-count @ rootid ! lf-term-serial @ serial-before !
T{ 0 cid @ 9 0 100 lf-mixed-instantiate -> -1 0 lf-minst-invalid }T
T{ 0 cid @ 9 rid @ -1 lf-mixed-instantiate -> -1 0 lf-minst-invalid }T
T{ 0 cid @ 9 rid @ 2 lf-mixed-instantiate -> -1 0 lf-minst-exhausted }T
T{ lf-minst-fuel @ -> 0 }T
T{ lf-term-count @ -> rootid @ }T
T{ lf-term-serial @ -> serial-before @ }T
\ A malformed unused replacement must fail without allocations.
1 2 lf-term-slot 2 cells + !
T{ 0 cid @ 9 rid @ 100 lf-mixed-instantiate -> -1 0 lf-minst-invalid }T
0 2 lf-term-slot 2 cells + !
T{ lf-term-count @ -> rootid @ }T
\ Exhaust after allocations, discard output, and never reuse the old identity.
setup
T{ 2 3 lf-term-app -> 7 true }T
lf-term-serial @ rootid !
lf-term-serial @ serial-before !
T{ 7 rootid @ 2 2 lf-term-identity drop 7 lf-mixed-instantiate -> -1 0 lf-minst-exhausted }T
T{ lf-term-count @ -> 8 }T
T{ lf-term-serial @ serial-before @ > -> true }T
lf-term-serial @ outid !
T{ 0 lf-term-bvar -> 8 true }T
T{ 8 outid @ lf-hterm-valid? -> false }T
\ A stale constant reference invalidates either complete input.
setup lf-cref-reset
T{ 2 2 lf-term-identity drop 0 cid @ 100 lf-mixed-instantiate -> -1 0 lf-minst-invalid }T
T{ 0 cid @ 2 2 lf-term-identity drop 100 lf-mixed-instantiate -> -1 0 lf-minst-invalid }T
\ Pi body and a replacement with its own binder: its local variable stays 0,
\ while its free variable shifts past the enclosing Pi.
setup
T{ 2 3 lf-term-app -> 7 true }T
T{ 1 7 lf-term-lam -> 8 true }T
lf-term-serial @ rid !
T{ 0 3 lf-term-pi -> 9 true }T
lf-term-serial @ rootid !
T{ 9 rootid @ 8 rid @ 100 lf-mixed-instantiate -> 13 lf-term-serial @ lf-minst-ok }T
T{ 10 lf-term-read -> lf-tag-bvar 2 0 true }T
T{ 11 lf-term-read -> lf-tag-app 2 10 true }T
T{ 12 lf-term-read -> lf-tag-lam 1 11 true }T
T{ 13 lf-term-read -> lf-tag-pi 0 12 true }T
T{ 13 lf-term-serial @ 100 lf-cterm-check -> lf-repr-ok }T
\ Shifting a maximum index fails after the audits, with rollback.
setup
T{ lf-mshift-max lf-term-bvar -> 7 true }T
T{ 0 3 lf-term-lam -> 8 true }T
lf-term-serial @ rootid !
T{ 8 rootid @ 7 7 lf-term-identity drop 100 lf-mixed-instantiate -> -1 0 lf-minst-exhausted }T
T{ lf-term-count @ -> 9 }T
\ Rebuilding in a full arena fails without changing count.
: fill-arena ( -- ) begin lf-term-count @ lf-term-capacity < while
  0 lf-term-bvar 0= abort" fill" drop repeat ;
fill-arena
T{ 3 3 lf-term-identity drop 0 cid @ 100 lf-mixed-instantiate -> -1 0 lf-minst-exhausted }T
T{ lf-term-count @ -> lf-term-capacity }T
\ Interface: the replacement shift runs on mixed-shift's record with the
\ instantiation's remaining fuel and hands back what it leaves, so both
\ fuel cells end equal; mixed-beta and mixed-infer continue with it.
setup
T{ 2 3 lf-term-app -> 7 true }T
T{ 0 7 lf-term-lam -> 8 true }T
lf-term-serial @ rootid !
T{ 1 2 lf-term-app -> 9 true }T
lf-term-serial @ rid !
T{ 8 rootid @ 9 rid @ 100 ' lf-mixed-instantiate rs-checked lf-minst-fuel @ lf-mshift-fuel @ ->
  13 lf-term-serial @ lf-minst-ok 82 82 }T
\ A chain that fills the store (node 0 is bvar 0, node k is lam(k-1, 0)) is
\ visited 64 frames deep down to node 0, the target, whose replacement
\ cannot be copied into the full store: audits 127 and 1 visits, the walk
\ 64, the shift 1.
: chain ( -- root identity )
  lf-term-reset lf-ssession-begin 0= abort" session" 0 lf-term-bvar 2drop
  63 0 do i 0 lf-term-lam 0= abort" chain" drop loop 63 dup lf-term-identity drop ;
T{ chain 0 0 lf-term-identity drop 1000 lf-mixed-instantiate
  lf-minst-fuel @ lf-mshift-fuel @ lf-term-count @ -> -1 0 lf-minst-exhausted 807 807 64 }T
\ A loose variable above the target under a binder is lowered there too:
\ fun _ : c => #0 #2 with #0 replaced by #0 becomes fun _ : c => #0 #1.
setup
T{ 2 lf-term-bvar -> 7 true }T
T{ 2 7 lf-term-app -> 8 true }T
T{ 0 8 lf-term-lam -> 9 true }T
T{ 9 9 lf-term-identity drop 2 2 lf-term-identity drop 100 lf-mixed-instantiate
  -> 12 lf-term-serial @ lf-minst-ok }T
T{ 10 lf-term-read -> lf-tag-bvar 1 0 true }T
T{ 11 lf-term-read -> lf-tag-app 2 10 true }T
T{ 12 lf-term-read -> lf-tag-lam 0 11 true }T
bye

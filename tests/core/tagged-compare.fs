\ Standalone Gforth tests for the untrusted comparator.
include ../support/tester.fs
include ../../src/core/terms.fs
include ../../src/experimental/levels.fs
include ../../src/experimental/level-scope.fs
include ../../src/experimental/tagged-sort-boundary.fs
include ../../src/experimental/symbolic-session.fs
include ../../src/experimental/generation-handles.fs
include ../../src/experimental/tagged-compare.fs
create tids 16 cells allot
: save-id ( index identity true | false -- ) 0= abort" setup" swap cells tids + ! ;
: h ( index -- index identity ) dup cells tids + @ ;
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ lf-ssession-begin -> true }T
0 lf-level-identities @ lf-hterm-sort save-id
0 lf-level-identities @ lf-hterm-sort save-id
0 lf-hterm-bvar save-id
1 lf-hterm-bvar save-id
0 h 2 h lf-hterm-app save-id
1 h 2 h lf-hterm-app save-id
0 h 2 h lf-hterm-lam save-id
1 h 2 h lf-hterm-lam save-id
0 h 2 h lf-hterm-pi save-id
1 h 3 h lf-hterm-pi save-id
T{ 0 h 1 h 1000 lf-tagged-compare -> lf-tcompare-equal }T
T{ 2 h 3 h 1000 lf-tagged-compare -> lf-tcompare-unknown }T
T{ 4 h 5 h 1000 lf-tagged-compare -> lf-tcompare-equal }T
T{ 6 h 7 h 1000 lf-tagged-compare -> lf-tcompare-equal }T
T{ 8 h 9 h 1000 lf-tagged-compare -> lf-tcompare-unknown }T
T{ 4 h 6 h 1000 lf-tagged-compare -> lf-tcompare-unknown }T
T{ 0 h 0 h 0 lf-tagged-compare -> lf-tcompare-exhausted }T
T{ lf-tcompare-fuel @ -> 0 }T
T{ 0 h 0 h -1 lf-tagged-compare -> lf-tcompare-invalid }T
T{ 0 h 1 0 1000 lf-tagged-compare -> lf-tcompare-invalid }T
T{ lf-tcompare-fuel @ -> 0 }T
\ Two complete Sort audits cost eight units; comparison costs one more.
T{ 0 h 1 h 8 lf-tagged-compare -> lf-tcompare-exhausted }T
T{ 0 h 1 h 9 lf-tagged-compare -> lf-tcompare-equal }T
\ Different live indices with identical level syntax remain unknown.
: make-succ ( -- ) 0 lf-level-identities @ lf-hlevel-succ 0= abort" level" 2drop ;
make-succ make-succ
1 lf-level-identities cell+ @ lf-hterm-sort save-id
2 lf-level-identities 2 cells + @ lf-hterm-sort save-id
T{ 10 h 11 h 1000 lf-tagged-compare -> lf-tcompare-unknown }T
T{ 0 h 10 h 1000 lf-tagged-compare -> lf-tcompare-unknown }T
\ Even a syntactic beta redex is not reduced.
6 h 2 h lf-hterm-app save-id
T{ 12 h 2 h 1000 lf-tagged-compare -> lf-tcompare-unknown }T
\ Reuse of a level slot invalidates the old Sort, even against another tag.
1 lf-level-count !
make-succ
T{ 2 h 10 h 1000 lf-tagged-compare -> lf-tcompare-invalid }T
\ Corrupt a reachable Sort stamp; mismatch at the root must not hide it.
0 0 cells lf-hsort-term-identities + !
T{ 2 h 4 h 1000 lf-tagged-compare -> lf-tcompare-invalid }T
T{ 4 h 2 h 1000 lf-tagged-compare -> lf-tcompare-invalid }T
bye

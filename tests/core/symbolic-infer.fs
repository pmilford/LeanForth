\ UNSAFE DRAFT: excluded from standard tests until Sort encodings are isolated.
\ Tests for untrusted symbolic-universe inference; no theorem is accepted.
\ Sort payloads in this test are level indices, not concrete universe values.
include ../support/tester.fs
include ../../src/experimental/symbolic-infer.fs

\ A symbolic Sort(u) has type Sort(succ(u)); inspect the resulting level DAG.
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ 42 lf-lscope-context-add -> true }T
T{ 42 lf-level-param -> 1 true }T
T{ 1 lf-term-sort -> 0 true }T
T{ 0 1000 lf-sinfer -> 1 lf-sinfer-ok }T
T{ 1 lf-term-read -> lf-tag-sort 2 0 true }T
T{ 2 lf-level-read -> lf-level-tag-succ 1 0 true }T

\ Unbound parameters and invalid level references fail before type inference.
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ 42 lf-level-param -> 1 true }T
T{ 1 lf-term-sort -> 0 true }T
T{ 0 100 lf-sinfer -> -1 lf-sinfer-invalid }T
T{ lf-term-count @ -> 1 }T
T{ lf-level-count @ -> 2 }T
T{ 42 lf-lscope-context-add -> true }T
99 0 lf-term-slot cell+ !
T{ 0 100 lf-sinfer -> -1 lf-sinfer-invalid }T
1 0 lf-term-slot cell+ !
T{ 0 0 lf-sinfer -> -1 lf-sinfer-exhausted }T
T{ lf-term-count @ -> 1 }T
T{ lf-level-count @ -> 2 }T

\ Build the expression DAG of the pinned polymorphic identity export. This
\ tests inference on its syntax, not declaration import or theorem acceptance.
: build-symbolic-identity ( -- )
  lf-term-reset lf-level-reset lf-lscope-context-reset
  2 lf-lscope-context-add 0= if -1 throw then
  2 lf-level-param 0= if -1 throw then drop
  1 lf-term-sort 0= if -1 throw then drop
  0 lf-term-bvar 0= if -1 throw then drop
  0 lf-term-sort 0= if -1 throw then drop
  1 2 lf-term-pi 0= if -1 throw then drop
  1 lf-term-bvar 0= if -1 throw then drop
  4 1 lf-term-app 0= if -1 throw then drop
  2 lf-term-bvar 0= if -1 throw then drop
  6 4 lf-term-app 0= if -1 throw then drop
  5 7 lf-term-pi 0= if -1 throw then drop
  4 8 lf-term-pi 0= if -1 throw then drop
  3 9 lf-term-pi 0= if -1 throw then drop
  0 10 lf-term-pi 0= if -1 throw then drop
  5 1 lf-term-lam 0= if -1 throw then drop
  4 12 lf-term-lam 0= if -1 throw then drop
  3 13 lf-term-lam 0= if -1 throw then drop
  0 14 lf-term-lam 0= if -1 throw then drop ;

build-symbolic-identity
T{ 11 50000 lf-sinfer -> 28 lf-sinfer-ok }T
T{ 28 lf-term-read -> lf-tag-sort 0 0 true }T
16 lf-term-count ! 2 lf-level-count !
T{ 15 50000 lf-sinfer -> 28 lf-sinfer-ok }T
T{ 28 11 50000 lf-compare -> lf-compare-equal }T
bye

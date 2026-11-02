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

\ Pi (A : Sort u), Sort u has a sort whose level is formed from the
\ inferred domain and body levels. The two successors need not share an ID.
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ 42 lf-lscope-context-add -> true }T
T{ 42 lf-level-param -> 1 true }T
T{ 1 lf-term-sort -> 0 true }T
T{ 0 0 lf-term-pi -> 1 true }T
T{ 1 1000 lf-sinfer -> 4 lf-sinfer-ok }T
T{ 4 lf-term-read -> lf-tag-sort 4 0 true }T
T{ 4 lf-level-read -> lf-level-tag-imax 2 3 true }T
T{ 2 lf-level-read -> lf-level-tag-succ 1 0 true }T
T{ 3 lf-level-read -> lf-level-tag-succ 1 0 true }T

\ A sort is not a function. The current experiment conservatively reports
\ unknown; the Lean oracle separately rejects this application outright.
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ 42 lf-lscope-context-add -> true }T
T{ 42 lf-level-param -> 1 true }T
T{ 1 lf-term-sort -> 0 true }T
T{ 0 0 lf-term-app -> 1 true }T
T{ 1 1000 lf-sinfer -> -1 lf-sinfer-unknown }T
T{ lf-term-count @ -> 2 }T
T{ lf-level-count @ -> 2 }T

\ Check every small fuel budget independently. In particular, exhaustion
\ after intermediate allocation must restore both arenas; a successful run
\ must be possible once enough fuel is supplied. This is not a soundness proof.
variable fuel-saw-success
variable fuel-saw-exhaustion
: symbolic-fuel-regressions ( -- )
  0 fuel-saw-success ! 0 fuel-saw-exhaustion !
  100 0 do
    lf-term-reset lf-level-reset lf-lscope-context-reset
    42 lf-lscope-context-add 0= abort" context allocation failed"
    42 lf-level-param 0= abort" parameter allocation failed" drop
    1 lf-term-sort 0= abort" sort allocation failed" drop
    0 0 lf-term-pi 0= abort" pi allocation failed" drop
    1 i lf-sinfer
    dup lf-sinfer-exhausted = if
      drop -1 <> abort" exhaustion returned a result"
      lf-term-count @ 2 <> abort" exhaustion leaked terms"
      lf-level-count @ 2 <> abort" exhaustion leaked levels"
      true fuel-saw-exhaustion !
    else
      lf-sinfer-ok <> abort" unexpected inference status"
      lf-term-valid? 0= abort" invalid successful result"
      true fuel-saw-success !
    then
  loop
  fuel-saw-success @ 0= abort" no successful budget"
  fuel-saw-exhaustion @ 0= abort" no exhausted budget" ;
symbolic-fuel-regressions

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
\ Level statuses keep their meaning; other codes are invalid, never ok.
T{ lf-lscope-ok lf-sinfer-level-status -> lf-sinfer-ok }T
T{ lf-lscope-invalid lf-sinfer-level-status -> lf-sinfer-invalid }T
T{ lf-lscope-exhausted lf-sinfer-level-status -> lf-sinfer-exhausted }T
T{ 3 lf-sinfer-level-status -> lf-sinfer-invalid }T
T{ 99 lf-sinfer-level-status -> lf-sinfer-invalid }T
bye

\ Exercise candidate declaration checks without creating theorem handles.
include ../support/tester.fs
include ../../src/legacy/declaration-probe.fs
include ../support/term-cases.fs
include ../support/composition.fs

\ The closed identity theorem from the Lean declaration oracle, followed by
\ an altered body, a non-type claim, and a non-proposition claim.
lf-term-reset
T{ 0 lf-term-sort -> 0 true }T
T{ 0 lf-term-bvar -> 1 true }T
T{ 1 lf-term-bvar -> 2 true }T
T{ 1 2 lf-term-pi -> 3 true }T
T{ 0 3 lf-term-pi -> 4 true }T
T{ 1 1 lf-term-lam -> 5 true }T
T{ 0 5 lf-term-lam -> 6 true }T
T{ 1 2 lf-term-lam -> 7 true }T
T{ 0 7 lf-term-lam -> 8 true }T
T{ 1 lf-term-sort -> 9 true }T
T{ 4 6 50000 lf-declaration-probe -> lf-infer-ok }T
T{ lf-term-count @ -> 10 }T
T{ 4 8 50000 lf-declaration-probe -> lf-infer-unknown }T
T{ 6 6 50000 lf-declaration-probe -> lf-infer-unknown }T
T{ 9 0 50000 lf-declaration-probe -> lf-infer-unknown }T
T{ 4 6 0 lf-declaration-probe -> lf-infer-exhausted }T
T{ -1 6 100 lf-declaration-probe -> lf-infer-invalid }T
T{ 4 -1 50000 lf-declaration-probe -> lf-infer-invalid }T
T{ 4 10 50000 lf-declaration-probe -> lf-infer-invalid }T
T{ 0 -1 50000 lf-declaration-probe -> lf-infer-invalid }T
\ A non-proposition claim cannot hide an open or malformed value root.
T{ 0 1 50000 lf-declaration-probe -> lf-infer-invalid }T
T{ 1 6 50000 lf-declaration-probe -> lf-infer-invalid }T
\ With one visit the claim is inspected but the open value is not yet seen.
T{ 0 1 1 lf-declaration-probe -> lf-infer-exhausted }T
T{ 0 1 2 lf-declaration-probe -> lf-infer-invalid }T
999 6 lf-term-slot !
T{ 0 6 50000 lf-declaration-probe -> lf-infer-invalid }T
lf-tag-lam 6 lf-term-slot !
6 6 lf-term-slot 2 cells + !
T{ 0 6 50000 lf-declaration-probe -> lf-infer-invalid }T
5 6 lf-term-slot 2 cells + !
T{ 4 6 50000 lf-declaration-probe -> lf-infer-ok }T
T{ 4 6 -1 lf-declaration-probe -> lf-infer-invalid }T
T{ lf-compare-equal lf-probe-compare-status -> lf-infer-ok }T
T{ lf-compare-invalid lf-probe-compare-status -> lf-infer-invalid }T
T{ lf-compare-exhausted lf-probe-compare-status -> lf-infer-exhausted }T
T{ lf-compare-unknown lf-probe-compare-status -> lf-infer-unknown }T
T{ 99 lf-probe-compare-status -> lf-infer-invalid }T
T{ lf-term-count @ -> 10 }T
T{ 4 lf-term-read -> lf-tag-pi 0 3 true }T
T{ 6 lf-term-read -> lf-tag-lam 0 5 true }T
\ All budgets either complete or exhaust without retaining temporary nodes.
: test-probe-budgets ( -- )
  300 0 do
    4 6 i lf-declaration-probe
    dup lf-infer-ok <> swap lf-infer-exhausted <> and if -1 throw then
    lf-term-count @ 10 <> if -1 throw then
  loop ;
test-probe-budgets
\ A full arena must report exhaustion and preserve all original records.
: fill-probe-arena ( -- )
  begin lf-term-count @ lf-term-capacity < while
    0 lf-term-sort 0= if -1 throw then drop
  repeat ;
fill-probe-arena
T{ 4 6 50000 lf-declaration-probe -> lf-infer-exhausted }T
T{ lf-term-count @ -> lf-term-capacity }T
T{ 4 lf-term-read -> lf-tag-pi 0 3 true }T
T{ 6 lf-term-read -> lf-tag-lam 0 5 true }T

\ Probe the larger composition fixture without retaining temporary nodes.
build-composition
T{ 10 20 50000 lf-declaration-probe -> lf-infer-ok }T
T{ lf-term-count @ -> 21 }T
bye

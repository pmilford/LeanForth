\ Untrusted declaration diagnostics. Success creates no checked theorem.
include ../support/tester.fs
include ../../src/core/terms.fs
include ../../src/core/levels.fs
include ../../src/core/level-scope.fs
include ../../src/core/tagged-sort-boundary.fs
include ../../src/core/symbolic-session.fs
include ../../src/core/generation-handles.fs
include ../../src/legacy/tagged-shift.fs
include ../../src/legacy/tagged-instantiate.fs
include ../../src/legacy/tagged-compare.fs
include ../../src/legacy/tagged-beta.fs
include ../../src/kernel/level-value.fs
include ../../src/kernel/level-compare.fs
include ../../src/legacy/tagged-convert.fs
include ../../src/legacy/tagged-infer.fs
include ../../src/legacy/tagged-declaration-probe.fs

variable claim-id
variable proof-id
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ lf-ssession-begin -> true }T
T{ 0 lf-level-identities @ lf-hterm-sort -> 0 lf-term-serial @ true }T
T{ 0 lf-term-bvar -> 1 true }T
T{ 1 lf-term-bvar -> 2 true }T
T{ 1 2 lf-term-pi -> 3 true }T
T{ 0 3 lf-term-pi -> 4 true }T
lf-term-serial @ claim-id !
T{ 1 1 lf-term-lam -> 5 true }T
T{ 0 5 lf-term-lam -> 6 true }T
lf-term-serial @ proof-id !
\ forall P : Prop, P -> P, with value fun P proof => proof.
T{ 4 claim-id @ 6 proof-id @ 10000 lf-tagged-declaration-probe -> lf-tprobe-ok }T
T{ lf-term-count @ -> 7 }T
T{ lf-level-count @ -> 1 }T
\ Sweep budgets through the complete two-root diagnostic. Every result,
\ including exhaustion after allocation, restores both input arenas.
variable probe-saw-ok
variable probe-saw-exhaustion
: declaration-probe-fuel-sweep ( -- )
  0 probe-saw-ok ! 0 probe-saw-exhaustion !
  500 0 do
    4 claim-id @ 6 proof-id @ i lf-tagged-declaration-probe
    dup lf-tprobe-exhausted = if
      drop true probe-saw-exhaustion !
    else
      lf-tprobe-ok <> abort" unexpected probe status"
      true probe-saw-ok !
    then
    lf-term-count @ 7 <> abort" probe term leak"
    lf-level-count @ 1 <> abort" probe level leak"
  loop
  probe-saw-ok @ 0= abort" no successful budget"
  probe-saw-exhaustion @ 0= abort" no exhausted budget" ;
declaration-probe-fuel-sweep
\ A wrong value, stale handle and insufficient fuel never succeed.
T{ 4 claim-id @ 0 0 lf-term-identity drop 10000 lf-tagged-declaration-probe -> lf-tprobe-unknown }T
T{ 4 claim-id @ 6 proof-id @ 1+ 10000 lf-tagged-declaration-probe -> lf-tprobe-invalid }T
T{ 4 claim-id @ 6 proof-id @ 0 lf-tagged-declaration-probe -> lf-tprobe-exhausted }T
\ A non-propositional claim must not hide an invalid value handle.
T{ 0 0 lf-term-identity drop -1 0 1000 lf-tagged-declaration-probe -> lf-tprobe-invalid }T
T{ lf-tprobe-fuel @ -> 0 }T
T{ 4 claim-id @ 6 proof-id @ -1 lf-tagged-declaration-probe -> lf-tprobe-invalid }T
T{ lf-tprobe-fuel @ -> 0 }T
T{ lf-term-count @ -> 7 }T
T{ lf-level-count @ -> 1 }T

\ Reconstruct the exact core nodes of the checked-in polymorphic identity
\ export. This construction is manual; it does not test NDJSON importing.
: build-poly-identity ( -- )
  lf-term-reset lf-level-reset lf-lscope-context-reset
  2 lf-lscope-context-add 0= abort" context"
  2 lf-hlevel-param 0= abort" universe" 2drop
  lf-ssession-begin 0= abort" session"
  1 lf-level-serial @ lf-hterm-sort 0= abort" Sort u" 2drop
  0 lf-term-bvar 0= abort" bvar" drop
  0 lf-level-identities @ lf-hterm-sort 0= abort" Prop" 2drop
  1 2 lf-term-pi 0= abort" Pi" drop
  1 lf-term-bvar 0= abort" bvar" drop
  4 1 lf-term-app 0= abort" app" drop
  2 lf-term-bvar 0= abort" bvar" drop
  6 4 lf-term-app 0= abort" app" drop
  5 7 lf-term-pi 0= abort" Pi" drop
  4 8 lf-term-pi 0= abort" Pi" drop
  3 9 lf-term-pi 0= abort" Pi" drop
  0 10 lf-term-pi 0= abort" Pi" drop
  5 1 lf-term-lam 0= abort" lambda" drop
  4 12 lf-term-lam 0= abort" lambda" drop
  3 13 lf-term-lam 0= abort" lambda" drop
  0 14 lf-term-lam 0= abort" lambda" drop ;
build-poly-identity
T{ 11 11 lf-term-identity drop 15 15 lf-term-identity drop 100000 lf-tagged-declaration-probe -> lf-tprobe-ok }T
T{ lf-term-count @ -> 16 }T
T{ lf-level-count @ -> 2 }T
bye

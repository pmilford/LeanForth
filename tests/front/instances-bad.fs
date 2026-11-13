\ The instance check refuses data that differs from the types (plan
\ FE1e3; FE1E §4; src/front/instances.fs): tests/front/bad-keys.elab.ndjson
\ is tests/front/whnf-slice.elab.ndjson with instOfNatNat's last key a
\ literal 0 where Lean has a star, and instMulNat recorded as an instance
\ of Add, and instSubNat's Nat key a star, as a no_index annotation the
\ export drops would leave it (its header's SHA-256 recomputed, so the
\ reader accepts it). lf-inst-check answers invalid with error 113 and
\ 112, and unsupported (unverified) with error 114; the other
\ instances still check; a query whose root holds a refused instance is
\ refused. Every T{ }T checks the data stack's depth.
include ../support/tester.fs
require ../../src/front/instances.fs
require ./menv-slice.fs

: bad-data ( -- c-addr u ) s" tests/front/bad-keys.elab.ndjson" ;
14 menv-lib stage-init menv-must menv-slice menv-lib stage-read menv-must
bad-data menv-lib menv-digest elab-read menv-must
menv-lib stage-seal menv-must menv-lib menv-feed lf-feed menv-must menv-lib lf-menv-stage!
lf-mctx-reset lf-lctx-reset

: inst-named ( c-addr u -- i ) menv-name elab-decl-of drop elab-instance-of drop ;
T{ s" instOfNatNat" inst-named lf-inst-check lf-inst-error -> outcome-invalid 113 }T
T{ s" instMulNat" inst-named lf-inst-check lf-inst-error -> outcome-invalid 112 }T
T{ s" instSubNat" inst-named lf-inst-check lf-inst-error -> outcome-unsupported 114 }T
T{ s" instAddNat" inst-named lf-inst-check -> outcome-ok }T
T{ lf-mctx-depth lf-mctx-marks -> 0 0 }T
bye

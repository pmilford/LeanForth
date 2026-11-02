\ Test-only transport for one exported definition (protocol in
\ tests/support/export-reader.fs). It optionally replaces every universe
\ parameter by a level record (lf-mixed-level-substitute), then runs the
\ current lf-mixed-definition-probe with an empty signature index.
\ Output: the probe status; after a substitution also the Lean-style shapes
\ of the claim and the value. A status of 0 is an untrusted diagnostic,
\ never theorem acceptance. Malformed input prints nothing and fails.
include ../../src/main.fs
include ../support/export-reader.fs

: substitute-root ( index identity -- index' identity' )
  params actuals subst-count @ 50000 lf-mixed-level-substitute ok? must ;
: specialize ( -- )
  claim-index @ claim-id @ substitute-root claim-id ! claim-index !
  value-index @ value-id @ substitute-root value-id ! value-index ! ;
: probe ( fuel -- status )
  >r lf-msp-begin must lf-msp-token must
  claim-index @ claim-id @ value-index @ value-id @ r> lf-mixed-definition-probe ;
: run ( -- )
  read-export subst-count @ if specialize then probe . cr
  subst-count @ if claim-index @ emit-shape cr value-index @ emit-shape cr then ;
: main ( -- ) ['] run catch if 1 (bye) then ;
main bye

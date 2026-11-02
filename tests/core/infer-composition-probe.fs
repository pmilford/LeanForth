\ Construct the pinned Lean composition term in the experimental term arena.
\ This is an untrusted inference regression, not a theorem acceptance test.
include ../support/tester.fs
include ../../src/legacy/infer.fs
include ../support/term-cases.fs
include ../support/composition.fs

\ Infer the value's type and compare it with the manually reconstructed claim.
\ Neither success status creates a theorem handle or imports a declaration.
: compare-composition ( -- status )
  20 50000 lf-infer dup if nip exit then drop
  10 50000 lf-compare ;
build-composition
T{ compare-composition -> lf-compare-equal }T
bye

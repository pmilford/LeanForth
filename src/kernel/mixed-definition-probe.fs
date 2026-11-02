\ UNTRUSTED mixed type/value diagnostic; load mixed-infer.fs and dependencies.
\ Signatures, including nested dependencies, are unchecked assumptions. This
\ registers nothing, proves no theorem, and returns no term or certificate.
\ One stable session/index, suffix-only rollback, no raw mutation, concurrency
\ or reentrancy are assumed. Unsupported inference/conversion is unknown.
0 constant lf-mdefinition-ok
1 constant lf-mdefinition-invalid
2 constant lf-mdefinition-exhausted
3 constant lf-mdefinition-unknown
variable lf-mdefinition-token
variable lf-mdefinition-type
variable lf-mdefinition-type-id
variable lf-mdefinition-value
variable lf-mdefinition-value-id
variable lf-mdefinition-fuel
variable lf-mdefinition-terms
variable lf-mdefinition-levels
variable lf-mdefinition-crefs

: lf-mdefinition-infer-status ( status -- status )
  case lf-minfer-ok of lf-mdefinition-ok endof
    lf-minfer-invalid of lf-mdefinition-invalid endof
    lf-minfer-exhausted of lf-mdefinition-exhausted endof
    lf-minfer-unknown of lf-mdefinition-unknown endof
    drop lf-mdefinition-invalid 0 endcase ;

\ Both closed source graphs and the entire index must be audited before any
\ allocation: otherwise a stale second root or index handle could revive.
: lf-mdefinition-preflight ( -- status )
  lf-mdefinition-type @ lf-mdefinition-type-id @ 0 lf-mdefinition-fuel @
  lf-constant-term-scope lf-minfer-repr-status lf-mdefinition-infer-status
  ?dup if exit then lf-cts-fuel @ lf-mdefinition-fuel !
  lf-mdefinition-value @ lf-mdefinition-value-id @ 0 lf-mdefinition-fuel @
  lf-constant-term-scope lf-minfer-repr-status lf-mdefinition-infer-status
  ?dup if exit then lf-cts-fuel @ lf-mdefinition-fuel !
  lf-mdefinition-token @ lf-mdefinition-fuel @ lf-mixed-signature-audit
  lf-minfer-msp-status lf-mdefinition-infer-status
  ?dup if exit then lf-msa-fuel @ lf-mdefinition-fuel !
  lf-mdefinition-ok ;

\ Internal inference consumes the original preflighted roots only. Its shared
\ state and all three arena marks are initialized once for the pair.
: lf-mdefinition-walk ( -- status )
  lf-mdefinition-token @ lf-minfer-token !
  lf-mdefinition-fuel @ lf-minfer-fuel !
  lf-mdefinition-terms @ lf-minfer-term-start !
  lf-mdefinition-levels @ lf-minfer-level-start !
  lf-mdefinition-crefs @ lf-minfer-cref-start !
  0 lf-minfer-depth ! 0 lf-minfer-context-depth !
  lf-mdefinition-type @ lf-minfer-walk
  lf-mdefinition-infer-status ?dup if nip exit then
  lf-minfer-sort-level lf-mdefinition-infer-status ?dup if nip exit then drop
  lf-mdefinition-value @ lf-minfer-walk
  lf-mdefinition-infer-status ?dup if nip exit then
  lf-mdefinition-type @ lf-minfer-compare lf-mdefinition-infer-status ;

\ ( token type type-id value value-id fuel -- status ) One shared visit fuel;
\ all failures conservatively report zero in lf-mdefinition-fuel. Success
\ reports the remaining fuel. Every result restores all three arena counts;
\ allocation serials never rewind. No generated handles escape this word.
: lf-mixed-definition-probe ( token type tid value vid fuel -- status )
  dup 0< if drop 2drop 2drop drop 0 lf-mdefinition-fuel ! lf-mdefinition-invalid exit then
  lf-mdefinition-fuel ! lf-mdefinition-value-id ! lf-mdefinition-value !
  lf-mdefinition-type-id ! lf-mdefinition-type ! lf-mdefinition-token !
  lf-term-count-valid? lf-level-count-valid? and lf-cref-state-valid? and 0= if
    0 lf-mdefinition-fuel ! lf-mdefinition-invalid exit then
  lf-term-count @ lf-mdefinition-terms ! lf-level-count @ lf-mdefinition-levels !
  lf-cref-count @ lf-mdefinition-crefs !
  lf-mdefinition-preflight ?dup if 0 lf-mdefinition-fuel ! exit then
  lf-mdefinition-walk
  lf-minfer-fuel @ lf-mdefinition-fuel !
  lf-mdefinition-terms @ lf-term-count ! lf-mdefinition-levels @ lf-level-count !
  lf-mdefinition-crefs @ lf-cref-count !
  dup if 0 lf-mdefinition-fuel ! then ;

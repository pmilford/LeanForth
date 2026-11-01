\ Untrusted diagnostic for a type/value pair in the tagged symbolic fragment.
\ It is NOT a theorem checker, declaration importer, certificate, or trusted
\ kernel, and it registers nothing. It assumes one stable symbolic session,
\ no concurrent/raw mutation and suffix-only rollback. Caller loads the term,
\ level, scope, representation, session, handles, shift, instantiate, compare,
\ beta, level-value, level-compare, convert and infer modules first.
\ The active session captures an explicitly supplied lf-lscope universe context.
\ Inference starts with no term binders, so success requires closed inputs.
\ Proof irrelevance, eta and other unsupported conversions remain unknown.
\ Success only reports that these incomplete experimental checks found no
\ obstacle; explicit human review is required before any trusted use.

0 constant lf-candidate-ok
1 constant lf-candidate-invalid
2 constant lf-candidate-exhausted
3 constant lf-candidate-unknown
variable lf-candidate-type
variable lf-candidate-type-id
variable lf-candidate-value
variable lf-candidate-value-id
variable lf-candidate-term-start
variable lf-candidate-level-start
variable lf-candidate-fuel

\ Map each dependency's status explicitly; unrecognized codes fail closed.
: lf-candidate-repr-status ( status -- status )
  case
    lf-repr-ok of lf-candidate-ok endof
    lf-repr-invalid of lf-candidate-invalid endof
    lf-repr-exhausted of lf-candidate-exhausted endof
    drop lf-candidate-invalid 0
  endcase ;
: lf-candidate-infer-status ( status -- status )
  case
    lf-tinfer-ok of lf-candidate-ok endof
    lf-tinfer-invalid of lf-candidate-invalid endof
    lf-tinfer-exhausted of lf-candidate-exhausted endof
    lf-tinfer-unknown of lf-candidate-unknown endof
    drop lf-candidate-invalid 0
  endcase ;
: lf-candidate-convert-status ( status -- status )
  case
    lf-tconvert-equal of lf-candidate-ok endof
    lf-tconvert-invalid of lf-candidate-invalid endof
    lf-tconvert-exhausted of lf-candidate-exhausted endof
    lf-tconvert-unknown of lf-candidate-unknown endof
    drop lf-candidate-invalid 0
  endcase ;

\ Check that the claim infers directly to a symbolic Sort, then check that
\ the value's inferred type matches the claim using conservative conversion.
\ An unsupported conversion is unknown, never theorem acceptance.
: lf-candidate-walk ( -- status )
  \ Validate both roots before any early unknown result from the claim.
  lf-candidate-type @ lf-candidate-type-id @ lf-candidate-fuel @ lf-hterm-check lf-candidate-repr-status
  ?dup if 0 lf-candidate-fuel ! exit then lf-href-fuel @ lf-candidate-fuel !
  lf-candidate-value @ lf-candidate-value-id @ lf-candidate-fuel @ lf-hterm-check lf-candidate-repr-status
  ?dup if 0 lf-candidate-fuel ! exit then lf-href-fuel @ lf-candidate-fuel !
  lf-candidate-type @ lf-candidate-type-id @ lf-candidate-fuel @ lf-tinfer lf-candidate-infer-status
  dup if 0 lf-candidate-fuel ! >r 2drop r> exit then 2drop
  lf-tinfer-fuel @ lf-candidate-fuel !
  lf-tinfer-sort-level lf-candidate-infer-status dup if nip exit then drop
  drop
  lf-candidate-value @ lf-candidate-value-id @ lf-candidate-fuel @ lf-tinfer lf-candidate-infer-status
  dup if 0 lf-candidate-fuel ! >r 2drop r> exit then drop
  lf-tinfer-fuel @ lf-candidate-fuel !
  lf-candidate-type @ lf-candidate-type-id @ lf-candidate-fuel @ lf-tagged-convert
  lf-tconvert-fuel @ lf-candidate-fuel ! lf-candidate-convert-status ;

\ Validate a pair of handles through inference with one shared visit budget.
\ Restore both arena counts on every result; allocation IDs never roll back.
\ ( type type-id value value-id fuel -- status )
: lf-candidate-definition-probe ( type tid value vid fuel -- status )
  dup 0< if drop 2drop 2drop 0 lf-candidate-fuel ! lf-candidate-invalid exit then lf-candidate-fuel !
  lf-candidate-value-id ! lf-candidate-value !
  lf-candidate-type-id ! lf-candidate-type !
  lf-term-count-valid? lf-level-count-valid? and 0= if lf-candidate-invalid exit then
  lf-term-count @ lf-candidate-term-start !
  lf-level-count @ lf-candidate-level-start !
  lf-candidate-walk
  lf-candidate-term-start @ lf-term-count !
  lf-candidate-level-start @ lf-level-count ! ;

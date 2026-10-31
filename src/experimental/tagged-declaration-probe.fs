\ Untrusted diagnostic for a type/value pair in the tagged symbolic fragment.
\ It is NOT a theorem checker, declaration importer, certificate, or trusted
\ kernel, and it registers nothing. It assumes one stable symbolic session,
\ no concurrent/raw mutation and suffix-only rollback. Caller loads the term,
\ level, session, handle, shift, instantiate, compare and infer modules first.
\ Success only reports that these incomplete experimental checks found no
\ obstacle; explicit human review is required before any trusted use.

lf-tinfer-ok constant lf-tprobe-ok
lf-tinfer-invalid constant lf-tprobe-invalid
lf-tinfer-exhausted constant lf-tprobe-exhausted
lf-tinfer-unknown constant lf-tprobe-unknown
variable lf-tprobe-type
variable lf-tprobe-type-id
variable lf-tprobe-value
variable lf-tprobe-value-id
variable lf-tprobe-term-start
variable lf-tprobe-level-start
variable lf-tprobe-fuel

\ Check that the claim infers directly to literal Sort zero, then check that
\ the value's inferred type matches the claim using conservative syntax.
\ A nonliteral or unsupported conversion is unknown, never theorem acceptance.
: lf-tprobe-walk ( -- status )
  \ Validate both roots before any early unknown result from the claim.
  lf-tprobe-type @ lf-tprobe-type-id @ lf-tprobe-fuel @ lf-hterm-check
  ?dup if 0 lf-tprobe-fuel ! exit then lf-href-fuel @ lf-tprobe-fuel !
  lf-tprobe-value @ lf-tprobe-value-id @ lf-tprobe-fuel @ lf-hterm-check
  ?dup if 0 lf-tprobe-fuel ! exit then lf-href-fuel @ lf-tprobe-fuel !
  lf-tprobe-type @ lf-tprobe-type-id @ lf-tprobe-fuel @ lf-tinfer
  dup if 0 lf-tprobe-fuel ! >r 2drop r> exit then 2drop
  lf-tinfer-fuel @ lf-tprobe-fuel !
  lf-tinfer-sort-level dup if nip exit then drop
  0<> if lf-tprobe-unknown exit then
  lf-tprobe-value @ lf-tprobe-value-id @ lf-tprobe-fuel @ lf-tinfer
  dup if 0 lf-tprobe-fuel ! >r 2drop r> exit then drop
  lf-tinfer-fuel @ lf-tprobe-fuel !
  lf-tprobe-type @ lf-tprobe-type-id @ lf-tprobe-fuel @ lf-tagged-compare
  lf-tcompare-fuel @ lf-tprobe-fuel ! ;

\ Validate a pair of handles through inference with one shared visit budget.
\ Restore both arena counts on every result; allocation IDs never roll back.
\ ( type type-id value value-id fuel -- status )
: lf-tagged-declaration-probe ( type tid value vid fuel -- status )
  dup 0< if drop 2drop 2drop 0 lf-tprobe-fuel ! lf-tprobe-invalid exit then lf-tprobe-fuel !
  lf-tprobe-value-id ! lf-tprobe-value !
  lf-tprobe-type-id ! lf-tprobe-type !
  lf-term-count-valid? lf-level-count-valid? and 0= if lf-tprobe-invalid exit then
  lf-term-count @ lf-tprobe-term-start !
  lf-level-count @ lf-tprobe-level-start !
  lf-tprobe-walk
  lf-tprobe-term-start @ lf-term-count !
  lf-tprobe-level-start @ lf-level-count ! ;

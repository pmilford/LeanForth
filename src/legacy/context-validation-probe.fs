\ Untrusted context-domain diagnostic. Load tagged-context-infer.fs and its
\ dependencies first. This does not authorize a theorem or establish Lean
\ compatibility. Constants and other unsupported syntax are not supported;
\ a non-Sort inferred type is UNKNOWN because it might reduce to a Sort.
\ Handles are forgeable stamps, not capabilities. No raw arena mutation,
\ session changes, concurrent or nested calls are permitted. Input must be
\ readable, aligned and disjoint from ALL mutable storage of this module and
\ its dependencies, including arenas and scratch; Forth cannot check this.

create lf-cv-domains lf-term-capacity 2 * cells allot
variable lf-cv-count
variable lf-cv-address
variable lf-cv-fuel
variable lf-cv-terms
variable lf-cv-levels

: lf-cv-pair ( n -- address ) 2 * cells lf-cv-domains + ;

\ Translate explicitly, including unexpected dependency statuses.
: lf-cv-status ( status -- status )
  case
    lf-tinfer-ok of lf-tinfer-ok endof
    lf-tinfer-invalid of lf-tinfer-invalid endof
    lf-tinfer-exhausted of lf-tinfer-exhausted endof
    lf-tinfer-unknown of lf-tinfer-unknown endof
    drop lf-tinfer-invalid 0
  endcase ;

\ Copy first, then audit every original handle and its preceding scope before
\ inference can allocate. All audits and inference share the caller's fuel.
: lf-cv-audit ( -- status )
  lf-ssession-current? 0= if lf-tinfer-invalid exit then
  lf-cv-count @ 0 ?do
    i lf-cv-pair dup @ swap cell+ @ i lf-tci-audit lf-cv-status
    lf-tci-fuel @ lf-cv-fuel !
    ?dup if unloop exit then
  loop lf-tinfer-ok ;

\ Earlier domains have already passed; inference remains an experimental,
\ conservative diagnostic. Do not classify a non-Sort as ill-typed.
: lf-cv-infer-domains ( -- status )
  lf-cv-count @ 0 ?do
    i lf-cv-pair dup @ swap cell+ @ lf-cv-domains i lf-cv-fuel @
    lf-tcontext-infer lf-cv-status
    ?dup if >r 2drop r> unloop exit then
    lf-tinfer-fuel @ lf-cv-fuel !
    drop lf-term-read 0= if lf-tinfer-invalid unloop exit then
    2drop lf-tag-symbolic-sort <> if lf-tinfer-unknown unloop exit then
    lf-cv-terms @ lf-term-count ! lf-cv-levels @ lf-level-count !
  loop lf-tinfer-ok ;

\ ( address count fuel -- status ) Oldest-first index/identity pairs; each
\ domain is scoped in its preceding context. Count is 0..lf-term-capacity,
\ fuel nonnegative; count zero permits any address but requires a live session.
\ Returns lf-tinfer-ok/invalid/exhausted/unknown. Counts in BOTH arenas are
\ restored on every outcome, including success; serials never rewind. Scratch
\ is global and non-reentrant. Audit failure can precede discovery of later
\ invalid inputs, but no inference/allocation starts unless every audit passes.
: lf-context-validation-probe ( address count fuel -- status )
  dup 0< if 2drop drop lf-tinfer-invalid exit then lf-cv-fuel !
  dup 0< over lf-term-capacity > or if 2drop lf-tinfer-invalid exit then
  lf-cv-count ! lf-cv-address !
  lf-term-count @ lf-cv-terms ! lf-level-count @ lf-cv-levels !
  lf-cv-count @ 0 ?do
    lf-cv-address @ i 2 * cells + dup @ i lf-cv-pair !
    cell+ @ i lf-cv-pair cell+ !
  loop
  lf-cv-fuel @ lf-tci-fuel !
  lf-cv-audit dup 0= if drop lf-cv-infer-domains then
  lf-cv-terms @ lf-term-count ! lf-cv-levels @ lf-level-count ! ;

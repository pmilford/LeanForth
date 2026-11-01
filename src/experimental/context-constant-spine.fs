\ Untrusted constant application in an explicit open binder context. Load
\ constant-spine-probe.fs and tagged-context-infer.fs and their dependencies.
\ A result assumes both the candidate signature and every context domain are
\ well-typed; neither is checked here. No theorem or declaration is accepted.
\ Arrays contain index/identity pairs: context oldest first, arguments in
\ application order. They must be aligned, readable and disjoint from all
\ mutable module/dependency storage. No raw mutation, resets, reentrancy or
\ concurrent use is permitted. Handles and tokens are forgeable diagnostics.
\ Constant-bearing arguments or candidate types are unsupported and may be
\ reported invalid even when valid in Lean. Capacities are temporary limits.

variable lf-csp-token
variable lf-csp-root
variable lf-csp-root-id
variable lf-csp-args
variable lf-csp-count
variable lf-csp-context
variable lf-csp-depth
variable lf-csp-terms
variable lf-csp-levels
variable lf-csp-type
variable lf-csp-type-id
variable lf-csp-domain
variable lf-csp-body
variable lf-csp-arg
variable lf-csp-arg-id

\ Read an already bounded pair from a caller-owned array.
: lf-csp-pair ( position array -- index identity )
  swap 2 * cells + dup @ swap cell+ @ ;

\ Audit identities, shapes, level scopes and binder scope of the context and
\ every argument before any operation can allocate. A domain may refer only
\ to earlier context entries. These checks do not establish domain typing.
: lf-csp-audit ( -- status )
  lf-csp-depth @ 0 ?do
    lf-caprobe-budget lf-tci-fuel !
    i lf-csp-context @ lf-csp-pair i lf-tci-audit lf-caprobe-infer-status
    ?dup if unloop exit then
  loop
  lf-csp-count @ 0 ?do
    lf-caprobe-budget lf-tci-fuel !
    i lf-csp-args @ lf-csp-pair lf-csp-depth @ lf-tci-audit
    lf-caprobe-infer-status ?dup if unloop exit then
  loop lf-caprobe-ok ;

\ Apply the current candidate Pi to one audited argument. Inference of that
\ argument is conditional on the caller's context-domain typing assumptions.
: lf-csp-step ( position -- status )
  lf-csp-args @ lf-csp-pair lf-csp-arg-id ! lf-csp-arg !
  lf-csp-type @ lf-csp-type-id @ lf-caprobe-budget lf-tagged-beta
  lf-caprobe-beta-status ?dup if >r 2drop r> exit then
  drop lf-term-read 0= if lf-caprobe-invalid exit then
  lf-csp-body ! lf-csp-domain !
  lf-tag-pi <> if lf-caprobe-unknown exit then
  lf-csp-arg @ lf-csp-arg-id @ lf-csp-context @ lf-csp-depth @
  lf-caprobe-budget lf-tcontext-infer
  lf-caprobe-infer-status ?dup if >r 2drop r> exit then
  lf-csp-domain @ dup lf-term-identity 0= if
    drop 2drop lf-caprobe-invalid exit
  then
  lf-caprobe-budget lf-tagged-convert lf-caprobe-convert-status ?dup if exit then
  lf-csp-body @ dup lf-term-identity 0= if drop lf-caprobe-invalid exit then
  lf-csp-arg @ lf-csp-arg-id @ lf-caprobe-budget lf-tagged-instantiate
  lf-caprobe-inst-status ?dup if >r 2drop r> exit then
  lf-csp-type-id ! lf-csp-type ! lf-caprobe-ok ;

\ Validate and specialize the closed candidate, then apply the arguments.
: lf-csp-work ( -- term identity 0 | status )
  lf-csp-audit ?dup if exit then
  lf-csp-token @ lf-csp-root @ lf-csp-root-id @
  lf-caprobe-budget lf-caprobe-budget lf-cttype-probe
  lf-caprobe-candidate-status ?dup if exit then
  2dup lf-caprobe-budget lf-hterm-check lf-caprobe-repr-status
  ?dup if >r 2drop r> exit then
  over lf-caprobe-budget lf-caprobe-closed ?dup if >r 2drop r> exit then
  lf-csp-type-id ! lf-csp-type !
  lf-csp-count @ 0 ?do i lf-csp-step ?dup if unloop exit then loop
  lf-csp-type @ lf-csp-type-id @ lf-caprobe-ok ;

\ ( token root root-id args count context depth -- result identity status )
\ Up to eight args and lf-term-capacity context entries are supported. Every
\ failure returns -1 0 status and restores both arena counts; serials and
\ scratch are never rewound. Each audit and operation gets a separate fixed
\ visit budget, as in the existing constant-application experiment.
: lf-context-constant-spine ( token root rid args count context depth -- result id status )
  dup 0< over lf-term-capacity > or if
    2drop 2drop 2drop drop -1 0 lf-caprobe-invalid exit
  then
  lf-csp-depth ! lf-csp-context !
  dup 0< over lf-spine-capacity > or if
    drop 2drop 2drop -1 0 lf-caprobe-invalid exit
  then
  lf-csp-count ! lf-csp-args ! lf-csp-root-id ! lf-csp-root ! lf-csp-token !
  lf-term-count @ lf-csp-terms ! lf-level-count @ lf-csp-levels !
  lf-csp-work dup if
    lf-csp-terms @ lf-term-count ! lf-csp-levels @ lf-level-count ! -1 0 rot
  then ;

\ Untrusted composition of context validation and constant application.
\ Load context-validation-probe.fs and context-constant-spine.fs first.
\ This checks domains with the limited inference diagnostic but does not
\ check the candidate declaration or its proof, and is not a Lean kernel.
\ Input arrays must obey both dependencies' readable, aligned, disjoint
\ storage contracts. No mutation, nested calls or concurrent use is allowed.
\ Handles and tokens are forgeable, session-local allocation diagnostics.

variable lf-vcsp-token
variable lf-vcsp-root
variable lf-vcsp-root-id
variable lf-vcsp-args
variable lf-vcsp-count
variable lf-vcsp-context
variable lf-vcsp-depth

\ Translate status namespaces explicitly; unknown values fail closed.
: lf-vcsp-status ( status -- status )
  case
    lf-tinfer-ok of lf-caprobe-ok endof
    lf-tinfer-invalid of lf-caprobe-invalid endof
    lf-tinfer-exhausted of lf-caprobe-exhausted endof
    lf-tinfer-unknown of lf-caprobe-unknown endof
    drop lf-caprobe-invalid 0
  endcase ;

\ Validate every external handle and scope before context checking allocates.
\ The reused audit reads but never allocates. Candidate metadata and argument
\ types remain unchecked; later stages revalidate the original handles.
: lf-vcsp-preflight ( -- status )
  lf-vcsp-depth @ dup 0< swap lf-term-capacity > or if lf-caprobe-invalid exit then
  lf-vcsp-count @ dup 0< swap lf-spine-capacity > or if lf-caprobe-invalid exit then
  lf-vcsp-token @ lf-rspec-current? 0= if lf-caprobe-invalid exit then
  lf-vcsp-root @ lf-vcsp-root-id @ lf-caprobe-budget lf-cterm-check
  lf-caprobe-repr-status ?dup if exit then
  lf-vcsp-context @ lf-csp-context ! lf-vcsp-depth @ lf-csp-depth !
  lf-vcsp-args @ lf-csp-args ! lf-vcsp-count @ lf-csp-count !
  lf-csp-audit ;

\ ( token root rid args count context depth -- result id status )
\ First check context domains oldest-first with the bounded experimental
\ inference. That check restores arena counts even on success; then the
\ existing application probe validates inputs again before allocating.
\ Each stage has its own fixed fuel. Failure returns -1 0 status; neither
\ stage rewinds consumed allocation identities or guarantees proof validity.
: lf-validated-context-spine ( token root rid args count context depth -- result id status )
  lf-vcsp-depth ! lf-vcsp-context ! lf-vcsp-count ! lf-vcsp-args !
  lf-vcsp-root-id ! lf-vcsp-root ! lf-vcsp-token !
  lf-vcsp-preflight ?dup if -1 0 rot exit then
  lf-vcsp-context @ lf-vcsp-depth @ lf-caprobe-budget lf-context-validation-probe
  lf-vcsp-status ?dup if -1 0 rot exit then
  lf-vcsp-token @ lf-vcsp-root @ lf-vcsp-root-id @
  lf-vcsp-args @ lf-vcsp-count @ lf-vcsp-context @ lf-vcsp-depth @
  lf-context-constant-spine ;

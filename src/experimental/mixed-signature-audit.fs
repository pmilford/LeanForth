\ Global nonallocating preflight for the untrusted mixed signature index.
\ Load mixed-signature-probe.fs and constant-term-scope.fs first. Signatures
\ are unchecked type assumptions: this checks neither types, declaration lookup,
\ dependency closure nor proofs. Constant names/handles are validated, not
\ resolved to index records; arities of referenced declarations are unknown.
\ Universe formal IDs are opaque positive IDs, not name-table handles. Used
\ parameters must belong both to the copied formals and the current session
\ scope; unused formals need not occur in the session scope.
\
\ Single-threaded, non-reentrant; no reset, insertion, raw writes or callback
\ during a call. The token fixes an index lifetime, not a content revision;
\ the caller must keep the index and session fixed for the whole call and any
\ subsequent use requires a fresh audit. Scratch of the called auditors changes.
\ No term, level or reference is allocated, even on failure; counts and serials
\ are unchanged. Handles are forgeable, instance-local diagnostics.

variable lf-msa-fuel
variable lf-msa-position

\ Validate bounded metadata before using it as a pointer or loop bound.
: lf-msa-metadata ( -- status )
  lf-msa-position @ cells lf-msp-names + @ dup 0<= swap lf-name-valid? 0= or
  if lf-msp-invalid exit then
  lf-msa-position @ 0 ?do
    i cells lf-msp-names + @ lf-msa-position @ cells lf-msp-names + @ = if
      lf-msp-invalid unloop exit
    then
  loop
  lf-msa-position @ cells lf-msp-arities + @ dup 0< over lf-level-capacity > or
  if drop lf-msp-invalid exit then
  lf-lsubst-count !
  lf-msa-position @ lf-msp-formals-at lf-lsubst-formals !
  lf-lsubst-count @ 0 ?do
    i lf-lsubst-formal@ 0<= if lf-msp-invalid unloop exit then
    i 0 ?do
      i lf-lsubst-formal@ j lf-lsubst-formal@ = if
        lf-msp-invalid unloop unloop exit
      then
    loop
  loop lf-msp-ok ;

: lf-msa-record ( -- status )
  lf-msa-metadata ?dup if exit then
  lf-msa-position @ cells lf-msp-roots + @ lf-mls-root !
  lf-msa-position @ cells lf-msp-ids + @ lf-mls-id !
  lf-mls-root @ lf-mls-id @ 0 lf-msa-fuel @ lf-constant-term-scope
  lf-cts-fuel @ lf-msa-fuel ! lf-mls-repr-status lf-msp-status ?dup if exit then
  lf-msa-fuel @ lf-mls-fuel ! lf-mls-audit
  lf-mls-fuel @ lf-msa-fuel ! lf-msp-status ;

\ ( token fuel -- status ) Validate every live record, including complete root
\ identity, reachable constant references, session level scope, copied formals,
\ structural syntax and term binder scope at outer depth zero. One shared
\ budget charges each term and level occurrence on each traversal, including
\ repeated DAG edges. Index/name/formal/context and reference identity scans
\ are bounded additional work; work-stack capacity can independently exhaust.
\ Negative fuel or malformed/stale data is invalid; zero fuel is exhausted,
\ including for an empty index. No lookup, specialization or inference is done.
: lf-mixed-signature-audit ( token fuel -- status )
  dup 0< if 2drop lf-msp-invalid exit then lf-msa-fuel !
  lf-msp-current? 0= if lf-msp-invalid exit then
  lf-lscope-context-valid? 0= if lf-msp-invalid exit then
  lf-msa-fuel @ 0= if lf-msp-exhausted exit then
  lf-msp-count @ 0 ?do
    i lf-msa-position ! lf-msa-record ?dup if unloop exit then
  loop lf-msp-ok ;
